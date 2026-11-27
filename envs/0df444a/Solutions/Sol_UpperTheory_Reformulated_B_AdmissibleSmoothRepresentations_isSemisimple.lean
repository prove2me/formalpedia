-- Prove2me | solution 1 for UpperTheory.Reformulated.B.AdmissibleSmoothRepresentations.isSemisimple
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-27T05:33:37.332828+00:00
-- url     : https://prove2.me/submissions/4e05366e-33ab-48c7-b184-2b52af2dff06

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_AdmissibleSmoothRepresentations
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
private theorem UpperTheory.Reformulated.B.AdmissibleSmoothRepresentations.mem_fixed {H V : Type} [Group H] [AddCommGroup V]
    [_root_.Module ℂ V] {ρ : Representation ℂ H V} {K : Subgroup H} {v : V} :
    v ∈ UpperTheory.Reformulated.B.AdmissibleSmoothRepresentations.fixed ρ K ↔ ∀ k ∈ K, ρ k v = v := by
  constructor
  · intro h k hk
    have h' := (show ∀ h : ↥K, ρ (h : H) v = (↑((1 : ↥K →* ℂˣ) h) : ℂ) • v from h) ⟨k, hk⟩
    simpa using h'
  · intro h
    show ∀ h : ↥K, ρ (h : H) v = (↑((1 : ↥K →* ℂˣ) h) : ℂ) • v
    intro k
    simpa using h k k.2
private theorem UpperTheory.Reformulated.B.AdmissibleSmoothRepresentations.inner_eq_zero_of_fixed {H V : Type} [Group H]
    [TopologicalSpace H] [IsTopologicalGroup H] [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    {ρ : Representation ℂ H V} (hsm : UpperTheory.Reformulated.B.AdmissibleSmoothRepresentations.IsSmooth ρ)
    (hun : ∀ (g : H) (x y : V), inner ℂ (ρ g x) (ρ g y) = inner ℂ x y)
    {K : Subgroup H} (hK : IsCompact (K : Set H)) (W : Subrepresentation ρ) {u : V}
    (hu : ∀ k ∈ K, ρ k u = u)
    (hperp : ∀ s ∈ W.toSubmodule, (∀ k ∈ K, ρ k s = s) → inner ℂ s u = 0)
    {w : V} (hw : w ∈ W.toSubmodule) : inner ℂ w u = 0 := by
  have hopen : ∀ x : H, IsOpen {g : H | ρ g w = ρ x w} := by
    intro x
    have h1 : IsOpen ((fun g : H => x⁻¹ * g) ⁻¹' {g : H | ρ g w = w}) :=
      (hsm w).preimage (continuous_const.mul continuous_id)
    convert h1 using 1
    ext g
    simp only [Set.mem_setOf_eq, Set.mem_preimage, map_mul, Module.End.mul_apply]
    constructor
    · intro h
      rw [h, ← Module.End.mul_apply, ← map_mul]
      simp
    · intro h
      have h2 := congrArg (ρ x) h
      rw [← Module.End.mul_apply (ρ x), ← map_mul] at h2
      simpa using h2
  obtain ⟨t, -, ht⟩ := hK.elim_nhds_subcover (fun x : H => {g : H | ρ g w = ρ x w})
    (fun x _ => (hopen x).mem_nhds rfl)
  classical
  have hfin : {y : V | ∃ k ∈ K, ρ k w = y}.Finite := by
    refine (t.image (fun x => ρ x w)).finite_toSet.subset ?_
    rintro y ⟨k, hk, rfl⟩
    obtain ⟨x, hx, hkx⟩ := Set.mem_iUnion₂.mp (ht hk)
    exact Finset.mem_coe.mpr (Finset.mem_image.mpr ⟨x, hx, hkx.symm⟩)
  have hO : ∀ y, y ∈ hfin.toFinset ↔ ∃ k ∈ K, ρ k w = y := by
    intro y
    simp
  have hsW : (∑ y ∈ hfin.toFinset, y) ∈ W.toSubmodule := by
    refine Submodule.sum_mem _ ?_
    intro y hy
    obtain ⟨k, -, rfl⟩ := (hO y).mp hy
    exact W.apply_mem_toSubmodule k hw
  have hsfix : ∀ k ∈ K, ρ k (∑ y ∈ hfin.toFinset, y) = ∑ y ∈ hfin.toFinset, y := by
    intro k hk
    rw [map_sum]
    refine Finset.sum_nbij' (fun y => ρ k y) (fun y => ρ k⁻¹ y) ?_ ?_ ?_ ?_ ?_
    · intro y hy
      obtain ⟨l, hl, rfl⟩ := (hO y).mp hy
      refine (hO _).mpr ⟨k * l, K.mul_mem hk hl, ?_⟩
      rw [map_mul, Module.End.mul_apply]
    · intro y hy
      obtain ⟨l, hl, rfl⟩ := (hO y).mp hy
      refine (hO _).mpr ⟨k⁻¹ * l, K.mul_mem (K.inv_mem hk) hl, ?_⟩
      rw [map_mul, Module.End.mul_apply]
    · intro y _
      show ρ k⁻¹ (ρ k y) = y
      rw [← Module.End.mul_apply, ← map_mul]
      simp
    · intro y _
      show ρ k (ρ k⁻¹ y) = y
      rw [← Module.End.mul_apply, ← map_mul]
      simp
    · intro y _
      rfl
  have hsum := hperp _ hsW hsfix
  rw [sum_inner] at hsum
  have hconst : ∀ y ∈ hfin.toFinset, inner ℂ y u = inner ℂ w u := by
    intro y hy
    obtain ⟨k, hk, rfl⟩ := (hO y).mp hy
    rw [← hun k w u, hu k hk]
  rw [Finset.sum_congr rfl hconst, Finset.sum_const, nsmul_eq_mul] at hsum
  have hcard : (hfin.toFinset.card : ℂ) ≠ 0 := by
    refine Nat.cast_ne_zero.mpr (Finset.card_ne_zero.mpr ⟨w, (hO w).mpr ⟨1, K.one_mem, ?_⟩⟩)
    simp
  exact (mul_eq_zero.mp hsum).resolve_left hcard
end

set_option autoImplicit false

namespace UpperTheory.Reformulated.B.AdmissibleSmoothRepresentations
theorem _root_.solution :
    ∀ {H : Type} [inst : Group H] [inst_1 : TopologicalSpace H] [IsTopologicalGroup H] {V : Type}
      [inst_3 : NormedAddCommGroup V] [inst_4 : InnerProductSpace ℂ V] {ρ : Representation ℂ H V},
      UpperTheory.Reformulated.B.AdmissibleSmoothRepresentations.IsAdmissible ρ →
        (∀ (g : H) (x y : V),
            Inner.inner ℂ (((ρ : H → V →ₗ[ℂ] V) g : V → V) x) (((ρ : H → V →ₗ[ℂ] V) g : V → V) y) = Inner.inner ℂ x y) →
          ∀ {K₀ : Subgroup H}, IsOpen (↑K₀ : Set H) → IsCompact (↑K₀ : Set H) → ρ.IsSemisimpleRepresentation := by
  intro H _ _ _ V _ _ ρ hadm hun K₀ hK₀o hK₀c
  refine ⟨fun W => ?_⟩
  have hinv : ∀ (g : H) ⦃v : V⦄, v ∈ W.toSubmoduleᗮ → ρ g v ∈ W.toSubmoduleᗮ := by
    intro g v hv
    rw [Submodule.mem_orthogonal] at hv ⊢
    intro w hw
    have h1 : ρ g (ρ g⁻¹ w) = w := by
      rw [← Module.End.mul_apply, ← map_mul]
      simp
    rw [← h1, hun]
    exact hv _ (W.apply_mem_toSubmodule g⁻¹ hw)
  refine ⟨⟨W.toSubmoduleᗮ, hinv⟩, ?_, ?_⟩
  · rw [disjoint_iff]
    apply Subrepresentation.toSubmodule_injective
    exact W.toSubmodule.inf_orthogonal_eq_bot
  · rw [codisjoint_iff]
    apply Subrepresentation.toSubmodule_injective
    show W.toSubmodule ⊔ W.toSubmoduleᗮ = ⊤
    rw [eq_top_iff]
    intro v _
    let S : Subgroup H :=
      { carrier := {g : H | ρ g v = v}
        mul_mem' := by
          intro a b ha hb
          show ρ (a * b) v = v
          rw [map_mul, Module.End.mul_apply, show ρ b v = v from hb, show ρ a v = v from ha]
        one_mem' := by
          show ρ 1 v = v
          simp
        inv_mem' := by
          intro a ha
          show ρ a⁻¹ v = v
          have h2 : ρ a⁻¹ (ρ a v) = v := by
            rw [← Module.End.mul_apply, ← map_mul]
            simp
          rwa [show ρ a v = v from ha] at h2 }
    let K : Subgroup H := K₀ ⊓ S
    have hKo : IsOpen (K : Set H) := hK₀o.inter (hadm.1 v)
    have hKc : IsCompact (K : Set H) :=
      hK₀c.of_isClosed_subset (Subgroup.isClosed_of_isOpen K hKo) (fun _ h => h.1)
    haveI : FiniteDimensional ℂ ↥(UpperTheory.Reformulated.B.AdmissibleSmoothRepresentations.fixed ρ K) := hadm.2 K hKo hKc
    let A : Submodule ℂ V := W.toSubmodule ⊓ UpperTheory.Reformulated.B.AdmissibleSmoothRepresentations.fixed ρ K
    haveI : FiniteDimensional ℂ ↥A := Submodule.finiteDimensional_inf_right _ _
    haveI : CompleteSpace ↥A := FiniteDimensional.complete ℂ ↥A
    obtain ⟨a, ha, u, hu, hv⟩ := A.exists_add_mem_mem_orthogonal v
    have hafix : ∀ k ∈ K, ρ k a = a := UpperTheory.Reformulated.B.AdmissibleSmoothRepresentations.mem_fixed.mp ha.2
    have hufix : ∀ k ∈ K, ρ k u = u := by
      intro k hk
      have hvk : ρ k v = v := hk.2
      rw [hv, map_add, hafix k hk] at hvk
      exact add_left_cancel hvk
    have huW : u ∈ W.toSubmoduleᗮ := by
      rw [Submodule.mem_orthogonal]
      intro w hw
      exact UpperTheory.Reformulated.B.AdmissibleSmoothRepresentations.inner_eq_zero_of_fixed hadm.1 hun hKc W hufix
        (fun s hs hsf => (Submodule.mem_orthogonal _ _).mp hu s
          ⟨hs, UpperTheory.Reformulated.B.AdmissibleSmoothRepresentations.mem_fixed.mpr hsf⟩) hw
    rw [hv]
    exact Submodule.add_mem_sup ha.1 huW
end UpperTheory.Reformulated.B.AdmissibleSmoothRepresentations
