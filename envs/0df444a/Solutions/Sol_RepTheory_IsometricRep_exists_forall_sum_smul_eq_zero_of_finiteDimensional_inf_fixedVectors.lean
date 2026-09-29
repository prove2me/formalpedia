-- Prove2me | solution 1 for RepTheory.IsometricRep.exists_forall_sum_smul_eq_zero_of_finiteDimensional_inf_fixedVectors
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.230386+00:00
-- url     : https://prove2.me/submissions/0677c647-93a4-5465-8c20-58d059945b16

import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.Spectrum
import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import Mathlib.Analysis.Normed.Operator.Compact.Basic
import Mathlib.Topology.Algebra.OpenSubgroup
import Mathlib.GroupTheory.GroupAction.Quotient
import Definitions.Def_RepTheory_SmoothAdmissibleSchurCommutant
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_RepTheory_IsometricRep_exists_forall_sum_smul_eq_zero_of_finiteDimensional_inf_fixedVectors

set_option autoImplicit false

open FLT.SmoothAdmissibleSchurCommutant
open scoped InnerProductSpace

universe v w

namespace AdmissibleGerm

variable {G : Type v} [Group G]
variable {H : Type w} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
variable (ρ : G →* Module.End ℂ H)

private def IsIsometricRep : Prop := ∀ (g : G) (x y : H), ⟪ρ g x, ρ g y⟫_ℂ = ⟪x, y⟫_ℂ

variable {ρ}

private theorem rep_apply_inv (g : G) (x : H) : ρ g (ρ g⁻¹ x) = x := by
  rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]

private theorem rep_inv_apply (g : G) (x : H) : ρ g⁻¹ (ρ g x) = x := by
  rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]

private theorem inner_rep_apply (hρ : IsIsometricRep ρ) (g : G) (x y : H) : ⟪ρ g x, y⟫_ℂ = ⟪x, ρ g⁻¹ y⟫_ℂ := by
  conv_lhs => rw [← rep_apply_inv (ρ := ρ) g y]
  exact hρ g x (ρ g⁻¹ y)

private theorem inner_rep_apply_right (hρ : IsIsometricRep ρ) (g : G) (x y : H) : ⟪x, ρ g y⟫_ℂ = ⟪ρ g⁻¹ x, y⟫_ℂ := by
  rw [inner_rep_apply hρ g⁻¹ x y, inv_inv]

private theorem norm_rep_apply (hρ : IsIsometricRep ρ) (g : G) (x : H) : ‖ρ g x‖ = ‖x‖ := by
  have h := hρ g x x
  rw [inner_self_eq_norm_sq_to_K, inner_self_eq_norm_sq_to_K] at h
  have h' : ‖ρ g x‖ ^ 2 = ‖x‖ ^ 2 := by exact_mod_cast h
  exact (pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).mp h'

private theorem continuous_rep_apply (hρ : IsIsometricRep ρ) (g : G) : Continuous (ρ g) :=
  AddMonoidHomClass.continuous_of_bound (ρ g) 1 fun x => le_of_eq (by rw [norm_rep_apply hρ, one_mul])

private theorem mem_fixedVectors_of_le {x : H} {K L : Subgroup G} (hLK : L ≤ K) (hx : x ∈ fixedVectors ρ K) :
    x ∈ fixedVectors ρ L :=
  (mem_fixedVectors ρ).mpr fun u hu => (mem_fixedVectors ρ).mp hx u (hLK hu)

private theorem map_average_of_commute {n : ℕ} (k : Fin n → G) (b : Module.End ℂ H) (hb : ∀ g : G, b * ρ g = ρ g * b)
    (x : H) : b ((n : ℂ)⁻¹ • ∑ i, ρ (k i) x) = (n : ℂ)⁻¹ • ∑ i, ρ (k i) (b x) := by
  rw [map_smul, map_sum]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Module.End.mul_apply, hb, Module.End.mul_apply]

private theorem isClosed_fixedVectors (hρ : IsIsometricRep ρ) (K : Subgroup G) :
    IsClosed ((fixedVectors ρ K : Submodule ℂ H) : Set H) := by
  have hset : ((fixedVectors ρ K : Submodule ℂ H) : Set H) = ⋂ u ∈ K, {x : H | ρ u x = x} := by
    ext x
    simp only [SetLike.mem_coe, mem_fixedVectors, Set.mem_iInter, Set.mem_setOf_eq]
  rw [hset]
  exact isClosed_biInter fun u _ => isClosed_eq (continuous_rep_apply hρ u) continuous_id

section Adjoint

variable [CompleteSpace H]

private theorem adjoint_apply_rep_comm (hρ : IsIsometricRep ρ) (T : H →L[ℂ] H)
    (hT : ∀ (g : G) (x : H), T (ρ g x) = ρ g (T x)) (g : G) (x : H) :
    (ContinuousLinearMap.adjoint T) (ρ g x) = ρ g ((ContinuousLinearMap.adjoint T) x) := by
  refine ext_inner_right ℂ fun y => ?_
  rw [ContinuousLinearMap.adjoint_inner_left, inner_rep_apply hρ, ← hT, ← ContinuousLinearMap.adjoint_inner_left,
    ← inner_rep_apply hρ]

end Adjoint

section Topological

variable [TopologicalSpace G] [SeparatelyContinuousMul G]

private theorem isCompact_isOpen_inf {K₁ K₂ : Subgroup G} (h₁ : IsCompact (K₁ : Set G)) (h₁' : IsOpen (K₁ : Set G))
    (_h₂ : IsCompact (K₂ : Set G)) (h₂' : IsOpen (K₂ : Set G)) :
    IsCompact ((K₁ ⊓ K₂ : Subgroup G) : Set G) ∧ IsOpen ((K₁ ⊓ K₂ : Subgroup G) : Set G) := by
  rw [Subgroup.coe_inf]
  exact ⟨h₁.inter_right (K₂.isClosed_of_isOpen h₂'), h₁'.inter h₂'⟩

private theorem isCompact_isOpen_map_conj {K : Subgroup G} (hK : IsCompact (K : Set G)) (hK' : IsOpen (K : Set G))
    (g : G) :
    IsCompact ((K.map (MulAut.conj g).toMonoidHom : Subgroup G) : Set G) ∧
      IsOpen ((K.map (MulAut.conj g).toMonoidHom : Subgroup G) : Set G) := by
  have hfun : (⇑(MulAut.conj g).toMonoidHom : G → G) = fun x : G => g * x * g⁻¹ := by
    funext x
    simp [MulAut.conj_apply]
  rw [Subgroup.coe_map, hfun]
  constructor
  · exact hK.image (by fun_prop)
  · have hsplit : ((fun x : G => g * x * g⁻¹) '' (K : Set G)) =
        (fun y : G => y * g⁻¹) '' ((fun x : G => g * x) '' (K : Set G)) := by
      rw [Set.image_image]
    rw [hsplit]
    exact isOpenMap_mul_right g⁻¹ _ (isOpenMap_mul_left g _ hK')

private theorem exists_isCompact_isOpen_mem_fixedVectors_apply {x : H} {K : Subgroup G} (hK : IsCompact (K : Set G))
    (hK' : IsOpen (K : Set G)) (hx : x ∈ fixedVectors ρ K) (g : G) :
    ∃ L : Subgroup G, IsCompact (L : Set G) ∧ IsOpen (L : Set G) ∧ ρ g x ∈ fixedVectors ρ L := by
  have hx' := (mem_fixedVectors ρ).mp hx
  refine ⟨K.map (MulAut.conj g).toMonoidHom, (isCompact_isOpen_map_conj hK hK' g).1,
    (isCompact_isOpen_map_conj hK hK' g).2, (mem_fixedVectors ρ).mpr ?_⟩
  intro u hu
  obtain ⟨a, ha, rfl⟩ := Subgroup.mem_map.mp hu
  change ρ (g * a * g⁻¹) (ρ g x) = ρ g x
  rw [← Module.End.mul_apply, ← map_mul, mul_assoc (g * a) g⁻¹ g, inv_mul_cancel, mul_one, map_mul,
    Module.End.mul_apply, hx' a ha]

private theorem exists_average_family (hρ : IsIsometricRep ρ) {K K' : Subgroup G} (hK : IsCompact (K : Set G))
    (hK' : IsOpen (K' : Set G)) (_hle : K' ≤ K) :
    ∃ (n : ℕ) (k : Fin n → G), 0 < n ∧ (∀ i, k i ∈ K) ∧
      ∀ x ∈ fixedVectors ρ K',
        ((n : ℂ)⁻¹ • ∑ i, ρ (k i) x) ∈ fixedVectors ρ K ∧
        (x ∈ fixedVectors ρ K → (n : ℂ)⁻¹ • ∑ i, ρ (k i) x = x) ∧
        (∀ u ∈ fixedVectors ρ K, ⟪(n : ℂ)⁻¹ • ∑ i, ρ (k i) x, u⟫_ℂ = ⟪x, u⟫_ℂ) ∧
        (∀ W : Submodule ℂ H, (∀ (g : G), ∀ w ∈ W, ρ g w ∈ W) → x ∈ W → ((n : ℂ)⁻¹ • ∑ i, ρ (k i) x) ∈ W) := by
  classical
  haveI : CompactSpace K := isCompact_iff_compactSpace.mp hK
  set Q : Subgroup K := K'.subgroupOf K with hQdef
  have hQ : IsOpen (Q : Set K) := by
    rw [hQdef, Subgroup.coe_subgroupOf]
    exact continuous_subtype_val.isOpen_preimage _ hK'
  haveI : SeparatelyContinuousMul K := inferInstanceAs (SeparatelyContinuousMul K.toSubmonoid)
  haveI : Finite (K ⧸ Q) := Subgroup.quotient_finite_of_isOpen Q hQ
  haveI : Fintype (K ⧸ Q) := Fintype.ofFinite _
  let e : (K ⧸ Q) ≃ Fin (Fintype.card (K ⧸ Q)) := Fintype.equivFin (K ⧸ Q)

  let rep : K ⧸ Q → G := fun q => ((Quotient.out q : K) : G)
  have hrep : ∀ q, rep q ∈ K := fun q => (Quotient.out q : K).2
  have hnpos : 0 < Fintype.card (K ⧸ Q) := Fintype.card_pos
  have hnC : ((Fintype.card (K ⧸ Q) : ℕ) : ℂ) ≠ 0 := by exact_mod_cast hnpos.ne'

  have hsum : ∀ x : H, (∑ i : Fin (Fintype.card (K ⧸ Q)), ρ (rep (e.symm i)) x) = ∑ q : K ⧸ Q, ρ (rep q) x :=
    fun x => Equiv.sum_comp e.symm (fun q => ρ (rep q) x)

  have hshift : ∀ (κ : K) (q : K ⧸ Q) (x : H), x ∈ fixedVectors ρ K' →
      ρ (κ : G) (ρ (rep q) x) = ρ (rep (κ • q)) x := by
    intro κ q x hx
    have hx' := (mem_fixedVectors ρ).mp hx
    have hq : κ • q = QuotientGroup.mk (κ * Quotient.out q) := by
      conv_lhs => rw [← QuotientGroup.out_eq' q]
      exact MulAction.Quotient.smul_mk Q κ (Quotient.out q)
    obtain ⟨h, hh⟩ := QuotientGroup.mk_out_eq_mul Q (κ * Quotient.out q)
    have hhK' : ((h : K) : G) ∈ K' := Subgroup.mem_subgroupOf.mp h.2
    simp only [rep, hq, hh, Subgroup.coe_mul, map_mul, Module.End.mul_apply, hx' _ hhK']
  refine ⟨Fintype.card (K ⧸ Q), fun i => rep (e.symm i), hnpos, fun i => hrep _, ?_⟩
  intro x hx
  have hx' := (mem_fixedVectors ρ).mp hx
  simp only [hsum]
  refine ⟨?_, ?_, ?_, ?_⟩
  ·
    refine (mem_fixedVectors ρ).mpr ?_
    intro κ₀ hκ₀
    rw [map_smul, map_sum]
    congr 1
    calc (∑ q : K ⧸ Q, ρ κ₀ (ρ (rep q) x)) = ∑ q : K ⧸ Q, ρ (rep ((⟨κ₀, hκ₀⟩ : K) • q)) x := by
          refine Finset.sum_congr rfl fun q _ => ?_
          exact hshift ⟨κ₀, hκ₀⟩ q x hx
      _ = ∑ q : K ⧸ Q, ρ (rep q) x :=
          Equiv.sum_comp (MulAction.toPerm (⟨κ₀, hκ₀⟩ : K)) (fun q => ρ (rep q) x)
  ·
    intro hxK
    have hxK' := (mem_fixedVectors ρ).mp hxK
    rw [Finset.sum_congr rfl fun q _ => hxK' _ (hrep q), Finset.sum_const, Finset.card_univ,
      ← Nat.cast_smul_eq_nsmul ℂ, smul_smul, inv_mul_cancel₀ hnC, one_smul]
  ·
    intro u hu
    have hu' := (mem_fixedVectors ρ).mp hu
    have hterm : ∀ q : K ⧸ Q, ⟪ρ (rep q) x, u⟫_ℂ = ⟪x, u⟫_ℂ := by
      intro q
      rw [inner_rep_apply hρ, hu' _ (K.inv_mem (hrep q))]
    rw [inner_smul_left, sum_inner, Finset.sum_congr rfl fun q _ => hterm q, Finset.sum_const, Finset.card_univ,
      nsmul_eq_mul, map_inv₀, map_natCast, ← mul_assoc, inv_mul_cancel₀ hnC, one_mul]
  ·
    intro W hW hxW
    exact W.smul_mem _ (W.sum_mem fun q _ => hW _ _ hxW)

private theorem exists_stable_le_of_finiteDimensional (hρ : IsIsometricRep ρ) (X : Submodule ℂ H)
    (hX₁ : ∀ (g : G), ∀ x ∈ X, ρ g x ∈ X)
    (hX₂ : ∀ K : Subgroup G, IsCompact (K : Set G) → IsOpen (K : Set G) →
      FiniteDimensional ℂ ↥(X ⊓ fixedVectors ρ K))
    (hX₃ : ∃ K : Subgroup G, IsCompact (K : Set G) ∧ IsOpen (K : Set G) ∧ X ⊓ fixedVectors ρ K ≠ ⊥) :
    ∃ E : Submodule ℂ H, E ≤ X ∧ (∀ (g : G), ∀ x ∈ E, ρ g x ∈ E) ∧
      (∀ x ∈ E, ∃ K : Subgroup G, IsCompact (K : Set G) ∧ IsOpen (K : Set G) ∧ x ∈ fixedVectors ρ K) ∧
      (∃ K : Subgroup G, IsCompact (K : Set G) ∧ IsOpen (K : Set G) ∧ E ⊓ fixedVectors ρ K ≠ ⊥) ∧
      ∀ W : Submodule ℂ H, W ≤ E → (∀ (g : G), ∀ w ∈ W, ρ g w ∈ W) → W = ⊥ ∨ W = E := by
  classical
  obtain ⟨K₀, hK₀c, hK₀o, hX₀⟩ := hX₃
  haveI hfin : FiniteDimensional ℂ ↥(X ⊓ fixedVectors ρ K₀) := hX₂ K₀ hK₀c hK₀o

  have hP : ∃ m : ℕ, ∃ U : Submodule ℂ H, U ≤ X ∧ (∀ (g : G), ∀ x ∈ U, ρ g x ∈ U) ∧
      U ⊓ fixedVectors ρ K₀ ≠ ⊥ ∧ Module.finrank ℂ ↥(U ⊓ fixedVectors ρ K₀) = m :=
    ⟨_, X, le_rfl, hX₁, hX₀, rfl⟩
  obtain ⟨U, hUX, hUst, hU₀, hUrank⟩ := Nat.find_spec hP
  have hmin : ∀ V : Submodule ℂ H, V ≤ X → (∀ (g : G), ∀ x ∈ V, ρ g x ∈ V) → V ⊓ fixedVectors ρ K₀ ≠ ⊥ →
      Module.finrank ℂ ↥(U ⊓ fixedVectors ρ K₀) ≤ Module.finrank ℂ ↥(V ⊓ fixedVectors ρ K₀) := by
    intro V hVX hVst hV₀
    rw [hUrank]
    exact Nat.find_min' hP ⟨V, hVX, hVst, hV₀, rfl⟩
  haveI : FiniteDimensional ℂ ↥(U ⊓ fixedVectors ρ K₀) :=
    Submodule.finiteDimensional_of_le (inf_le_inf_right _ hUX)

  obtain ⟨E, hE⟩ : ∃ E : Submodule ℂ H, E = ⨆ g : G, (U ⊓ fixedVectors ρ K₀).map (ρ g) := ⟨_, rfl⟩
  have hgen_le : ∀ g : G, (U ⊓ fixedVectors ρ K₀).map (ρ g) ≤ E := by
    intro g
    rw [hE]
    exact le_iSup (fun g : G => (U ⊓ fixedVectors ρ K₀).map (ρ g)) g
  have hUF_le_E : U ⊓ fixedVectors ρ K₀ ≤ E := by
    intro x hx
    apply hgen_le 1
    refine Submodule.mem_map.mpr ⟨x, hx, ?_⟩
    rw [map_one, Module.End.one_apply]
  have hEU : E ≤ U := by
    rw [hE]
    refine iSup_le fun g => ?_
    intro y hy
    obtain ⟨x, hx, rfl⟩ := Submodule.mem_map.mp hy
    exact hUst g x (Submodule.mem_inf.mp hx).1
  have hEX : E ≤ X := hEU.trans hUX
  have hEst : ∀ (g : G), ∀ x ∈ E, ρ g x ∈ E := by
    intro g x hx
    rw [hE] at hx
    refine Submodule.iSup_induction (fun h : G => (U ⊓ fixedVectors ρ K₀).map (ρ h))
      (motive := fun y => ρ g y ∈ E) hx ?_ ?_ ?_
    · intro h y hy
      obtain ⟨u, hu, rfl⟩ := Submodule.mem_map.mp hy
      apply hgen_le (g * h)
      refine Submodule.mem_map.mpr ⟨u, hu, ?_⟩
      rw [map_mul, Module.End.mul_apply]
    · show ρ g 0 ∈ E
      rw [map_zero]
      exact E.zero_mem
    · intro y z hy hz
      rw [map_add]
      exact E.add_mem hy hz
  have hEF : E ⊓ fixedVectors ρ K₀ = U ⊓ fixedVectors ρ K₀ :=
    le_antisymm (inf_le_inf_right _ hEU) (le_inf hUF_le_E inf_le_right)
  have hsmooth : ∀ x ∈ E, ∃ K : Subgroup G, IsCompact (K : Set G) ∧ IsOpen (K : Set G) ∧ x ∈ fixedVectors ρ K := by
    intro x hx
    rw [hE] at hx
    refine Submodule.iSup_induction (fun h : G => (U ⊓ fixedVectors ρ K₀).map (ρ h))
      (motive := fun y => ∃ K : Subgroup G, IsCompact (K : Set G) ∧ IsOpen (K : Set G) ∧ y ∈ fixedVectors ρ K)
      hx ?_ ?_ ?_
    · intro h y hy
      obtain ⟨u, hu, rfl⟩ := Submodule.mem_map.mp hy
      exact exists_isCompact_isOpen_mem_fixedVectors_apply hK₀c hK₀o (Submodule.mem_inf.mp hu).2 h
    · exact ⟨K₀, hK₀c, hK₀o, (fixedVectors ρ K₀).zero_mem⟩
    · rintro y z ⟨K₁, h₁c, h₁o, hy⟩ ⟨K₂, h₂c, h₂o, hz⟩
      refine ⟨K₁ ⊓ K₂, (isCompact_isOpen_inf h₁c h₁o h₂c h₂o).1, (isCompact_isOpen_inf h₁c h₁o h₂c h₂o).2, ?_⟩
      exact (fixedVectors ρ (K₁ ⊓ K₂)).add_mem (mem_fixedVectors_of_le inf_le_left hy)
        (mem_fixedVectors_of_le inf_le_right hz)
  refine ⟨E, hEX, hEst, hsmooth, ⟨K₀, hK₀c, hK₀o, by rw [hEF]; exact hU₀⟩, ?_⟩
  intro W hWE hWst
  by_cases hW₀ : W ⊓ fixedVectors ρ K₀ = ⊥
  ·
    left
    rw [Submodule.eq_bot_iff]
    intro w hw
    have hperp : ∀ y ∈ E, ⟪w, y⟫_ℂ = 0 := by
      intro y hy
      rw [hE] at hy
      refine Submodule.iSup_induction (fun h : G => (U ⊓ fixedVectors ρ K₀).map (ρ h))
        (motive := fun y => ⟪w, y⟫_ℂ = 0) hy ?_ ?_ ?_
      · intro h y hy
        obtain ⟨u, hu, rfl⟩ := Submodule.mem_map.mp hy
        have huF : u ∈ fixedVectors ρ K₀ := (Submodule.mem_inf.mp hu).2
        have hw'W : ρ h⁻¹ w ∈ W := hWst h⁻¹ w hw
        obtain ⟨L, hLc, hLo, hw'L⟩ := hsmooth _ (hWE hw'W)
        obtain ⟨n, k, -, -, havg⟩ := exists_average_family hρ (K := K₀) (K' := K₀ ⊓ L) hK₀c
          (isCompact_isOpen_inf hK₀c hK₀o hLc hLo).2 inf_le_left
        obtain ⟨hy₁, -, hy₃, hy₄⟩ := havg (ρ h⁻¹ w) (mem_fixedVectors_of_le inf_le_right hw'L)
        have hyW : ((n : ℂ)⁻¹ • ∑ i, ρ (k i) (ρ h⁻¹ w)) ∈ W ⊓ fixedVectors ρ K₀ :=
          Submodule.mem_inf.mpr ⟨hy₄ W hWst hw'W, hy₁⟩
        rw [hW₀, Submodule.mem_bot] at hyW
        rw [inner_rep_apply_right hρ, ← hy₃ u huF, hyW, inner_zero_left]
      · exact inner_zero_right w
      · intro y z hy hz
        rw [inner_add_right, hy, hz, add_zero]
    exact inner_self_eq_zero.mp (hperp w (hWE hw))
  ·
    right
    have hle : W ⊓ fixedVectors ρ K₀ ≤ U ⊓ fixedVectors ρ K₀ := (inf_le_inf_right _ hWE).trans hEF.le
    have heq : W ⊓ fixedVectors ρ K₀ = U ⊓ fixedVectors ρ K₀ :=
      Submodule.eq_of_le_of_finrank_le hle (hmin W (hWE.trans hEX) hWst hW₀)
    refine le_antisymm hWE ?_
    rw [hE]
    refine iSup_le fun g => ?_
    intro y hy
    obtain ⟨x, hx, rfl⟩ := Submodule.mem_map.mp hy
    rw [← heq] at hx
    exact hWst g x (Submodule.mem_inf.mp hx).1

end Topological

variable (ρ)

private noncomputable def act (μ : G →₀ ℂ) : Module.End ℂ H := μ.sum fun (h : G) (c : ℂ) => c • ρ h

private theorem act_apply (μ : G →₀ ℂ) (x : H) : act ρ μ x = μ.sum fun (h : G) (c : ℂ) => c • ρ h x := by
  simp only [act, LinearMap.finsupp_sum_apply, LinearMap.smul_apply]

private noncomputable def ann {d : ℕ} (e : Fin d → H) : Submodule ℂ H :=
  ⨅ μ ∈ {μ : G →₀ ℂ | ∀ j, act ρ μ (e j) = 0}, LinearMap.ker (act ρ μ)

variable {ρ}

private theorem mem_ann_iff {d : ℕ} {e : Fin d → H} {x : H} :
    x ∈ ann ρ e ↔ ∀ μ : G →₀ ℂ, (∀ j, act ρ μ (e j) = 0) → act ρ μ x = 0 := by
  simp only [ann, Submodule.mem_iInf, LinearMap.mem_ker, Set.mem_setOf_eq]

private theorem range_subset_ann {d : ℕ} (e : Fin d → H) : Set.range e ⊆ (ann ρ e : Set H) := by
  rintro _ ⟨j, rfl⟩
  exact mem_ann_iff.2 fun μ hμ => hμ j

private theorem span_le_ann {d : ℕ} (e : Fin d → H) : Submodule.span ℂ (Set.range e) ≤ ann ρ e :=
  Submodule.span_le.2 (range_subset_ann e)

private theorem act_comp_of_commute (b : Module.End ℂ H) (hb : ∀ g : G, b * ρ g = ρ g * b) (μ : G →₀ ℂ) (x : H) :
    act ρ μ (b x) = b (act ρ μ x) := by
  simp only [act_apply, map_finsuppSum, map_smul]
  refine Finsupp.sum_congr fun h _ => ?_
  have := congrArg (fun T : Module.End ℂ H => T x) (hb h)
  simp only [Module.End.mul_apply] at this
  rw [this]

private theorem apply_mem_ann_of_commute {d : ℕ} {e : Fin d → H} (b : Module.End ℂ H) (hb : ∀ g : G, b * ρ g = ρ g * b)
    {x : H} (hx : x ∈ ann ρ e) : b x ∈ ann ρ e := by
  rw [mem_ann_iff] at hx ⊢
  intro μ hμ
  rw [act_comp_of_commute b hb, hx μ hμ, map_zero]

private theorem continuous_apply_of_isIsometricRep (hρ : IsIsometricRep ρ) (g : G) : Continuous (ρ g) :=
  (LinearMap.isometryOfInner (ρ g) (hρ g)).continuous

private theorem continuous_act (hρ : IsIsometricRep ρ) (μ : G →₀ ℂ) : Continuous (act ρ μ) := by
  have : (act ρ μ : H → H) = fun x => μ.sum fun (h : G) (c : ℂ) => c • ρ h x := funext fun x => act_apply ρ μ x
  rw [this]
  unfold Finsupp.sum
  exact continuous_finsetSum _ fun h _ => (continuous_apply_of_isIsometricRep hρ h).const_smul _

private theorem isClosed_ann (hρ : IsIsometricRep ρ) {d : ℕ} (e : Fin d → H) :
    IsClosed ((ann ρ e : Submodule ℂ H) : Set H) := by
  have hset : ((ann ρ e : Submodule ℂ H) : Set H) =
      ⋂ μ ∈ {μ : G →₀ ℂ | ∀ j, act ρ μ (e j) = 0}, (act ρ μ) ⁻¹' {0} := by
    ext x
    simp only [SetLike.mem_coe, mem_ann_iff, Set.mem_iInter, Set.mem_preimage, Set.mem_singleton_iff,
      Set.mem_setOf_eq]
  rw [hset]
  exact isClosed_biInter fun μ _ => isClosed_singleton.preimage (continuous_act hρ μ)

private theorem eq_of_mem_fixedVectors_of_forall_inner_eq {K : Subgroup G} {y₁ y₂ : H} (h₁ : y₁ ∈ fixedVectors ρ K)
    (h₂ : y₂ ∈ fixedVectors ρ K) (h : ∀ u ∈ fixedVectors ρ K, ⟪y₁, u⟫_ℂ = ⟪y₂, u⟫_ℂ) : y₁ = y₂ := by
  have hu : y₁ - y₂ ∈ fixedVectors ρ K := (fixedVectors ρ K).sub_mem h₁ h₂
  have h0 : ⟪y₁ - y₂, y₁ - y₂⟫_ℂ = 0 := by
    rw [inner_sub_left, h _ hu, sub_self]
  exact sub_eq_zero.1 (inner_self_eq_zero.1 h0)

private theorem inner_starProjection_left (K : Subgroup G) [(fixedVectors ρ K).HasOrthogonalProjection] (x : H)
    {u : H} (hu : u ∈ fixedVectors ρ K) : ⟪(fixedVectors ρ K).starProjection x, u⟫_ℂ = ⟪x, u⟫_ℂ := by
  have h0 : ⟪x - (fixedVectors ρ K).starProjection x, u⟫_ℂ = 0 :=
    (Submodule.mem_orthogonal' _ _).1 ((fixedVectors ρ K).sub_starProjection_mem_orthogonal x) u hu
  rw [inner_sub_left, sub_eq_zero] at h0
  exact h0.symm

private inductive Reach (E : Submodule ℂ H) (B : Set (Module.End ℂ H)) : H → Prop
  | base {x : H} : x ∈ E → Reach E B x
  | step {x : H} (b : Module.End ℂ H) : b ∈ B → Reach E B x → Reach E B (b x)

private theorem reach_apply {E : Submodule ℂ H} {B : Set (Module.End ℂ H)} (hB : ∀ b ∈ B, ∀ g : G, b * ρ g = ρ g * b)
    (hEρ : ∀ (g : G), ∀ x ∈ E, ρ g x ∈ E) (g : G) {y : H} (hy : Reach E B y) : Reach E B (ρ g y) := by
  induction hy with
  | base hx => exact Reach.base (hEρ g _ hx)
  | @step x b hb _ ih =>
    have hcomm := congrArg (fun T : Module.End ℂ H => T x) (hB b hb g)
    simp only [Module.End.mul_apply] at hcomm
    rw [← hcomm]
    exact Reach.step b hb ih

private theorem span_stable_of_forall {s : Set H} (L : Module.End ℂ H) (hL : ∀ y ∈ s, L y ∈ Submodule.span ℂ s) :
    ∀ x ∈ Submodule.span ℂ s, L x ∈ Submodule.span ℂ s := fun _ hx =>
  (Submodule.span_le.2 (fun y hy => Submodule.mem_comap.2 (hL y hy)) :
    Submodule.span ℂ s ≤ (Submodule.span ℂ s).comap L) hx

private theorem dense_of_forall_isClosed (hρ : IsIsometricRep ρ) {S : Set (H →L[ℂ] H)}
    (hirr : ∀ W : Submodule ℂ H, IsClosed (W : Set H) → (∀ (g : G), ∀ x ∈ W, ρ g x ∈ W) →
      (∀ s ∈ S, ∀ x ∈ W, s x ∈ W) → W = ⊥ ∨ W = ⊤)
    (W : Submodule ℂ H) (hW0 : W ≠ ⊥) (hWρ : ∀ (g : G), ∀ x ∈ W, ρ g x ∈ W) (hWS : ∀ s ∈ S, ∀ x ∈ W, s x ∈ W) :
    Dense (W : Set H) := by
  rw [Submodule.dense_iff_topologicalClosure_eq_top]
  have hC : ∀ x ∈ W.topologicalClosure, ∀ (L : H → H), Continuous L → (∀ w ∈ W, L w ∈ W) →
      L x ∈ W.topologicalClosure := by
    intro x hx L hL hLW
    have hx' : x ∈ closure (W : Set H) := by
      rw [← SetLike.mem_coe, Submodule.topologicalClosure_coe] at hx
      exact hx
    rw [← SetLike.mem_coe, Submodule.topologicalClosure_coe]
    exact map_mem_closure hL hx' fun w hw => hLW w hw
  rcases hirr W.topologicalClosure W.isClosed_topologicalClosure
      (fun g x hx => hC x hx (ρ g) (continuous_apply_of_isIsometricRep hρ g) (hWρ g))
      (fun s hs x hx => hC x hx s s.continuous (hWS s hs)) with h | h
  · exact absurd (le_bot_iff.1 (h ▸ W.le_topologicalClosure)) hW0
  · exact h

private theorem dense_span_reach {B : Set (Module.End ℂ H)} (hB : ∀ b ∈ B, ∀ g : G, b * ρ g = ρ g * b)
    (hirr : ∀ W : Submodule ℂ H, W ≠ ⊥ → (∀ (g : G), ∀ x ∈ W, ρ g x ∈ W) → (∀ b ∈ B, ∀ x ∈ W, b x ∈ W) →
      Dense (W : Set H))
    {E : Submodule ℂ H} (hE0 : E ≠ ⊥) (hEρ : ∀ (g : G), ∀ x ∈ E, ρ g x ∈ E) :
    Dense ((Submodule.span ℂ {y : H | Reach E B y} : Submodule ℂ H) : Set H) := by
  refine hirr _ ?_ ?_ ?_
  · intro h0
    apply hE0
    rw [eq_bot_iff]
    intro x hx
    have : x ∈ Submodule.span ℂ {y : H | Reach E B y} := Submodule.subset_span (Reach.base hx)
    rw [h0] at this
    exact this
  · intro g
    exact span_stable_of_forall (ρ g) fun y hy => Submodule.subset_span (reach_apply hB hEρ g hy)
  · intro b hb
    exact span_stable_of_forall b fun y hy => Submodule.subset_span (Reach.step b hb hy)

variable (ρ)

private noncomputable def restrictRep (E : Submodule ℂ H) (hEρ : ∀ (g : G), ∀ x ∈ E, ρ g x ∈ E) :
    G →* Module.End ℂ ↥E where
  toFun g := (ρ g).restrict (hEρ g)
  map_one' := by
    ext y
    simp [LinearMap.restrict_apply]
  map_mul' g₁ g₂ := by
    ext y
    simp [LinearMap.restrict_apply]

variable {ρ}

private theorem coe_restrictRep_apply {E : Submodule ℂ H} (hEρ : ∀ (g : G), ∀ x ∈ E, ρ g x ∈ E) (g : G) (y : ↥E) :
    ((restrictRep ρ E hEρ g y : ↥E) : H) = ρ g (y : H) := rfl

private theorem repStabilizer_restrictRep {E : Submodule ℂ H} (hEρ : ∀ (g : G), ∀ x ∈ E, ρ g x ∈ E) (y : ↥E) :
    repStabilizer (restrictRep ρ E hEρ) y = repStabilizer ρ (y : H) := by
  ext g
  simp only [mem_repStabilizer, Subtype.ext_iff, coe_restrictRep_apply]

private theorem map_subtype_fixedVectors_restrictRep {E : Submodule ℂ H} (hEρ : ∀ (g : G), ∀ x ∈ E, ρ g x ∈ E)
    (K : Subgroup G) : (fixedVectors (restrictRep ρ E hEρ) K).map E.subtype = E ⊓ fixedVectors ρ K := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    refine Submodule.mem_inf.2 ⟨y.2, fun u hu => ?_⟩
    have := congrArg Subtype.val (hy u hu)
    simpa [coe_restrictRep_apply] using this
  · intro hx
    obtain ⟨hxE, hxK⟩ := Submodule.mem_inf.1 hx
    exact ⟨⟨x, hxE⟩, fun u hu => Subtype.ext (by simpa [coe_restrictRep_apply] using hxK u hu), rfl⟩

private theorem isIrreducibleRep_restrictRep {E : Submodule ℂ H} (hEρ : ∀ (g : G), ∀ x ∈ E, ρ g x ∈ E) (hE0 : E ≠ ⊥)
    (hmin : ∀ W : Submodule ℂ H, W ≤ E → (∀ (g : G), ∀ w ∈ W, ρ g w ∈ W) → W = ⊥ ∨ W = E) :
    IsIrreducibleRep (restrictRep ρ E hEρ) := by
  refine ⟨?_, ?_⟩
  · obtain ⟨x, hxE, hx0⟩ := (Submodule.ne_bot_iff E).1 hE0
    exact ⟨⟨x, hxE⟩, fun h => hx0 (congrArg Subtype.val h)⟩
  · intro W' hW'
    have hle : W'.map E.subtype ≤ E := by
      rintro _ ⟨w, -, rfl⟩
      exact w.2
    have hstable : ∀ (g : G), ∀ w ∈ W'.map E.subtype, ρ g w ∈ W'.map E.subtype := by
      rintro g _ ⟨w, hw, rfl⟩
      exact ⟨restrictRep ρ E hEρ g w, hW' g w hw, rfl⟩
    rcases hmin _ hle hstable with h | h
    · left
      exact Submodule.map_injective_of_injective E.injective_subtype (by rw [h, Submodule.map_bot])
    · right
      exact Submodule.map_injective_of_injective E.injective_subtype (by rw [h, Submodule.map_subtype_top])

section LevelGrammar

variable [TopologicalSpace G]

private theorem reach_exists_fixed {E : Submodule ℂ H} {B : Set (Module.End ℂ H)}
    (hB : ∀ b ∈ B, ∀ g : G, b * ρ g = ρ g * b)
    (hEsm : ∀ x ∈ E, ∃ K : Subgroup G, IsCompact (K : Set G) ∧ IsOpen (K : Set G) ∧ x ∈ fixedVectors ρ K)
    {y : H} (hy : Reach E B y) :
    ∃ K : Subgroup G, IsCompact (K : Set G) ∧ IsOpen (K : Set G) ∧ y ∈ fixedVectors ρ K := by
  induction hy with
  | base hx => exact hEsm _ hx
  | step b hb _ ih =>
    obtain ⟨K, hKc, hKo, hxK⟩ := ih
    exact ⟨K, hKc, hKo, apply_mem_fixedVectors_of_commute ρ (fun g => (hB b hb g).symm) hxK⟩

private theorem isAdmissibleRep_restrictRep {E : Submodule ℂ H} (hEρ : ∀ (g : G), ∀ x ∈ E, ρ g x ∈ E)
    (hEfd : ∀ K : Subgroup G, IsCompact (K : Set G) → IsOpen (K : Set G) →
      FiniteDimensional ℂ ↥(E ⊓ fixedVectors ρ K)) :
    IsAdmissibleRep (restrictRep ρ E hEρ) := by
  intro K hKc hKo
  have hmap : FiniteDimensional ℂ ↥((fixedVectors (restrictRep ρ E hEρ) K).map E.subtype) := by
    rw [map_subtype_fixedVectors_restrictRep]
    exact hEfd K hKc hKo
  exact (Submodule.equivMapOfInjective E.subtype E.injective_subtype
    (fixedVectors (restrictRep ρ E hEρ) K)).symm.finiteDimensional

private theorem ne_bot_of_exists_inf_ne_bot {E : Submodule ℂ H}
    (hE0 : ∃ K : Subgroup G, IsCompact (K : Set G) ∧ IsOpen (K : Set G) ∧ E ⊓ fixedVectors ρ K ≠ ⊥) : E ≠ ⊥ := by
  obtain ⟨K, -, -, hK⟩ := hE0
  rintro rfl
  exact hK (bot_inf_eq _)

section TopologicalGroup

variable [SeparatelyContinuousMul G]

private theorem isOpen_repStabilizer_of_exists_fixed {x : H}
    (hx : ∃ K : Subgroup G, IsCompact (K : Set G) ∧ IsOpen (K : Set G) ∧ x ∈ fixedVectors ρ K) :
    IsOpen ((repStabilizer ρ x : Subgroup G) : Set G) := by
  obtain ⟨K, -, hKo, hxK⟩ := hx
  exact Subgroup.isOpen_mono (fun u hu => (mem_repStabilizer ρ).2 (hxK u hu)) hKo

private theorem isSmoothRep_restrictRep {E : Submodule ℂ H} (hEρ : ∀ (g : G), ∀ x ∈ E, ρ g x ∈ E)
    (hEsm : ∀ x ∈ E, ∃ K : Subgroup G, IsCompact (K : Set G) ∧ IsOpen (K : Set G) ∧ x ∈ fixedVectors ρ K) :
    IsSmoothRep (restrictRep ρ E hEρ) := by
  intro y
  rw [repStabilizer_restrictRep]
  exact isOpen_repStabilizer_of_exists_fixed (hEsm y y.2)

private theorem starProjection_eq_average (hρ : IsIsometricRep ρ) {K K' : Subgroup G} (hK : IsCompact (K : Set G))
    (hK' : IsOpen (K' : Set G)) (hle : K' ≤ K) [(fixedVectors ρ K).HasOrthogonalProjection] :
    ∃ (n : ℕ) (k : Fin n → G), ∀ x ∈ fixedVectors ρ K',
      (fixedVectors ρ K).starProjection x = (n : ℂ)⁻¹ • ∑ i, ρ (k i) x := by
  obtain ⟨n, k, -, -, hfam⟩ := exists_average_family hρ hK hK' hle
  refine ⟨n, k, fun x hx => ?_⟩
  obtain ⟨hmem, -, hinner, -⟩ := hfam x hx
  refine eq_of_mem_fixedVectors_of_forall_inner_eq ((fixedVectors ρ K).starProjection_apply_mem x) hmem
    fun u hu => ?_
  rw [inner_starProjection_left K x hu, hinner u hu]

private theorem starProjection_apply_of_commute (hρ : IsIsometricRep ρ) {K : Subgroup G} (hK : IsCompact (K : Set G))
    (hKo : IsOpen (K : Set G)) [(fixedVectors ρ K).HasOrthogonalProjection] (b : Module.End ℂ H)
    (hb : ∀ g : G, b * ρ g = ρ g * b) {x : H}
    (hx : ∃ K₀ : Subgroup G, IsCompact (K₀ : Set G) ∧ IsOpen (K₀ : Set G) ∧ x ∈ fixedVectors ρ K₀) :
    (fixedVectors ρ K).starProjection (b x) = b ((fixedVectors ρ K).starProjection x) := by
  obtain ⟨K₀, -, hK₀o, hxK₀⟩ := hx
  have hK'o : IsOpen ((K ⊓ K₀ : Subgroup G) : Set G) := by
    rw [Subgroup.coe_inf]
    exact hKo.inter hK₀o
  have hxK' : x ∈ fixedVectors ρ (K ⊓ K₀) := fun u hu => hxK₀ u (Subgroup.mem_inf.1 hu).2
  have hbxK' : b x ∈ fixedVectors ρ (K ⊓ K₀) :=
    apply_mem_fixedVectors_of_commute ρ (fun g => (hb g).symm) hxK'
  obtain ⟨n, k, havg⟩ := starProjection_eq_average hρ hK hK'o inf_le_left
  rw [havg _ hbxK', havg _ hxK', map_average_of_commute k b hb]

private theorem starProjection_mem_inf_of_mem (hρ : IsIsometricRep ρ) {E : Submodule ℂ H}
    (hEρ : ∀ (g : G), ∀ x ∈ E, ρ g x ∈ E)
    (hEsm : ∀ x ∈ E, ∃ K : Subgroup G, IsCompact (K : Set G) ∧ IsOpen (K : Set G) ∧ x ∈ fixedVectors ρ K)
    {K : Subgroup G} (hK : IsCompact (K : Set G)) (hKo : IsOpen (K : Set G))
    [(fixedVectors ρ K).HasOrthogonalProjection] {x : H} (hx : x ∈ E) :
    (fixedVectors ρ K).starProjection x ∈ E ⊓ fixedVectors ρ K := by
  obtain ⟨K₀, -, hK₀o, hxK₀⟩ := hEsm x hx
  have hK'o : IsOpen ((K ⊓ K₀ : Subgroup G) : Set G) := by
    rw [Subgroup.coe_inf]
    exact hKo.inter hK₀o
  have hxK' : x ∈ fixedVectors ρ (K ⊓ K₀) := fun u hu => hxK₀ u (Subgroup.mem_inf.1 hu).2
  obtain ⟨n, k, -, -, hfam⟩ := exists_average_family hρ hK hK'o inf_le_left
  obtain ⟨hmem, -, hinner, hstable⟩ := hfam x hxK'
  have hP : (fixedVectors ρ K).starProjection x = (n : ℂ)⁻¹ • ∑ i, ρ (k i) x :=
    eq_of_mem_fixedVectors_of_forall_inner_eq ((fixedVectors ρ K).starProjection_apply_mem x) hmem
      fun u hu => by rw [inner_starProjection_left K x hu, hinner u hu]
  rw [hP]
  exact Submodule.mem_inf.2 ⟨hstable E hEρ hx, hmem⟩

private theorem starProjection_mem_ann_of_reach (hρ : IsIsometricRep ρ) {B : Set (Module.End ℂ H)}
    (hB : ∀ b ∈ B, ∀ g : G, b * ρ g = ρ g * b) {E : Submodule ℂ H} (hEρ : ∀ (g : G), ∀ x ∈ E, ρ g x ∈ E)
    (hEsm : ∀ x ∈ E, ∃ K : Subgroup G, IsCompact (K : Set G) ∧ IsOpen (K : Set G) ∧ x ∈ fixedVectors ρ K)
    {K : Subgroup G} (hK : IsCompact (K : Set G)) (hKo : IsOpen (K : Set G))
    [(fixedVectors ρ K).HasOrthogonalProjection] {d : ℕ} {e : Fin d → H}
    (he : E ⊓ fixedVectors ρ K ≤ Submodule.span ℂ (Set.range e)) {y : H} (hy : Reach E B y) :
    (fixedVectors ρ K).starProjection y ∈ ann ρ e := by
  induction hy with
  | base hx => exact span_le_ann e (he (starProjection_mem_inf_of_mem hρ hEρ hEsm hK hKo hx))
  | step b hb hy' ih =>
    rw [starProjection_apply_of_commute hρ hK hKo b (hB b hb) (reach_exists_fixed hB hEsm hy')]
    exact apply_mem_ann_of_commute b (hB b hb) ih

private theorem exists_family_forall_fixed_sum_eq_zero [CompleteSpace H] (hρ : IsIsometricRep ρ)
    {B : Set (Module.End ℂ H)} (hB : ∀ b ∈ B, ∀ g : G, b * ρ g = ρ g * b)
    (hirr : ∀ W : Submodule ℂ H, W ≠ ⊥ → (∀ (g : G), ∀ x ∈ W, ρ g x ∈ W) → (∀ b ∈ B, ∀ x ∈ W, b x ∈ W) →
      Dense (W : Set H))
    {E : Submodule ℂ H} (hE0 : E ≠ ⊥) (hEρ : ∀ (g : G), ∀ x ∈ E, ρ g x ∈ E)
    (hEsm : ∀ x ∈ E, ∃ K : Subgroup G, IsCompact (K : Set G) ∧ IsOpen (K : Set G) ∧ x ∈ fixedVectors ρ K)
    (hEfd : ∀ K : Subgroup G, IsCompact (K : Set G) → IsOpen (K : Set G) →
      FiniteDimensional ℂ ↥(E ⊓ fixedVectors ρ K))
    {K : Subgroup G} (hKc : IsCompact (K : Set G)) (hKo : IsOpen (K : Set G)) :
    ∃ (d : ℕ) (e : Fin d → H), (∀ j, e j ∈ E) ∧
      ∀ x ∈ fixedVectors ρ K, ∀ μ : G →₀ ℂ,
        (∀ j : Fin d, (μ.sum fun (h : G) (c : ℂ) => c • ρ h (e j)) = 0) →
          (μ.sum fun (h : G) (c : ℂ) => c • ρ h x) = 0 := by
  haveI : CompleteSpace (fixedVectors ρ K) := (isClosed_fixedVectors hρ K).completeSpace_coe
  haveI := hEfd K hKc hKo
  set V : Submodule ℂ H := E ⊓ fixedVectors ρ K with hV
  let bV := Module.finBasis ℂ ↥V
  refine ⟨Module.finrank ℂ ↥V, fun j => ((bV j : ↥V) : H), fun j => (Submodule.mem_inf.1 (bV j).2).1, ?_⟩

  have he : V ≤ Submodule.span ℂ (Set.range fun j => ((bV j : ↥V) : H)) := by
    intro v hv
    have hmem : (⟨v, hv⟩ : ↥V) ∈ Submodule.span ℂ (Set.range bV) := by rw [bV.span_eq]; trivial
    have := Submodule.mem_map_of_mem (f := V.subtype) hmem
    rw [Submodule.map_span, ← Set.range_comp] at this
    exact this

  have hann : ∀ x ∈ fixedVectors ρ K, x ∈ ann ρ fun j => ((bV j : ↥V) : H) := by
    intro x hx
    have hP : (fixedVectors ρ K).starProjection x = x := (Submodule.starProjection_eq_self_iff).2 hx
    have hdense := dense_span_reach (B := B) hB hirr hE0 hEρ
    have hmaps : ∀ z ∈ Submodule.span ℂ {y : H | Reach E B y},
        (fixedVectors ρ K).starProjection z ∈ ann ρ fun j => ((bV j : ↥V) : H) := by
      intro z hz
      refine (Submodule.span_le.2 (fun y hy => Submodule.mem_comap.2 ?_) :
        Submodule.span ℂ {y : H | Reach E B y} ≤
          (ann ρ fun j => ((bV j : ↥V) : H)).comap ((fixedVectors ρ K).starProjection : H →ₗ[ℂ] H)) hz
      exact starProjection_mem_ann_of_reach hρ hB hEρ hEsm hKc hKo he hy
    have hcl : (fixedVectors ρ K).starProjection x ∈
        closure ((ann ρ fun j => ((bV j : ↥V) : H) : Submodule ℂ H) : Set H) :=
      map_mem_closure (fixedVectors ρ K).starProjection.continuous (hdense x) fun z hz => hmaps z hz
    rw [(isClosed_ann hρ _).closure_eq, hP] at hcl
    exact hcl
  intro x hx μ hμ
  have hx' := (mem_ann_iff).1 (hann x hx) μ (fun j => by rw [act_apply]; exact hμ j)
  rwa [act_apply] at hx'

private theorem exists_package [CompleteSpace H] (hρ : IsIsometricRep ρ) {B : Set (Module.End ℂ H)}
    (hB : ∀ b ∈ B, ∀ g : G, b * ρ g = ρ g * b)
    (hirr : ∀ W : Submodule ℂ H, W ≠ ⊥ → (∀ (g : G), ∀ x ∈ W, ρ g x ∈ W) → (∀ b ∈ B, ∀ x ∈ W, b x ∈ W) →
      Dense (W : Set H))
    (E : Submodule ℂ H) (hEρ : ∀ (g : G), ∀ x ∈ E, ρ g x ∈ E)
    (hEsm : ∀ x ∈ E, ∃ K : Subgroup G, IsCompact (K : Set G) ∧ IsOpen (K : Set G) ∧ x ∈ fixedVectors ρ K)
    (hE0 : ∃ K : Subgroup G, IsCompact (K : Set G) ∧ IsOpen (K : Set G) ∧ E ⊓ fixedVectors ρ K ≠ ⊥)
    (hmin : ∀ W : Submodule ℂ H, W ≤ E → (∀ (g : G), ∀ w ∈ W, ρ g w ∈ W) → W = ⊥ ∨ W = E)
    (hEfd : ∀ K : Subgroup G, IsCompact (K : Set G) → IsOpen (K : Set G) →
      FiniteDimensional ℂ ↥(E ⊓ fixedVectors ρ K)) :
    ∃ (E' : Type w) (_ : AddCommGroup E') (_ : Module ℂ E') (πE : G →* Module.End ℂ E'),
      IsIrreducibleRep πE ∧ IsSmoothRep πE ∧ IsAdmissibleRep πE ∧
        ∀ K : Subgroup G, IsCompact (K : Set G) → IsOpen (K : Set G) →
          ∃ (d : ℕ) (e : Fin d → E'), ∀ x ∈ fixedVectors ρ K, ∀ μ : G →₀ ℂ,
            (∀ j : Fin d, (μ.sum fun (h : G) (c : ℂ) => c • πE h (e j)) = 0) →
              (μ.sum fun (h : G) (c : ℂ) => c • ρ h x) = 0 := by
  have hE0' : E ≠ ⊥ := ne_bot_of_exists_inf_ne_bot hE0
  refine ⟨↥E, inferInstance, inferInstance, restrictRep ρ E hEρ, isIrreducibleRep_restrictRep hEρ hE0' hmin,
    isSmoothRep_restrictRep hEρ hEsm, isAdmissibleRep_restrictRep hEρ hEfd, fun K hKc hKo => ?_⟩
  obtain ⟨d, e, heE, hsent⟩ := exists_family_forall_fixed_sum_eq_zero hρ hB hirr hE0' hEρ hEsm hEfd hKc hKo
  refine ⟨d, fun j => ⟨e j, heE j⟩, fun x hx μ hμ => hsent x hx μ fun j => ?_⟩
  have := congrArg (E.subtype) (hμ j)
  simpa [map_finsuppSum, coe_restrictRep_apply] using this

private theorem exists_package_of_forall_isClosed [CompleteSpace H] (hρ : IsIsometricRep ρ) {S : Set (H →L[ℂ] H)}
    (hS : ∀ s ∈ S, ∀ (g : G) (x : H), s (ρ g x) = ρ g (s x))
    (hirr : ∀ W : Submodule ℂ H, IsClosed (W : Set H) → (∀ (g : G), ∀ x ∈ W, ρ g x ∈ W) →
      (∀ s ∈ S, ∀ x ∈ W, s x ∈ W) → W = ⊥ ∨ W = ⊤)
    (E : Submodule ℂ H) (hEρ : ∀ (g : G), ∀ x ∈ E, ρ g x ∈ E)
    (hEsm : ∀ x ∈ E, ∃ K : Subgroup G, IsCompact (K : Set G) ∧ IsOpen (K : Set G) ∧ x ∈ fixedVectors ρ K)
    (hE0 : ∃ K : Subgroup G, IsCompact (K : Set G) ∧ IsOpen (K : Set G) ∧ E ⊓ fixedVectors ρ K ≠ ⊥)
    (hmin : ∀ W : Submodule ℂ H, W ≤ E → (∀ (g : G), ∀ w ∈ W, ρ g w ∈ W) → W = ⊥ ∨ W = E)
    (hEfd : ∀ K : Subgroup G, IsCompact (K : Set G) → IsOpen (K : Set G) →
      FiniteDimensional ℂ ↥(E ⊓ fixedVectors ρ K)) :
    ∃ (E' : Type w) (_ : AddCommGroup E') (_ : Module ℂ E') (πE : G →* Module.End ℂ E'),
      IsIrreducibleRep πE ∧ IsSmoothRep πE ∧ IsAdmissibleRep πE ∧
        ∀ K : Subgroup G, IsCompact (K : Set G) → IsOpen (K : Set G) →
          ∃ (d : ℕ) (e : Fin d → E'), ∀ x ∈ fixedVectors ρ K, ∀ μ : G →₀ ℂ,
            (∀ j : Fin d, (μ.sum fun (h : G) (c : ℂ) => c • πE h (e j)) = 0) →
              (μ.sum fun (h : G) (c : ℂ) => c • ρ h x) = 0 := by
  refine exists_package hρ (B := (fun s : H →L[ℂ] H => (s : H →ₗ[ℂ] H)) '' S) ?_ ?_ E hEρ hEsm hE0 hmin hEfd
  · rintro _ ⟨s, hs, rfl⟩ g
    ext x
    simp only [Module.End.mul_apply, ContinuousLinearMap.coe_coe]
    exact hS s hs g x
  · intro W hW0 hWρ hWB
    exact dense_of_forall_isClosed hρ hirr W hW0 hWρ fun s hs x hx => hWB _ ⟨s, hs, rfl⟩ x hx

end TopologicalGroup

end LevelGrammar

end AdmissibleGerm

open AdmissibleGerm in
theorem solution
    {G : Type v} [Group G] [TopologicalSpace G] [SeparatelyContinuousMul G]
    {H : Type w} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (ρ : G →* Module.End ℂ H) (hρ : ∀ (g : G) (x y : H), ⟪ρ g x, ρ g y⟫_ℂ = ⟪x, y⟫_ℂ)
    (S : Set (H →L[ℂ] H)) (hS : ∀ s ∈ S, ∀ (g : G) (x : H), s (ρ g x) = ρ g (s x))
    (hirr : ∀ W : Submodule ℂ H, IsClosed (W : Set H) →
      (∀ (g : G) (x : H), x ∈ W → ρ g x ∈ W) → (∀ s ∈ S, ∀ x : H, x ∈ W → s x ∈ W) → W = ⊥ ∨ W = ⊤)
    (hX : ∃ X : Submodule ℂ H, (∀ (g : G) (x : H), x ∈ X → ρ g x ∈ X) ∧
      (∀ K : Subgroup G, IsCompact (K : Set G) → IsOpen (K : Set G) →
        FiniteDimensional ℂ ↥(X ⊓ fixedVectors ρ K)) ∧
      ∃ K₀ : Subgroup G, IsCompact (K₀ : Set G) ∧ IsOpen (K₀ : Set G) ∧ X ⊓ fixedVectors ρ K₀ ≠ ⊥) :
    ∃ (E : Type w) (_ : AddCommGroup E) (_ : Module ℂ E) (πE : G →* Module.End ℂ E),
      IsIrreducibleRep πE ∧ IsSmoothRep πE ∧ IsAdmissibleRep πE ∧
        ∀ K : Subgroup G, IsCompact (K : Set G) → IsOpen (K : Set G) →
          ∃ (d : ℕ) (e : Fin d → E), ∀ x : H, (∀ k ∈ K, ρ k x = x) → ∀ μ : G →₀ ℂ,
            (∀ j : Fin d, (μ.sum fun (h : G) (c : ℂ) => c • πE h (e j)) = 0) →
              (μ.sum fun (h : G) (c : ℂ) => c • ρ h x) = 0 := by
  obtain ⟨X, hX₁, hX₂, hX₃⟩ := hX
  obtain ⟨E, hEX, hEρ, hEsm, hE0, hmin⟩ := exists_stable_le_of_finiteDimensional hρ X hX₁ hX₂ hX₃
  obtain ⟨E', i₁, i₂, πE, h₁, h₂, h₃, h₄⟩ := exists_package_of_forall_isClosed hρ hS hirr E hEρ hEsm hE0 hmin
    fun K hKc hKo => by
      haveI := hX₂ K hKc hKo
      exact Submodule.finiteDimensional_of_le (inf_le_inf_right _ hEX)
  refine ⟨E', i₁, i₂, πE, h₁, h₂, h₃, fun K hKc hKo => ?_⟩
  obtain ⟨d, e, he⟩ := h₄ K hKc hKo
  exact ⟨d, e, fun x hx => he x ((mem_fixedVectors ρ).2 hx)⟩

end S_RepTheory_IsometricRep_exists_forall_sum_smul_eq_zero_of_finiteDimensional_inf_fixedVectors
end P2MW
export P2MW.S_RepTheory_IsometricRep_exists_forall_sum_smul_eq_zero_of_finiteDimensional_inf_fixedVectors (solution)
