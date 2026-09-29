-- Prove2me | solution 1 for RingHom.existsUnique_eq_smul_kaehlerDifferential_D_of_formallySmooth_of_maximalIdeal_eq_map_sup_span
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.230386+00:00
-- url     : https://prove2.me/submissions/7b65c408-76f6-5191-9dd4-e97bb5d01184

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_RingHom_existsUnique_eq_smul_kaehlerDifferential_D_of_formallySmooth_of_maximalIdeal_eq_map_sup_span

set_option autoImplicit false

open IsLocalRing

theorem solution
    {A : Type} [CommRing A] [IsLocalRing A]
    {S : Type} [CommRing S] [IsLocalRing S]
    (i : A →+* S) (hi : i.FormallySmooth) (hif : i.EssFiniteType)
    (hres : Function.Surjective ((IsLocalRing.residue S).comp i))
    (t : S) (hm : maximalIdeal S = (maximalIdeal A).map i ⊔ Ideal.span {t})
    (ht : t ∉ (maximalIdeal A).map i) :
    letI : Algebra A S := i.toAlgebra
    ∀ ω : KaehlerDifferential A S, ∃! s : S, ω = s • KaehlerDifferential.D A S t := by
  letI instAS : Algebra A S := i.toAlgebra
  show ∀ ω : KaehlerDifferential A S, ∃! s : S, ω = s • KaehlerDifferential.D A S t
  classical
  haveI : Algebra.FormallySmooth A S := hi
  haveI : Algebra.EssFiniteType A S := hif
  have halg : ∀ a : A, algebraMap A S a = i a := fun _ => rfl
  set dt := KaehlerDifferential.D A S t with hdt
  set I₀ : Ideal S := (maximalIdeal A).map i with hI₀
  have hI₀m : I₀ ≤ maximalIdeal S := by rw [hm]; exact le_sup_left
  have htm : t ∈ maximalIdeal S := by rw [hm]; exact Ideal.mem_sup_right (Ideal.mem_span_singleton_self t)

  have hDI₀ : ∀ m ∈ I₀, KaehlerDifferential.D A S m ∈ (maximalIdeal S) • (⊤ : Submodule S (KaehlerDifferential A S)) := by
    intro m hm0
    rw [hI₀, Ideal.map] at hm0
    refine Submodule.span_induction ?_ ?_ ?_ ?_ hm0
    · rintro x ⟨a, ha, rfl⟩
      rw [← halg, Derivation.map_algebraMap]; exact Submodule.zero_mem _
    · rw [map_zero]; exact Submodule.zero_mem _
    · intro x y _ _ hx hy; rw [map_add]; exact Submodule.add_mem _ hx hy
    · intro c x hx hDx
      rw [smul_eq_mul, Derivation.leibniz]
      refine Submodule.add_mem _ (Submodule.smul_mem _ _ hDx) ?_
      exact Submodule.smul_mem_smul (hI₀m (by rw [hI₀, Ideal.map]; exact hx)) Submodule.mem_top

  have hgen : ∀ s : S, KaehlerDifferential.D A S s ∈
      Submodule.span S {dt} ⊔ (maximalIdeal S) • (⊤ : Submodule S (KaehlerDifferential A S)) := by
    intro s
    obtain ⟨a, ha⟩ := hres (IsLocalRing.residue S s)
    have hm' : s - i a ∈ maximalIdeal S := by
      rw [← IsLocalRing.residue_eq_zero_iff, map_sub, sub_eq_zero]; exact ha.symm
    rw [hm] at hm'
    obtain ⟨m, hm0, y, hy, hmy⟩ := Submodule.mem_sup.mp hm'
    obtain ⟨v, rfl⟩ := Ideal.mem_span_singleton'.mp hy
    have hs : s = i a + m + v * t := by linear_combination -hmy
    have hD : KaehlerDifferential.D A S s = KaehlerDifferential.D A S m + (v • dt + t • KaehlerDifferential.D A S v) := by
      rw [hs, map_add, map_add, ← halg, Derivation.map_algebraMap, zero_add, Derivation.leibniz, hdt]
    rw [hD]
    refine Submodule.add_mem _ (Submodule.mem_sup_right (hDI₀ m hm0)) (Submodule.add_mem _ ?_ ?_)
    · exact Submodule.mem_sup_left (Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _))
    · exact Submodule.mem_sup_right (Submodule.smul_mem_smul htm Submodule.mem_top)
  have hspan : Submodule.span S {dt} = ⊤ := by
    apply le_antisymm le_top
    have hfg : (⊤ : Submodule S (KaehlerDifferential A S)).FG := Module.Finite.fg_top
    have hjac : maximalIdeal S ≤ (⊥ : Ideal S).jacobson := by
      rw [IsLocalRing.jacobson_eq_maximalIdeal ⊥ bot_ne_top]
    apply Submodule.le_of_le_smul_of_le_jacobson_bot hfg hjac
    intro ω _
    have hω : ω ∈ Submodule.span S (Set.range (KaehlerDifferential.D A S)) := by
      rw [KaehlerDifferential.span_range_derivation]; trivial
    exact (Submodule.span_le.mpr (by rintro _ ⟨s, rfl⟩; exact hgen s)) hω
  have hsurj : ∀ ω : KaehlerDifferential A S, ∃ s : S, ω = s • dt := by
    intro ω
    have : ω ∈ Submodule.span S {dt} := by rw [hspan]; trivial
    obtain ⟨s, hs⟩ := Submodule.mem_span_singleton.mp this
    exact ⟨s, hs.symm⟩

  haveI : IsLocalHom (algebraMap A S) := by
    refine ⟨fun a ha => ?_⟩
    by_contra hna
    have hmem : a ∈ maximalIdeal A := (IsLocalRing.mem_maximalIdeal _).mpr hna
    have : i a ∈ maximalIdeal S := hI₀m (by rw [hI₀]; exact Ideal.mem_map_of_mem _ hmem)
    exact (IsLocalRing.mem_maximalIdeal _).mp this ha
  have hnon : Nontrivial (KaehlerDifferential A S) := by
    by_contra hsub
    rw [not_nontrivial_iff_subsingleton] at hsub
    haveI : Algebra.FormallyUnramified A S := (Algebra.formallyUnramified_iff A S).mpr hsub
    have hmax := Algebra.FormallyUnramified.map_maximalIdeal (R := A) (S := S)
    apply ht
    have h1 := htm
    rw [← hmax] at h1
    exact h1
  haveI : Module.Free S (KaehlerDifferential A S) := Module.free_of_flat_of_isLocalRing
  have hinj : ∀ s : S, s • dt = 0 → s = 0 := by
    let b := Module.Free.chooseBasis S (KaehlerDifferential A S)
    haveI : Nonempty (Module.Free.ChooseBasisIndex S (KaehlerDifferential A S)) := by
      by_contra hne
      rw [not_nonempty_iff] at hne
      apply not_subsingleton (KaehlerDifferential A S)
      exact b.repr.toEquiv.subsingleton_congr.mpr inferInstance
    obtain ⟨j⟩ := this
    obtain ⟨s₀, hs₀⟩ := hsurj (b j)
    let f : S →ₗ[S] S := (b.coord j).comp (LinearMap.toSpanSingleton S _ dt)
    have hf : ∀ s, f s = b.coord j (s • dt) := fun s => rfl
    have hfsurj : Function.Surjective f := by
      intro c
      refine ⟨c * s₀, ?_⟩
      rw [hf, mul_smul, ← hs₀, map_smul, Module.Basis.coord_apply, Module.Basis.repr_self, Finsupp.single_eq_same,
        smul_eq_mul, mul_one]
    have hfinj := OrzechProperty.injective_of_surjective_endomorphism f hfsurj
    intro s hs
    apply hfinj
    rw [hf, hs, map_zero, map_zero]

  intro ω
  obtain ⟨s, hs⟩ := hsurj ω
  refine ⟨s, hs, fun s' hs' => ?_⟩
  have : (s' - s) • dt = 0 := by rw [sub_smul, ← hs, ← hs', sub_self]
  exact sub_eq_zero.mp (hinj _ this)

#print axioms solution

end S_RingHom_existsUnique_eq_smul_kaehlerDifferential_D_of_formallySmooth_of_maximalIdeal_eq_map_sup_span
end P2MW
export P2MW.S_RingHom_existsUnique_eq_smul_kaehlerDifferential_D_of_formallySmooth_of_maximalIdeal_eq_map_sup_span (solution)
