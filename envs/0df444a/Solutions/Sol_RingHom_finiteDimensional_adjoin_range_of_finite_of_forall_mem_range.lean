-- Prove2me | solution 1 for RingHom.finiteDimensional_adjoin_range_of_finite_of_forall_mem_range
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.230386+00:00
-- url     : https://prove2.me/submissions/9c3d833f-6a08-57a5-8a66-09baa38b4f32

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_RingHom_finiteDimensional_adjoin_range_of_finite_of_forall_mem_range

namespace SolChiFinField

theorem isIntegral_apply
    {R S A K : Type*} [CommRing R] [CommRing S] [Algebra R S] [Algebra.IsIntegral R S]
    [CommRing A] [CommRing K] [Algebra A K]
    (χ' : S →+* K) (h : ∀ r : R, χ' (algebraMap R S r) ∈ (algebraMap A K).range) (s : S) :
    IsIntegral A (χ' s) := by
  classical
  nontriviality K
  obtain ⟨p, hpm, hps⟩ := Algebra.IsIntegral.isIntegral (R := R) s
  set χ : R →+* K := χ'.comp (algebraMap R S) with hχ
  have hlift : p.map χ ∈ Polynomial.lifts (algebraMap A K) := by
    rw [Polynomial.lifts_iff_coeff_lifts]
    intro n
    rw [Polynomial.coeff_map]
    obtain ⟨a, ha⟩ := h (p.coeff n)
    exact ⟨a, ha⟩
  obtain ⟨q, hq, -, hqm⟩ :=
    Polynomial.lifts_and_degree_eq_and_monic hlift (hpm.map χ)
  refine ⟨q, hqm, ?_⟩
  rw [← Polynomial.eval_map, hq, Polynomial.eval_map, ← Polynomial.hom_eval₂,
    hps, map_zero]

end SolChiFinField

theorem solution
    {R S E K : Type*} [CommRing R] [CommRing S] [Algebra R S] [Module.Finite R S]
    [Field E] [Field K] [Algebra E K]
    (χ' : S →+* K) (h : ∀ r : R, χ' (algebraMap R S r) ∈ (algebraMap E K).range) :
    FiniteDimensional E (IntermediateField.adjoin E (Set.range χ')) := by
  classical
  obtain ⟨t, ht⟩ := Module.finite_def.mp (inferInstance : Module.Finite R S)
  have hint : ∀ x ∈ (χ' '' (t : Set S)), IsIntegral E x := by
    rintro _ ⟨s, -, rfl⟩
    exact SolChiFinField.isIntegral_apply χ' h s
  have hsub : Set.range χ' ⊆ IntermediateField.adjoin E (χ' '' (t : Set S)) := by
    rintro _ ⟨s, rfl⟩
    have hs : s ∈ Submodule.span R (t : Set S) := by rw [ht]; exact Submodule.mem_top
    induction hs using Submodule.span_induction with
    | mem x hx => exact IntermediateField.subset_adjoin _ _ ⟨x, hx, rfl⟩
    | zero => rw [map_zero]; exact zero_mem _
    | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
    | smul r x _ hx =>
      rw [Algebra.smul_def, map_mul]
      obtain ⟨a, ha⟩ := h r
      rw [← ha]
      exact mul_mem (IntermediateField.algebraMap_mem _ a) hx
  have heq : IntermediateField.adjoin E (Set.range χ')
      = IntermediateField.adjoin E (χ' '' (t : Set S)) := by
    apply le_antisymm (IntermediateField.adjoin_le_iff.mpr hsub)
    exact IntermediateField.adjoin.mono _ _ _ (by rintro _ ⟨s, -, rfl⟩; exact ⟨s, rfl⟩)
  rw [heq]
  haveI : Finite (χ' '' (t : Set S)) := Set.toFinite _
  exact IntermediateField.finiteDimensional_adjoin hint

end S_RingHom_finiteDimensional_adjoin_range_of_finite_of_forall_mem_range
end P2MW
export P2MW.S_RingHom_finiteDimensional_adjoin_range_of_finite_of_forall_mem_range (solution)
