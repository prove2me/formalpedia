-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_isDomain_of_serre_84d7177c1de9
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T05:29:36.527267+00:00
-- url     : https://prove2.me/submissions/395d6bc2-1af4-4407-b541-9dc8099f28fc

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_Imports
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PCMRegularElement
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PFlatNormalFibres
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_RegularCurve
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_ExistsMulEqZeroOfMemAssociatedPrime
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_exists_mul_eq_zero_of_mem_associatedPrime_661bba168f30
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_isReduced_of_serre_3a1aaf270bc3
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_isIntegrallyClosed_of_serre_8afe127d72cc

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
open IsLocalRing RingTheory.Sequence Pointwise
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
theorem _root_.solution {B : Type} [CommRing B] [IsLocalRing B] [IsNoetherianRing B] (hR : SerreR B 1)
    (hS : SerreS B 2) : IsDomain B := by
  have hred : IsReduced B := isReduced_of_serre hR hS
  have hic : IsIntegrallyClosed B := isIntegrallyClosed_of_serre hR hS
  refine @NoZeroDivisors.to_isDomain B _ _ ⟨fun {u v} huv => ?_⟩
  by_contra! h
  obtain ⟨hu, hv⟩ := h
  let J : Ideal B := Ideal.span {u} ⊔ (⊥ : Submodule B B).colon {u}
  have hJ : ∃ s ∈ J, s ∈ nonZeroDivisors B := by
    by_contra! hJ
    have hsub : (J : Set B) ⊆ ⋃ p ∈ associatedPrimes B B, (p : Set B) := by
      rw [biUnion_associatedPrimes_eq_compl_nonZeroDivisors]
      exact fun s hs => hJ s hs
    obtain ⟨Q, hQ, hJQ⟩ := (Ideal.subset_union_prime_finite (associatedPrimes.finite B B) (f := id) ⊥ ⊥
      (fun Q hQ _ _ => hQ.isPrime)).mp hsub
    obtain ⟨t, ht, htu⟩ := exists_mul_eq_zero_of_mem_associatedPrime hR hS hQ
      (hJQ (Ideal.mem_sup_left (Ideal.mem_span_singleton_self u)))
    exact ht (hJQ (Ideal.mem_sup_right (by
      rw [Submodule.mem_colon_singleton, smul_eq_mul, Submodule.mem_bot]; exact htu)))
  obtain ⟨s, hsJ, hs⟩ := hJ
  obtain ⟨x, hx, w, hw, rfl⟩ := Submodule.mem_sup.mp hsJ
  obtain ⟨r, rfl⟩ := Ideal.mem_span_singleton'.mp hx
  have hwu : w * u = 0 := by
    rwa [Submodule.mem_colon_singleton, smul_eq_mul, Submodule.mem_bot] at hw
  have hxy : r * u * w = 0 := by rw [mul_assoc, mul_comm u w, hwu, mul_zero]
  let e := IsLocalization.mk' (FractionRing B) (r * u) (⟨r * u + w, hs⟩ : nonZeroDivisors B)
  have he : e * e = e := by
    rw [← IsLocalization.mk'_mul, IsLocalization.mk'_eq_iff_eq]
    congr 1
    simp only [Submonoid.coe_mul]
    linear_combination (-(r * u + w)) * hxy
  have hint : IsIntegral B e := by
    refine ⟨Polynomial.X ^ 2 - Polynomial.X, ?_, ?_⟩
    · exact Polynomial.monic_X_pow_sub (by rw [Polynomial.degree_X]; norm_num)
    · simp [Polynomial.eval₂_sub, pow_two, he]
  obtain ⟨c, hc⟩ := (isIntegrallyClosedIn_iff.mp hic).2 hint
  have hc' : c * (r * u + w) = r * u := by
    rw [IsLocalization.eq_mk'_iff_mul_eq] at hc
    exact IsLocalization.injective (FractionRing B) le_rfl (by rw [map_mul]; exact hc)
  have h1 : c * (w * w) = 0 := by linear_combination w * hc' + (1 - c) * hxy
  have h2 : (1 - c) * ((r * u) * (r * u)) = 0 := by linear_combination (-(r * u)) * hc' + c * hxy
  rcases IsLocalRing.isUnit_or_isUnit_one_sub_self c with hc1 | hc1
  · have hw0 : w = 0 := IsReduced.eq_zero w ⟨2, by rw [pow_two]; exact (hc1.mul_right_eq_zero).mp h1⟩
    subst hw0
    rw [add_zero] at hs
    apply hv
    exact (mul_left_mem_nonZeroDivisors_eq_zero_iff hs).mp (by rw [mul_assoc, huv, mul_zero])
  · have hx0 : r * u = 0 := IsReduced.eq_zero _ ⟨2, by rw [pow_two]; exact (hc1.mul_right_eq_zero).mp h2⟩
    rw [hx0, zero_add] at hs
    exact hu ((mul_left_mem_nonZeroDivisors_eq_zero_iff hs).mp hwu)
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
