-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_PrimeMapFractionRing_proof_9dd9162094e8
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-27T05:08:14.512145+00:00
-- url     : https://prove2.me/submissions/295a5638-fd5e-4e64-88bf-0a3188869ccb

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_StatementsNormForm
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_PPrimeMapFractionRing

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MvPolynomial
attribute [local instance] MvPolynomial.algebraMvPolynomial
namespace GroundTheory.Heights₂.Heights
namespace PrimeMapFractionRing
theorem _root_.solution : PrimeMapFractionRing.Statement := by
  intro O K _ _ _ _ _ n P hP hnc
  classical
  set M : Submonoid (MvPolynomial (Fin n) O) := (nonZeroDivisors O).map (C (σ := Fin n))
  have : IsLocalization M (MvPolynomial (Fin n) K) :=
    MvPolynomial.isLocalization (σ := Fin n) (nonZeroDivisors O) K

  have hprime : (Ideal.span {P}).IsPrime := (Ideal.span_singleton_prime hP.ne_zero).mpr hP
  have hdisj : Disjoint (M : Set (MvPolynomial (Fin n) O)) ↑(Ideal.span {P}) := by
    rw [Set.disjoint_left]
    rintro _ ⟨a, ha, rfl⟩ hmem
    have ha0 : a ≠ 0 := nonZeroDivisors.ne_zero ha
    have hCa : (C a : MvPolynomial (Fin n) O) ≠ 0 := by simpa using ha0
    have hdvd : P ∣ C a := Ideal.mem_span_singleton.mp hmem
    have hdeg : P.totalDegree = 0 := by
      have := totalDegree_le_of_dvd_of_isDomain hdvd hCa
      rw [totalDegree_C] at this
      omega
    exact hnc _ (totalDegree_eq_zero_iff_eq_C.mp hdeg)
  have hmap := IsLocalization.isPrime_of_isPrime_disjoint M (MvPolynomial (Fin n) K) _ hprime hdisj
  rw [Ideal.map_span, Set.image_singleton, MvPolynomial.algebraMap_def] at hmap

  have hinj : Function.Injective (map (σ := Fin n) (algebraMap O K)) :=
    map_injective _ (IsFractionRing.injective O K)
  have hne : map (algebraMap O K) P ≠ 0 := by
    intro h
    exact hP.ne_zero (hinj (by rw [h, map_zero]))
  exact (Ideal.span_singleton_prime hne).mp hmap
end PrimeMapFractionRing
end GroundTheory.Heights₂.Heights
