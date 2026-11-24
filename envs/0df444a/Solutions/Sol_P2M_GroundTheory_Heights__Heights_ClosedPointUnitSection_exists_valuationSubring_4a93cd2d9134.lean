-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_ClosedPointUnitSection_exists_valuationSubring_4a93cd2d9134
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:40:08.991006+00:00
-- url     : https://prove2.me/submissions/e4fd9fd3-6ced-47f2-b557-88d119499fde

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsClosedPointChart
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsClosedPointUnitSection

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
open ReciprocityTheory.ChartRestriction.G.Geo
noncomputable section
namespace GroundTheory.Heights₂.Heights
namespace ClosedPointUnitSection
theorem _root_.solution {K : Type*} [Field K] (A : Subring K)
    (P : Ideal A) [P.IsPrime] :
    ∃ W : ValuationSubring K, (∀ a : A, (a : K) ∈ W) ∧ (∀ a : A, a ∉ P → W.valuation (a : K) = 1) ∧
      ∀ a : A, a ∈ P → W.valuation (a : K) < 1 := by
  obtain ⟨W, h, hloc⟩ := LocalSubring.exists_le_valuationSubring (LocalSubring.ofPrime A P)
  have hA : ∀ a : A, (a : K) ∈ (LocalSubring.ofPrime A P).toSubring :=
    fun a => LocalSubring.le_ofPrime A P a.2
  have key : ∀ a : A, (IsUnit (algebraMap A (LocalSubring.ofPrime A P).toSubring a) ↔ a ∉ P) :=
    fun a => IsLocalization.AtPrime.isUnit_to_map_iff _ P a
  refine ⟨W, fun a => h (hA a), fun a ha => ?_, fun a ha => ?_⟩
  · have hu := ((key a).mpr ha).map (Subring.inclusion h)
    exact (W.valuation_eq_one_iff ⟨a, h (hA a)⟩).mp hu
  · refine lt_of_le_of_ne (W.valuation_le_one ⟨a, h (hA a)⟩) fun h1 => ?_
    have hu : IsUnit (Subring.inclusion h (algebraMap A (LocalSubring.ofPrime A P).toSubring a)) :=
      (W.valuation_eq_one_iff ⟨a, h (hA a)⟩).mpr h1
    exact (key a).mp ((isUnit_map_iff (Subring.inclusion h) _).mp hu) ha
end ClosedPointUnitSection
end GroundTheory.Heights₂.Heights
