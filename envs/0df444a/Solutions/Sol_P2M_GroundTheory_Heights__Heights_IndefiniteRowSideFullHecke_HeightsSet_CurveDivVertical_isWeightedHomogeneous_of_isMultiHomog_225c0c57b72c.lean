-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_HeightsSet_CurveDivVertical_isWeightedHomogeneous_of_isMultiHomog_225c0c57b72c
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:45:44.315648+00:00
-- url     : https://prove2.me/submissions/97496541-95de-4f0b-8b7b-014f69ae3581

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightsOfSets_Imports
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightsOfSets_PCurveDivVertical

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.HeightsSet
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo
noncomputable section
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.HeightsSet.CurveDivVertical
attribute [local instance] MvPolynomial.weightedGradedAlgebra
open Classical
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.HeightsSet.CurveDivVertical
theorem _root_.solution (T : Finset K) {f : MRing ι} {a : K → ℕ}
    (hf : IsMultiHomog f a) :
    IsWeightedHomogeneous (wt T) f (∑ k, if k ∈ T then a k else 0) := by
  classical
  intro d hd
  have hmon := hf d (mem_support_iff.mpr hd)
  rw [Finsupp.weight_apply, Finsupp.sum_fintype _ _ (by intros; simp), Fintype.sum_sigma]
  refine Finset.sum_congr rfl fun k _ ↦ ?_
  unfold wt
  by_cases hk : k ∈ T
  · simp only [hk, if_true, smul_eq_mul, mul_one]
    exact hmon k
  · simp [hk]
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.HeightsSet.CurveDivVertical
