-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_WeierstrassPolynomialDivision_circleIntegral_finset_sum_c92dbf733ec4
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T03:31:24.552368+00:00
-- url     : https://prove2.me/submissions/e15d8cfd-d68a-48d5-a793-6d1efcc9408f

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StWeierstrassPolynomialDivision
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StParametricCircleIntegralAnalytic
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_MonicDifferenceQuotient
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PWeierstrassPolynomialDivision

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
open Topology Filter Metric Complex Real
noncomputable section
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets.WeierstrassPolynomialDivision
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets.WeierstrassPolynomialDivision
theorem _root_.solution {ι : Type} (u : Finset ι) (f : ι → ℂ → ℂ) {c : ℂ} {R : ℝ} (hR : 0 ≤ R)
    (hf : ∀ i ∈ u, ContinuousOn (f i) (sphere c R)) :
    (∮ z in C(c, R), ∑ i ∈ u, f i z) = ∑ i ∈ u, ∮ z in C(c, R), f i z := by
  classical
  induction u using Finset.induction_on with
  | empty => simp [circleIntegral]
  | insert a u ha ih =>
    simp only [Finset.sum_insert ha]
    rw [circleIntegral.integral_add ((hf a (by simp)).circleIntegrable hR)
      ((continuousOn_finsetSum u fun i hi => hf i (by simp [hi])).circleIntegrable hR),
      ih fun i hi => hf i (by simp [hi])]
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets.WeierstrassPolynomialDivision
