-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_LocalGraphMass_frameFibreCount_ball_le_26a4f9913696
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T04:39:14.67919+00:00
-- url     : https://prove2.me/submissions/34d7d41d-9cfe-40f3-906d-9fdb7cda6676

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StLocalGraphMass
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PLocalGraphMass
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_LocalGraphMass_norm_le_of_frameProj_c4b386709b7d

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
open MeasureTheory Function
open scoped ENNReal
noncomputable section
open GroundTheory.Heights₂.Heights.LocalGraphMass
variable {n : ℕ}
namespace GroundTheory.Heights₂.Heights.LocalGraphMass
theorem _root_.solution (b : OrthonormalBasis (Fin n) ℂ (EuclideanSpace ℂ (Fin n)))
    (I : Finset (Fin n)) (S : Set (EuclideanSpace ℂ (Fin n))) (R : ℝ) (x : EuclideanSpace ℂ I) :
    frameFibreCount b I (S ∩ Metric.ball 0 R) (WithLp.ofLp x) ≤
      (Metric.ball (0 : EuclideanSpace ℂ I) R).indicator
        (fun _ => ⨆ y : I → ℂ, frameFibreCount b I S y) x := by
  by_cases hx : x ∈ Metric.ball (0 : EuclideanSpace ℂ I) R
  · rw [Set.indicator_of_mem hx]
    refine le_trans ?_ (le_iSup (fun y => frameFibreCount b I S y) (WithLp.ofLp x))
    simp only [frameFibreCount]
    exact ENat.toENNReal_le.2 (Set.encard_le_encard fun z hz => ⟨hz.1.1, hz.2⟩)
  · rw [Set.indicator_of_notMem hx]
    have h : {z ∈ S ∩ Metric.ball 0 R | frameProj b I z = WithLp.ofLp x} = ∅ := by
      refine Set.eq_empty_of_forall_notMem fun z hz => hx ?_
      rw [mem_ball_zero_iff]
      exact (norm_le_of_frameProj b I z x hz.2.symm).trans_lt (mem_ball_zero_iff.1 hz.1.2)
    simp only [frameFibreCount]
    rw [h]
    simp
end GroundTheory.Heights₂.Heights.LocalGraphMass
