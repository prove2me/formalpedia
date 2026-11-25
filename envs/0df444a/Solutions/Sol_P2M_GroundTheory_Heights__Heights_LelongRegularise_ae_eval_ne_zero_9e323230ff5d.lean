-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_LelongRegularise_ae_eval_ne_zero_9e323230ff5d
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T06:27:19.798811+00:00
-- url     : https://prove2.me/submissions/b923f488-fa51-4d92-a2f8-3280fea787b5

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StLelongRegularise
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PSheetSumMeasurable
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_LogIntPoly
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PLelongRegularise
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_LogInt_ae_eval_ne_zero_e1e014cbbf7d


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
open MvPolynomial MeasureTheory Filter Topology Matrix ComplexSets
open scoped ContDiff
noncomputable section
open GroundTheory.Heights₂.Heights.LelongRegularise
namespace GroundTheory.Heights₂.Heights.LelongRegularise
theorem _root_.solution {ι : Type*} [Fintype ι] (g : MvPolynomial ι ℂ) (hg : g ≠ 0) :
    ∀ᵐ w : ι → ℂ, MvPolynomial.eval w g ≠ 0 := by
  have hU : (⋃ r : ℕ, LogInt.polydisc ι r) = Set.univ := by
    refine Set.eq_univ_of_forall fun w => ?_
    obtain ⟨r, hr⟩ := exists_nat_ge ‖w‖
    refine Set.mem_iUnion.mpr ⟨r, Set.mem_univ_pi.mpr fun i => ?_⟩
    rw [Metric.mem_closedBall, dist_zero_right]
    exact (norm_le_pi_norm w i).trans hr
  have h := (ae_restrict_iUnion_iff (fun r : ℕ => LogInt.polydisc ι r)
    (fun w => MvPolynomial.eval w g ≠ 0)).mpr fun r => LogInt.ae_eval_ne_zero g hg r
  rwa [hU, Measure.restrict_univ] at h
end GroundTheory.Heights₂.Heights.LelongRegularise
