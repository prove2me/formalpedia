-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_AnalyticLimit_errE_le_978993fb0664
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T13:29:53.637066+00:00
-- url     : https://prove2.me/submissions/c707ae91-1b91-4a4d-80a7-9653be4ceb2c

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_AnalyticLimit_Objects
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_AnalyticLimit_Telescoping

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.AnalyticLimit
open ReciprocityTheory.AnForm.M (FinHolAtlas)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Regular (RegChartData ell errE)
noncomputable section
namespace GroundTheory.Heights₂.Heights.AnalyticLimit
theorem _root_.solution {C t : ℝ} (hC : 0 ≤ C) (h : 1 ≤ ell t) : errE C t ≤ C := by
  unfold errE
  rw [div_le_iff₀ (by linarith)]
  exact mul_le_mul_of_nonneg_left (Real.log_le_self (by linarith)) hC
end GroundTheory.Heights₂.Heights.AnalyticLimit
