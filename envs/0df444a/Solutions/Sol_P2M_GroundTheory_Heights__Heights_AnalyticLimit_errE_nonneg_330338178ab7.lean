-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_AnalyticLimit_errE_nonneg_330338178ab7
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T13:31:07.114985+00:00
-- url     : https://prove2.me/submissions/bbc8ceec-37a6-4f33-9ebb-4a5bf2f74098

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
theorem _root_.solution {C t : ℝ} (hC : 0 ≤ C) (h : 1 ≤ ell t) : 0 ≤ errE C t :=
  div_nonneg (mul_nonneg hC (Real.log_nonneg h)) (by linarith)
end GroundTheory.Heights₂.Heights.AnalyticLimit
