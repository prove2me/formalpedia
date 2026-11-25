-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_AnalyticLimit_errE_mono_55b70623b837
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T13:35:15.451911+00:00
-- url     : https://prove2.me/submissions/e1cece70-be26-4b87-a875-ebc3980621c2

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
theorem _root_.solution {C C' t : ℝ} (hCC : C ≤ C') (h : 1 ≤ ell t) : errE C t ≤ errE C' t :=
  div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hCC (Real.log_nonneg h)) (by linarith)
end GroundTheory.Heights₂.Heights.AnalyticLimit
