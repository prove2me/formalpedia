-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_AnalyticLimit_ell_anti_7cd2c6ef86ff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T13:37:32.27432+00:00
-- url     : https://prove2.me/submissions/53155b1c-282b-40ff-824a-79aa5ae6f1fa

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
theorem _root_.solution {t t' : ℝ} (ht' : 0 < t') (htt : t' ≤ t) : ell t ≤ ell t' :=
  Real.log_le_log (inv_pos.2 (lt_of_lt_of_le ht' htt)) (inv_anti₀ ht' htt)
end GroundTheory.Heights₂.Heights.AnalyticLimit
