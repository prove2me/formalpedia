-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_MahlerIntegrand_proof_287835cc31c5
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-27T05:03:41.944971+00:00
-- url     : https://prove2.me/submissions/62966260-fb7c-4d79-b0af-ee703869c501

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsMahler
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_LogIntSphere
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PMahlerIntegrand
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ballProd_subset_polydisc_122db61ad4e0
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_HermNorm_li_exists_coord_le_93e1a2c1b1f2
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_LogInt_logNormT_b092fe5ed6e3


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
open MeasureTheory
namespace GroundTheory.Heights₂.Heights
namespace MahlerIntegrand
theorem _root_.solution : MahlerIntegrand.Statement := by
  intro n k δ h f hf _
  obtain ⟨C, hC0, hC⟩ := h.li_exists_coord_le
  have e : nrmGroups h k = LogInt.normT h Finset.univ := by
    funext u ij
    simp [nrmGroups, LogInt.normT]
  rw [e]
  exact (LogInt.logNormT h C hC0 hC Finset.univ f hf).1.mono_set (ballProd_subset_polydisc h C hC0 hC)
end MahlerIntegrand
end GroundTheory.Heights₂.Heights
