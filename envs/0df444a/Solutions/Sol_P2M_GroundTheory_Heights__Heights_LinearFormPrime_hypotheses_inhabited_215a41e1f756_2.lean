-- Prove2me | solution 2 for P2M_GroundTheory_Heights__Heights_LinearFormPrime_hypotheses_inhabited_215a41e1f756
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-27T05:03:47.779554+00:00
-- url     : https://prove2.me/submissions/753aed9f-a744-4931-9978-7455456665a6

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_StatementsNormForm

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
open MvPolynomial
noncomputable section
namespace GroundTheory.Heights₂.Heights
namespace LinearFormPrime
theorem _root_.solution : (fun _ : Fin 1 => (1 : ℚ)) ≠ 0 :=
  fun h => one_ne_zero (congrFun h 0)
end LinearFormPrime
end GroundTheory.Heights₂.Heights
