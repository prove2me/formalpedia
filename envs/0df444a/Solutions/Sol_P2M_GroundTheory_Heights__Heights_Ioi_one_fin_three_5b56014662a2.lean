-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Ioi_one_fin_three_5b56014662a2
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T03:59:58.440599+00:00
-- url     : https://prove2.me/submissions/e333c815-02ef-4e68-8013-653b35547e4a

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Antisymmetric_Statements

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MvPolynomial
namespace GroundTheory.Heights₂.Heights
theorem _root_.solution : Finset.Ioi (1 : Fin 3) = {2} := by decide
end GroundTheory.Heights₂.Heights
