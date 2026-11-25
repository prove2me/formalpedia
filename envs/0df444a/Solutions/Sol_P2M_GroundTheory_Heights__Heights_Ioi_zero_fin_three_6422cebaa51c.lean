-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Ioi_zero_fin_three_6422cebaa51c
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T04:17:28.389223+00:00
-- url     : https://prove2.me/submissions/e6168c71-59d8-477d-a54b-2f6bfc0a035f

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
theorem _root_.solution : Finset.Ioi (0 : Fin 3) = {1, 2} := by decide
end GroundTheory.Heights₂.Heights
