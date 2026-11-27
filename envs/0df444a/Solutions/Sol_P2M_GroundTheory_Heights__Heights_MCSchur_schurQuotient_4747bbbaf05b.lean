-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_MCSchur_schurQuotient_4747bbbaf05b
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-27T05:03:25.453801+00:00
-- url     : https://prove2.me/submissions/b2be6d9a-ae64-4ed3-aab0-f945a2f1b759

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_HermValueIsLeast
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_MCSchur_hermValue_isLeast_2b30b119e286

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.MCSchur
open Matrix
noncomputable section
variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
namespace GroundTheory.Heights₂.Heights.MCSchur
theorem _root_.solution : SchurQuotient.Statement := fun _ _ Y hY v => hermValue_isLeast Y hY v
end GroundTheory.Heights₂.Heights.MCSchur
