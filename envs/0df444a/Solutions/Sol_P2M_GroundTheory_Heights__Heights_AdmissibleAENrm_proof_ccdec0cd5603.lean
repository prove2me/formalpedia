-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_AdmissibleAENrm_proof_ccdec0cd5603
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-27T04:52:28.083427+00:00
-- url     : https://prove2.me/submissions/439ccf87-92b3-4cee-99d5-57be223ba8c0

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsMahler
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PAdmissibleAENrm
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IsAdmissible_nrmv_70a1134c823d

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
open MvPolynomial MeasureTheory Matrix
noncomputable section
variable {n : ℕ}
namespace GroundTheory.Heights₂.Heights
namespace AdmissibleAENrm
theorem _root_.solution (h1 : AdmissibleAE.Statement) : AdmissibleAENrm.Statement := by
  intro n h Z hrel
  exact ae_restrict_of_ae ((h1 n Z hrel).mono fun v hv => hv.nrmv h)
end AdmissibleAENrm
end GroundTheory.Heights₂.Heights
