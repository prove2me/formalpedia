-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_AdmissibleAE_linForm_single_be165f805885
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T02:34:04.522291+00:00
-- url     : https://prove2.me/submissions/89c3ff5e-7cad-4de2-b99d-f34d1f341a6a

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsMahler
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PAdmissibleAE

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
open MvPolynomial MeasureTheory
noncomputable section
open GroundTheory.Heights₂.Heights.AdmissibleAE
variable {n : ℕ}
namespace GroundTheory.Heights₂.Heights.AdmissibleAE
theorem _root_.solution (j : Fin n) :
    linForm (Pi.single j (1 : ℂ)) = (X j : MvPolynomial (Fin n) ℂ) := by
  simp [linForm, Pi.single_apply]
end GroundTheory.Heights₂.Heights.AdmissibleAE
