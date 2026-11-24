-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_polyDiff_apply_f452501de9f2
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:48:57.024655+00:00
-- url     : https://prove2.me/submissions/8137a95e-160e-48de-a398-f268db253e04

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsPolyLocalGenerators
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PPolyLocalGeneratorsDiff

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
open MvPolynomial Module
noncomputable section
variable {n : ℕ}
namespace GroundTheory.Heights₂.Heights
theorem _root_.solution (p : Fin n → ℂ) (f : MvPolynomial (Fin n) ℂ) (j : Fin n) :
    polyDiff p f j = eval p (pderiv j f) := rfl
end GroundTheory.Heights₂.Heights
