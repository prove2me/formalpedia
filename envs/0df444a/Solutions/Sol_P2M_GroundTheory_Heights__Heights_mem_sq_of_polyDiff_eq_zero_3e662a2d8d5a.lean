-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_mem_sq_of_polyDiff_eq_zero_3e662a2d8d5a
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T08:58:18.39832+00:00
-- url     : https://prove2.me/submissions/b0333d1c-0f7f-40aa-990e-76021746f568

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsPolyLocalGenerators
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PPolyLocalGeneratorsDiff
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_tanLinPoly_zero_a4dc94d63023
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_sub_tanLinPoly_mem_sq_d80c589f9db2

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
theorem _root_.solution (p : Fin n → ℂ) {f : MvPolynomial (Fin n) ℂ}
    (h0 : eval p f = 0) (h1 : polyDiff p f = 0) : f ∈ RingHom.ker (eval p) ^ 2 := by
  simpa [h0, h1, tanLinPoly_zero] using sub_tanLinPoly_mem_sq p f
end GroundTheory.Heights₂.Heights
