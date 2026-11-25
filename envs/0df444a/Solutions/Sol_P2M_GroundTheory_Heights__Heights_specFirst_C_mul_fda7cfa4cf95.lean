-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_specFirst_C_mul_fda7cfa4cf95
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T08:40:21.553598+00:00
-- url     : https://prove2.me/submissions/f7633d86-7234-45ea-a876-84cb2cdaf000

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsMahler
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PSpecFirstSwapMahler

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
theorem _root_.solution {n k : ℕ} (c : ℂ) (f : MvPolynomial (Fin (k + 1) × Fin n) ℂ) (u : Fin n → ℂ) :
    specFirst (C c * f) u = C c * specFirst f u := by
  unfold specFirst
  rw [map_mul, bind₁_C_right]
end GroundTheory.Heights₂.Heights
