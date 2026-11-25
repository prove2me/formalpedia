-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_mahler_specFirst_eq_24ebff051de3
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T08:35:14.290911+00:00
-- url     : https://prove2.me/submissions/be4448bf-a7e8-45de-987a-769e280d72bf

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsMahler
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PMahlerAverageSplit

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
namespace GroundTheory.Heights₂.Heights
theorem _root_.solution (h3 : EvalSpecFirst.Statement) {n e : ℕ} (h : HermNorm n)
    (f : MvPolynomial (Fin (e + 1) × Fin n) ℂ) (v : Fin n → ℂ) :
    mahler h e (specFirst f v) =
      sphereMean h e (fun w => Real.log ‖eval (consGroup v w) f‖) := by
  unfold mahler
  congr 1
  funext w
  rw [h3]
end GroundTheory.Heights₂.Heights
