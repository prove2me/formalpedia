-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_LineChowForm_cancelN_35a0c58da760
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T05:24:12.476345+00:00
-- url     : https://prove2.me/submissions/55d3737b-fc48-4fe4-b872-d2cb7df323e2

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_LineInhabitant
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_LineChowForm_cancel1_94c871ed607b

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
open GroundTheory.Heights₂.Heights.LineChowForm
variable {F : Type*} [Field F]
variable {F : Type*} [Field F]
namespace GroundTheory.Heights₂.Heights.LineChowForm
theorem _root_.solution (N : ℕ) (g : MvPolynomial (Fin 2 × Fin 2) F) (h : D2 ∣ X (0,0) ^ N * g) : D2 ∣ g := by
  induction N with
  | zero => simpa using h
  | succ N ih =>
    obtain ⟨q, hq⟩ := h
    exact ih (cancel1 _ q (by rw [← hq]; ring))
end GroundTheory.Heights₂.Heights.LineChowForm
