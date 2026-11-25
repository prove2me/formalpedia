-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_ChartChoiceAlgClosed_specFirst_rename_shiftVar_f3b2f9ee6aab
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T02:36:09.364428+00:00
-- url     : https://prove2.me/submissions/ff8a034e-8ccc-4457-91b4-1e79219f74a1

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsChartChoiceAlgClosed
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PChartChoiceAlgClosed

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
open GroundTheory.Heights₂.Heights.ChartChoiceAlgClosed
variable {F : Type} [Field F] {n e : ℕ}
namespace GroundTheory.Heights₂.Heights.ChartChoiceAlgClosed
theorem _root_.solution (q : MvPolynomial (Fin e × Fin n) F) :
    specFirst (rename (shiftVar e n) q) 0 = q := by
  unfold specFirst
  rw [bind₁_rename]
  have : (specFirstVar (0 : Fin n → F) ∘ shiftVar e n) = X := by
    funext jm
    simp [specFirstVar, shiftVar]
  rw [this, bind₁_X_left]
  rfl
end GroundTheory.Heights₂.Heights.ChartChoiceAlgClosed
