-- Prove2me | solution 1 for PI.WGL.sqAct_smul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T11:14:27.538308+00:00
-- url     : https://prove2.me/submissions/f73825cc-d9d2-43b8-9d11-5ab4e17162e0

import Definitions.Def_Formalism_PeriodIntegrals_GTLower
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinLowering_ZScalarVanish
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinLowering_Assembly

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.WGL
open Formalism.BasicNotions MvPolynomial
namespace PI.WGL
theorem _root_.solution {k : ℕ} (mu : DomWeight k) (g : GL (Fin k) ℂ) (c : ℂ)
    (x : MvPolynomial (Fin k × Fin k) ℂ) : sqAct ℂ k mu g (c • x) = c • sqAct ℂ k mu g x := by
  rw [sqAct, sqAct, map_smul, smul_comm]
end PI.WGL
