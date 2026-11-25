-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.UnimodLocStd.target_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T10:47:41.712663+00:00
-- url     : https://prove2.me/submissions/751192a1-e422-46a4-87b7-edd60718d976

import Definitions.Def_Formalism_PeriodIntegrals_UnimodLocStd
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnimodularLocalStandard_Development

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped ComplexConjugate
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.UnimodLocStd
open PI.ULS
namespace PI.UnitaryGroupMassFormula.UnimodLocStd
theorem _root_.solution (hB : StepB) (hC : StepC) : PI.UnimodLocStd := by
  intro a b c d ha hd lam hlam hok m _ _ Λa hsd hθ h1 h2 l hl
  obtain ⟨g, hg, g1, g2, g3⟩ := hB a b c d ha hd lam hlam hok m Λa hsd hθ h1 h2 l hl
  exact hC a b c d ha hd lam hlam hok m Λa g hθ l hl hg g1 g2 g3
end PI.UnitaryGroupMassFormula.UnimodLocStd
