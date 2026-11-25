-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.ClassNumImQInt.adjoin_top
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T10:38:19.153253+00:00
-- url     : https://prove2.me/submissions/a38e1926-4e78-4e7a-b05b-13d15a232477

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_ClassNumImQ
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_QuadraticDifference_QuadraticDifferenceForm
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ClassNumberIntegrality_HalfIntegral

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.ClassNumImQInt
open NumberField Polynomial
namespace PI.UnitaryGroupMassFormula.ClassNumImQInt
theorem _root_.solution {K : Type} [Field K] [NumberField K] (b : K)
    (h : IntermediateField.adjoin ℚ {b} = ⊤) : Algebra.adjoin ℚ {b} = ⊤ := by
  rw [← IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic
    (Algebra.IsAlgebraic.isAlgebraic b), h]
  exact IntermediateField.top_toSubalgebra
end PI.UnitaryGroupMassFormula.ClassNumImQInt
