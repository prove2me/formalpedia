-- Prove2me | solution 1 for PI.ZW.isOpen_strip
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T11:16:30.843464+00:00
-- url     : https://prove2.me/submissions/a4330549-bdb1-4059-93bb-71aac33b1f85

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ZeroWindow_RightHalfWith
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ZeroWindow_Transfer

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Complex Filter Topology
open PI PI.ZW
open DirichletCharacter
namespace PI.ZW
theorem _root_.solution : IsOpen {s : ℂ | 0 < s.re ∧ s.re < 1} := by
  exact (isOpen_lt continuous_const Complex.continuous_re).inter (isOpen_lt Complex.continuous_re continuous_const)
end PI.ZW
