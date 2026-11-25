-- Prove2me | solution 1 for PI.LocDualGen.FpD.norm_l_pos
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T09:50:52.584472+00:00
-- url     : https://prove2.me/submissions/e282dd6e-461f-44b1-8a0a-70e300cef02b

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalDualGenerator_FpDualUnram
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalDualGenerator_FpDual

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ValuativeRel
open PI PI.LocDualGen PI.LocDualGen.FpD
open PI.LocDualGen.W
variable {K : Type} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  (l : ℕ) [Fact l.Prime] [Algebra ℚ_[l] K] [FiniteDimensional ℚ_[l] K]
namespace PI.LocDualGen.FpD
theorem _root_.solution : (0 : ℝ) < ‖(l : ℚ_[l])‖ :=
  norm_pos_iff.2 (Nat.cast_ne_zero.2 (Fact.out : l.Prime).ne_zero)
end PI.LocDualGen.FpD
