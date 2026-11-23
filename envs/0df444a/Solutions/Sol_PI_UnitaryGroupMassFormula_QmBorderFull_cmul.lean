-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.QmBorderFull.cmul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:47:10.976259+00:00
-- url     : https://prove2.me/submissions/2f12ad82-f8c5-405d-a7c9-6115d8a4d58e

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_BorderMinorRotation_Development
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_BorderMinorRotation_SkipOneEqSuccAbove

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset Formalism.REAL
noncomputable section
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.QmBorderFull
open PI
namespace PI.UnitaryGroupMassFormula.QmBorderFull
theorem _root_.solution {A : Type*} [Ring A] (s : ℤ) (x y : A) : x * ((s : A) * y) = (s : A) * (x * y) := by
  rw [← mul_assoc, ← mul_assoc, Int.cast_comm]
end PI.UnitaryGroupMassFormula.QmBorderFull
