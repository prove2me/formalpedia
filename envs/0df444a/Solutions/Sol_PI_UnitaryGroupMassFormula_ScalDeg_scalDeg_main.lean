-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.ScalDeg.scalDeg_main
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T11:03:34.897115+00:00
-- url     : https://prove2.me/submissions/2e5ccbef-7999-4611-a6f1-a957e4265cd7

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_ScalDeg
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ScalarDegree_ScalDegMain
import Theorems.Thm_PI_UnitaryGroupMassFormula_ScalDeg_part_two
import Theorems.Thm_PI_UnitaryGroupMassFormula_ScalDeg_part_one

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.ScalDeg
open MvPolynomial PI.ScalDeg
namespace PI.UnitaryGroupMassFormula.ScalDeg
theorem _root_.solution : PI.ScalDeg.ScalDeg := by
  intro T _ N N' s s' Q dg hQ y'
  exact ⟨part_one s s' Q dg hQ y', part_two s s' Q y'⟩
end PI.UnitaryGroupMassFormula.ScalDeg
