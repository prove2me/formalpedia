-- Prove2me | solution 1 for PI.AmpRootJacW.sUp_neg
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:14:04.524852+00:00
-- url     : https://prove2.me/submissions/0be3e399-56ee-4f1b-a1c7-355d9c0a72a5

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_RootSubgroupBasics_TriShear
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_RootSubgroupJacobian_SUpPowEqZero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Matrix
noncomputable section
open PI PI.AmpRootJacW
variable {n : ℕ}
namespace PI.AmpRootJacW
theorem _root_.solution {V : Matrix (Fin n) (Fin n) ℂ} (hV : SUp V) : SUp (-V) := by
  intro i j h
  simp [hV i j h]
end PI.AmpRootJacW
