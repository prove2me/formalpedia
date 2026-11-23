-- Prove2me | solution 1 for PI.AmpRootJacW.vM_at
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T01:07:04.373781+00:00
-- url     : https://prove2.me/submissions/e6edb16b-f42e-47d9-89c7-3dfccc07c580

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
variable (S : Finset (Fin n × Fin n))
namespace PI.AmpRootJacW
theorem _root_.solution (v : S → ℂ) (q : S) : vM S v q.1.1 q.1.2 = v q := by
  unfold vM
  rw [dif_pos q.2]
end PI.AmpRootJacW
