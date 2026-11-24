-- Prove2me | solution 1 for PI.FHS.omAct_apply
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:35:40.437793+00:00
-- url     : https://prove2.me/submissions/59bae096-2434-4b0b-829f-a0bf582168f1

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockHarmonicSplitting_FockInnerSelfReNonneg
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockHarmonicSplitting_ConjTransposeOneKronecker

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MvPolynomial Matrix FockH1Action
open PI PI.FHS
variable {p q r s : ℕ}
namespace PI.FHS
theorem _root_.solution (M : Matrix (Ln p q r s) (Ln p q r s) ℂ) (P : Pol p q r s) :
    omAct p q r s M P = ∑ l, ∑ l', M l l' • omE l l' P := by
  simp [FockH1Action.omAct, LinearMap.sum_apply, LinearMap.smulRight_apply]
end PI.FHS
