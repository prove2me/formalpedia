-- Prove2me | solution 1 for PI.FHS.fockAct1_eq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:36:18.387046+00:00
-- url     : https://prove2.me/submissions/fbfbeee3-9d83-49e8-8393-279fb4dce8c8

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
theorem _root_.solution (Z : Mat p q) :
    fockAct1 p q r s Z = omAct p q r s (Matrix.kroneckerMap (fun a b => a * b) Z (1 : Mat r s)) :=
  rfl
end PI.FHS
