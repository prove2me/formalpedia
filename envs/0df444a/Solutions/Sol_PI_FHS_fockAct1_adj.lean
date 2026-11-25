-- Prove2me | solution 1 for PI.FHS.fockAct1_adj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T10:09:04.837893+00:00
-- url     : https://prove2.me/submissions/44eb6ad6-0f11-4417-965e-2e0368c81400

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockHarmonicSplitting_FockInnerSelfReNonneg
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockHarmonicSplitting_ConjTransposeOneKronecker
import Theorems.Thm_PI_FHS_omAct_adj
import Theorems.Thm_PI_FHS_fockAct1_eq
import Theorems.Thm_PI_FHS_mixed1
import Theorems.Thm_PI_FHS_conjTranspose_kronecker_one

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
theorem _root_.solution {Z : Mat p q} (hZ : IsPC Z) (P Q : Pol p q r s) :
    fockInner (fockAct1 p q r s Z P) Q = - fockInner P (fockAct1 p q r s Zᴴ Q) := by
  rw [fockAct1_eq, fockAct1_eq,
    omAct_adj _ (mixed1 hZ), conjTranspose_kronecker_one]
end PI.FHS
