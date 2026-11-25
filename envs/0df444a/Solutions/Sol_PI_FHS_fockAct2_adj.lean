-- Prove2me | solution 1 for PI.FHS.fockAct2_adj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T10:14:51.992252+00:00
-- url     : https://prove2.me/submissions/ab447254-e29a-48f2-84a5-44fa71d90f7f

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockHarmonicSplitting_FockInnerSelfReNonneg
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockHarmonicSplitting_ConjTransposeOneKronecker
import Theorems.Thm_PI_FHS_omAct_adj
import Theorems.Thm_PI_FHS_fockAct2_eq
import Theorems.Thm_PI_FHS_mixed2
import Theorems.Thm_PI_FHS_conjTranspose_one_kronecker

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
theorem _root_.solution {Z : Mat r s} (hZ : IsPC Z) (P Q : Pol p q r s) :
    fockInner (fockAct2 p q r s Z P) Q = - fockInner P (fockAct2 p q r s Zᴴ Q) := by
  rw [fockAct2_eq, fockAct2_eq,
    omAct_adj _ (mixed2 hZ), conjTranspose_one_kronecker]
end PI.FHS
