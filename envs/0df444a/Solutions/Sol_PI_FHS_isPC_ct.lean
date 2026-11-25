-- Prove2me | solution 1 for PI.FHS.isPC_ct
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T09:38:17.695899+00:00
-- url     : https://prove2.me/submissions/f7c9b495-9359-4a86-8b99-b8c8363c599f

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockHarmonicSplitting_FockInnerSelfReNonneg
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockHarmonicSplitting_ConjTransposeOneKronecker
import Theorems.Thm_PI_FHS_sameBlock_symm

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
theorem _root_.solution {Z : Mat p q} (h : IsPC Z) : IsPC Zᴴ := by
  intro a b hab
  simp [Matrix.conjTranspose_apply, h b a (sameBlock_symm hab)]
end PI.FHS
