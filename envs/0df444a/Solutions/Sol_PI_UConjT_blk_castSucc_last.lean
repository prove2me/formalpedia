-- Prove2me | solution 1 for PI.UConjT.blk_castSucc_last
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T10:31:25.684966+00:00
-- url     : https://prove2.me/submissions/d1f7b5e3-200d-4921-a8c1-0f9b9adb69de

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UMultOne
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryConjugation_TransferStep
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryConjugation_SubmatrixMemUnitaryGroup

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.UConjT
open Matrix
namespace PI.UConjT
theorem _root_.solution (n : ℕ) (h : Matrix (Fin n) (Fin n) ℂ) (a : Fin n) :
    PI.UMultOne.blk n h (Fin.castSucc a) (Fin.last n) = 0 := by
  simp [PI.UMultOne.blk, Matrix.reindex_apply, finSumFinEquiv_symm_apply_castSucc,
    finSumFinEquiv_symm_last]
end PI.UConjT
