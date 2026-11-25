-- Prove2me | solution 1 for PI.UConjT.eq_blk_of_last
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T10:37:33.827452+00:00
-- url     : https://prove2.me/submissions/42fd5db7-1696-45bc-9877-1b3159b798ce

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UMultOne
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryConjugation_TransferStep
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryConjugation_SubmatrixMemUnitaryGroup
import Theorems.Thm_PI_UConjT_blk_castSucc_castSucc
import Theorems.Thm_PI_UConjT_blk_castSucc_last
import Theorems.Thm_PI_UConjT_blk_last_castSucc
import Theorems.Thm_PI_UConjT_blk_last_last

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
theorem _root_.solution {n : ℕ} (k : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ)
    (hcol : ∀ i, k (Fin.castSucc i) (Fin.last n) = 0)
    (hrow : ∀ j, k (Fin.last n) (Fin.castSucc j) = 0) (hll : k (Fin.last n) (Fin.last n) = 1) :
    PI.UMultOne.blk n (k.submatrix Fin.castSucc Fin.castSucc) = k := by
  ext i j
  induction i using Fin.lastCases with
  | last =>
    induction j using Fin.lastCases with
    | last => rw [blk_last_last, hll]
    | cast b => rw [blk_last_castSucc, hrow]
  | cast a =>
    induction j using Fin.lastCases with
    | last => rw [blk_castSucc_last, hcol]
    | cast b => rw [blk_castSucc_castSucc, submatrix_apply]
end PI.UConjT
