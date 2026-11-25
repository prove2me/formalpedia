-- Prove2me | solution 1 for ReciprocityTheory.MultiplicativeHeights.wa_witt_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T15:06:18.427221+00:00
-- url     : https://prove2.me/submissions/ce3b6860-77f0-41cf-bb10-ef56f1c22ae1

import Definitions.Def_ReciprocityTheory_SemistableReduction_SemiDegAA
import Definitions.Def_ReciprocityTheory_SemistableReduction_SemiDegAB
import Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_waExt_zero
import Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_waExt_last
import Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_waExt_mid
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] ReciprocityTheory.MultiplicativeHeights.waExt_zero
attribute [local simp] ReciprocityTheory.MultiplicativeHeights.waExt_last
attribute [local simp] ReciprocityTheory.MultiplicativeHeights.waExt_mid

set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.MultiplicativeHeights
open Module
namespace ReciprocityTheory.MultiplicativeHeights
theorem _root_.solution {K : Type} [Field K] (r m : ℕ) (g : Fin r → K) (i j : Fin r) :
    wittMat r m g i j = if (i : ℕ) + j + 1 = r ∧ ((i : ℕ) < m ∨ (j : ℕ) < m) then 1
      else if (i : ℕ) = j ∧ m ≤ (i : ℕ) ∧ (i : ℕ) + m < r then g i else 0 := by
  unfold wittMat
  simp only [Matrix.of_apply, Fin.val_inj]
end ReciprocityTheory.MultiplicativeHeights
