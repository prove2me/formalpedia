-- Prove2me | solution 1 for ReciprocityTheory.AnForm.A.det_single_add
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T12:06:08.550254+00:00
-- url     : https://prove2.me/submissions/28b60614-b568-44c7-b2ff-c58c4f1d9149

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_MaIntEmpty
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_PartsSt

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.A
open MeasureTheory ReciprocityTheory.AnForm
noncomputable section
namespace ReciprocityTheory.AnForm.A
theorem _root_.solution {n : ℕ} (j : Fin (n + 1)) (M : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) :
    (Matrix.single j j 1 + M).det = M.det + (M.submatrix j.succAbove j.succAbove).det := by
  classical
  have h1 : Matrix.single j j 1 + M = M.updateRow j (Pi.single j 1 + M j) := by
    ext a b
    by_cases ha : a = j
    · subst ha
      by_cases hb : b = a
      · simp [hb]
      · simp [hb, Ne.symm hb]
    · simp [ha, Ne.symm ha]
  rw [h1, Matrix.det_updateRow_add, Matrix.updateRow_eq_self, add_comm]
  congr 1
  rw [Matrix.det_succ_row _ j, Finset.sum_eq_single j]
  · have hs : ((M.updateRow j (Pi.single j 1)).submatrix j.succAbove j.succAbove) =
        M.submatrix j.succAbove j.succAbove := by
      ext a b; simp
    rw [hs]
    simp [Even.neg_one_pow ⟨(j : ℕ), rfl⟩]
  · intro k _ hk; simp [hk]
  · simp
end ReciprocityTheory.AnForm.A
