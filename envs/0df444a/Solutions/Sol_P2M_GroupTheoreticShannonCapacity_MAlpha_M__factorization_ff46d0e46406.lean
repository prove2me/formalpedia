-- Prove2me | solution 1 for P2M_GroupTheoreticShannonCapacity_MAlpha_M__factorization_ff46d0e46406
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T07:44:34.340092+00:00
-- url     : https://prove2.me/submissions/af79b33d-ccc4-4187-a9da-a13c83477015

import Mathlib.Algebra.Group.Pi.Units
import Definitions.Def_GroupTheoreticShannonCapacity_P0Matrix
import Definitions.Def_GroupTheoreticShannonCapacity_MAlpha
import Theorems.Thm_P2M_GroupTheoreticShannonCapacity_MAlpha_R__sub_one_isUnit_29a9b3d1283b
import Theorems.Thm_P2M_GroupTheoreticShannonCapacity_MAlpha_M__mul_R__sub_one_c7dee40b7706

set_option autoImplicit true
open GroupTheoreticShannonCapacity GroupTheoreticShannonCapacity.MAlpha
open Matrix
namespace GroupTheoreticShannonCapacity.MAlpha
theorem _root_.solution (n : ℕ) (α : ℝ) (hα : α ≠ -1) :
    Mα n α = (Rα n α + α • 1) * (Rα n α - 1)⁻¹ := by
  cases n with
  | zero =>
    -- 0×0 matrices are trivially equal
    ext i; exact i.elim0
  | succ m =>
    -- For n ≥ 1, use the helper lemmas
    have hinv := Rα_sub_one_isUnit (m + 1) (by omega) α hα
    have hdet : IsUnit (Rα (m + 1) α - 1).det :=
      (Matrix.isUnit_iff_isUnit_det _).mp hinv
    -- From Mα * (Rα - 1) = Rα + α • 1, multiply by (Rα - 1)⁻¹ on the right
    have hmul := Mα_mul_Rα_sub_one (m + 1) α
    calc Mα (m + 1) α
        = Mα (m + 1) α * (Rα (m + 1) α - 1) * (Rα (m + 1) α - 1)⁻¹ := by
          rw [Matrix.mul_nonsing_inv_cancel_right _ _ hdet]
      _ = (Rα (m + 1) α + α • 1) * (Rα (m + 1) α - 1)⁻¹ := by
          rw [hmul]
end GroupTheoreticShannonCapacity.MAlpha
