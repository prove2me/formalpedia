-- Prove2me | solution 1 for P2M_GroupTheoreticShannonCapacity_MAlpha_M__det_72ab166505ea
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T07:47:10.020394+00:00
-- url     : https://prove2.me/submissions/3c127c0e-40a4-4b35-bd9d-66d93f437fe4

import Mathlib.Algebra.Group.Pi.Units
import Definitions.Def_GroupTheoreticShannonCapacity_P0Matrix
import Definitions.Def_GroupTheoreticShannonCapacity_MAlpha
import Theorems.Thm_P2M_GroupTheoreticShannonCapacity_MAlpha_det_xR__add_yI_9d0b1d30422b
import Theorems.Thm_P2M_GroupTheoreticShannonCapacity_MAlpha_R__sub_one_isUnit_29a9b3d1283b
import Theorems.Thm_P2M_GroupTheoreticShannonCapacity_MAlpha_M__factorization_ff46d0e46406

set_option autoImplicit true
open GroupTheoreticShannonCapacity GroupTheoreticShannonCapacity.MAlpha
open Matrix
namespace GroupTheoreticShannonCapacity.MAlpha
theorem _root_.solution (n : ℕ) (hn : 1 ≤ n) (α : ℝ) (hα : α ≠ -1) :
    (Mα n α).det = ((-1)^n * α + α^n) / ((-1)^n * α + (-1)^n) := by
  have hfact := Mα_factorization n α hα
  rw [hfact, Matrix.det_mul]
  have hinv := Rα_sub_one_isUnit n hn α hα
  have hdet_inv : (Rα n α - 1)⁻¹.det = ((Rα n α - 1).det)⁻¹ := by
    rw [Matrix.det_nonsing_inv, Ring.inverse_eq_inv]
  rw [hdet_inv]
  -- Compute the two determinants using det_xRα_add_yI
  have hdet_num : (Rα n α + α • 1).det = (-1)^n * α + α^n := by
    have h := det_xRα_add_yI n hn 1 α α
    simp only [one_smul] at h
    exact h
  have hdet_denom : (Rα n α - 1).det = (-1)^n * α + (-1)^n := by
    have h := det_xRα_add_yI n hn 1 (-1) α
    simp only [one_smul, neg_one_smul] at h
    exact h
  rw [hdet_num, hdet_denom]
  field_simp
end GroupTheoreticShannonCapacity.MAlpha
