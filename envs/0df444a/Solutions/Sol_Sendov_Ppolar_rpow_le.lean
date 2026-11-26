-- Prove2me | solution 1 for Sendov.Ppolar_rpow_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T19:01:08.277105+00:00
-- url     : https://prove2.me/submissions/bb8a0ee1-cdba-4d6b-be29-aad884429e7f

import Definitions.Def_Sendov_Reduction_Setup
import Definitions.Def_Sendov_Reduction_Polar
import Theorems.Thm_Sendov_Ppolar_le_lin
import Theorems.Thm_Sendov_M_pos
import Theorems.Thm_Sendov_Ppolar_nonneg


set_option autoImplicit false
open Sendov
open MeasureTheory
variable {n : ℕ} {a x t α : ℝ}
namespace Sendov
theorem _root_.solution (hn : 2 ≤ n) (hx : x ^ 2 ≤ 1) (hα : α = M n * (1 - a ^ 2) / 2)
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    Ppolar a x t ^ (((n : ℝ) - 1) / 2)
      ≤ Real.exp (α * (-1 + (2 - QQ (a * x) (a ^ 2) 1) * t)) := by
  have hM : (0 : ℝ) < M n := M_pos hn
  have he : (0 : ℝ) ≤ ((n : ℝ) - 1) / 2 := by simp only [M] at hM; linarith
  set y : ℝ := (1 - a ^ 2) * (-1 + (2 - QQ (a * x) (a ^ 2) 1) * t) with hy
  have h1 : Ppolar a x t ≤ Real.exp y := by
    refine le_trans (Ppolar_le_lin a x ht0 ht1) ?_
    have := Real.add_one_le_exp y
    linarith
  have h2 : Ppolar a x t ^ (((n : ℝ) - 1) / 2) ≤ Real.exp y ^ (((n : ℝ) - 1) / 2) :=
    Real.rpow_le_rpow (Ppolar_nonneg hx a t) h1 he
  refine h2.trans_eq ?_
  rw [← Real.exp_mul]
  congr 1
  simp only [M] at hα
  rw [hy, hα]
  ring
end Sendov
