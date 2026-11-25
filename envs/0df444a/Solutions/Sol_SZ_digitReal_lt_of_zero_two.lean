-- Prove2me | solution 1 for SZ.digitReal_lt_of_zero_two
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T03:02:52.080889+00:00
-- url     : https://prove2.me/submissions/9641beb8-88cb-4f25-ac7a-7724ee1c0802

import Definitions.Def_SZ_SqrtThree
import Mathlib.Algebra.AlgebraicCard
import Mathlib.SetTheory.Cardinal.Continuum
import Definitions.Def_SZ_CoverTree
import Theorems.Thm_SZ_digitSum_congr
import Theorems.Thm_SZ_digitReal_le_digitSum_add
import Theorems.Thm_P2M_SZ_IsDigits_pow_pos__7f25d03f067c
import Theorems.Thm_SZ_digitSum_le_digitReal
import Theorems.Thm_SZ_digitSum_succ


set_option autoImplicit false
open SZ
open Filter Topology
namespace SZ
theorem _root_.solution {d d' : ℕ → ℤ} (h : IsDigits 3 d) (h' : IsDigits 3 d')
    {i : ℕ} (hagree : ∀ j, j < i → d j = d' j) (h0 : d i = 0) (h2 : d' i = 2) :
    digitReal 3 d < digitReal 3 d' := by
  have hp : (0:ℝ) < ((3:ℕ) : ℝ) ^ (i + 1) := h.pow_pos' _
  have hsum : digitSum 3 d i = digitSum 3 d' i := digitSum_congr hagree
  have hd : digitSum 3 d (i + 1) = digitSum 3 d i := by
    rw [digitSum_succ, h0]; norm_num
  have hd' : digitSum 3 d' (i + 1) = digitSum 3 d i + 2 / ((3:ℕ) : ℝ) ^ (i + 1) := by
    rw [digitSum_succ, h2, hsum]; norm_num
  have hup : digitReal 3 d ≤ digitSum 3 d (i + 1) + 1 / ((3:ℕ) : ℝ) ^ (i + 1) :=
    digitReal_le_digitSum_add h (i + 1)
  have hlo : digitSum 3 d' (i + 1) ≤ digitReal 3 d' := digitSum_le_digitReal h' (i + 1)
  rw [hd] at hup
  rw [hd'] at hlo
  have hhalf : 1 / ((3:ℕ) : ℝ) ^ (i + 1) < 2 / ((3:ℕ) : ℝ) ^ (i + 1) := by
    rw [div_lt_div_iff_of_pos_right hp]; norm_num
  linarith
end SZ
