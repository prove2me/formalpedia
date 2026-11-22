-- Prove2me | solution 1 for SZ.mem_MahlerZ_of_pos
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T20:53:32.915429+00:00
-- url     : https://prove2.me/submissions/a962fff8-d77a-4011-b617-9a1bfe043e9b

import Definitions.Def_SZ_Trace
import Mathlib.Algebra.Order.Ring.Abs
import Definitions.Def_SZ_PellDesign
import Theorems.Thm_SZ_Pair_beta_lt_one
import Theorems.Thm_SZ_Pair_sq_alpha
import Theorems.Thm_SZ_Pair_sq_beta
import Theorems.Thm_SZ_Pair_sub_pos
import Theorems.Thm_SZ_mem_MahlerZ_of_floor_eq
import Theorems.Thm_SZ_rec2_even
import Theorems.Thm_SZ_rec2_real


set_option autoImplicit false
open SZ
variable {α β : ℝ} {a b : ℤ}
namespace SZ
theorem _root_.solution (h : Pair α β a b) (hβ : 0 < β) : α ∈ MahlerZ := by
  have hd := h.sub_pos
  have hβ1 : β < 1 := h.beta_lt_one
  have hupos : 0 < 2 / (α - β) := div_pos two_pos hd
  have hid : ∀ n : ℕ, 2 / (α - β) * α ^ n + (-(2 / (α - β))) * β ^ n
      = (rec2 a b 0 2 n : ℝ) := by
    refine rec2_real h.sq_alpha h.sq_beta ?_ ?_
    · norm_num
    · have hne : (α - β) ≠ 0 := ne_of_gt hd
      push_cast
      field_simp
      ring
  obtain ⟨N, hN⟩ : ∃ N : ℕ, β ^ N < (α - β) / 2 := exists_pow_lt_of_lt_one (by linarith) hβ1
  refine mem_MahlerZ_of_floor_eq h.one_lt (ne_of_gt hupos) N (rec2 a b 0 2) ?_ ?_
  · exact fun n _ => rec2_even ⟨0, by ring⟩ ⟨1, by ring⟩ n
  · intro n hn
    have hbn : β ^ n ≤ β ^ N := (pow_le_pow_iff_right_of_lt_one₀ hβ hβ1).mpr hn
    have hbpos : 0 < β ^ n := pow_pos hβ n
    have hval : 2 / (α - β) * α ^ n = (rec2 a b 0 2 n : ℝ) + 2 / (α - β) * β ^ n := by
      have := hid n; linarith
    have hstep : 2 / (α - β) * β ^ n < 2 / (α - β) * ((α - β) / 2) :=
      mul_lt_mul_of_pos_left (by linarith) hupos
    have heq : 2 / (α - β) * ((α - β) / 2) = 1 := by field_simp
    have hrpos : 0 < 2 / (α - β) * β ^ n := mul_pos hupos hbpos
    rw [Int.floor_eq_iff]
    refine ⟨?_, ?_⟩ <;> rw [hval] <;> linarith
end SZ
