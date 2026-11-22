-- Prove2me | solution 1 for SZ.floorNeg
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T20:53:32.199774+00:00
-- url     : https://prove2.me/submissions/de3b23d9-66e5-40dd-8790-6f98560ac905

import Definitions.Def_SZ_Trace
import Mathlib.Algebra.Order.Ring.Abs
import Definitions.Def_SZ_PellDesign
import Theorems.Thm_SZ_Pair_sq_alpha
import Theorems.Thm_SZ_Pair_sq_beta
import Theorems.Thm_SZ_Pair_abs_pow_le
import Theorems.Thm_P2M_SZ_xiDesign__pos_7fd4c80a1ef7
import Theorems.Thm_P2M_SZ_xiDesign__lt_one_4e35a34576eb
import Theorems.Thm_P2M_SZ_xiDesign_seed__77c5a5c95eea
import Theorems.Thm_P2M_SZ_xiDesign_seed__46b539b85d21
import Theorems.Thm_SZ_rec2_real


set_option autoImplicit false
open SZ
variable {α β : ℝ} {a b : ℤ}
namespace SZ
theorem _root_.solution (h : Pair α β a b) (hβ : β < 0) (n : ℕ) :
    ⌊xiDesign α β * α ^ n⌋ = rec2 a b 1 0 n - (if n % 2 = 0 then 1 else 0) := by
  have hp := xiDesign'_pos h
  have hlt := xiDesign'_lt_one h hβ
  have hid : xiDesign α β * α ^ n + xiDesign' α β * β ^ n = (rec2 a b 1 0 n : ℝ) :=
    rec2_real h.sq_alpha h.sq_beta (xiDesign_seed₀ h) (xiDesign_seed₁ h) n
  set r : ℝ := xiDesign' α β * β ^ n with hr
  have hval : xiDesign α β * α ^ n = (rec2 a b 1 0 n : ℝ) - r := by linarith
  have hβ0 : β ≠ 0 := ne_of_lt hβ
  have habs : |r| < 1 := by
    rw [hr, abs_mul, abs_of_pos hp]
    calc xiDesign' α β * |β ^ n| ≤ xiDesign' α β * 1 :=
          mul_le_mul_of_nonneg_left (h.abs_pow_le n) hp.le
      _ = xiDesign' α β := by ring
      _ < 1 := hlt
  obtain ⟨hlo, hhi⟩ := abs_lt.mp habs
  rcases Nat.even_or_odd n with he | ho
  · have hn2 : n % 2 = 0 := Nat.even_iff.mp he
    have hpos : 0 < r := mul_pos hp (he.pow_pos hβ0)
    rw [hn2, if_pos rfl, Int.floor_eq_iff]
    refine ⟨?_, ?_⟩ <;> push_cast <;> rw [hval] <;> linarith
  · have hn2 : n % 2 = 1 := Nat.odd_iff.mp ho
    have hneg : r < 0 := mul_neg_of_pos_of_neg hp (ho.pow_neg hβ)
    rw [hn2, if_neg (by norm_num), sub_zero, Int.floor_eq_iff]
    refine ⟨?_, ?_⟩ <;> rw [hval] <;> linarith
end SZ
