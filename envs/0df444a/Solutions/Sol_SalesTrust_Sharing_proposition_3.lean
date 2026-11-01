-- Prove2me | solution 1 for SalesTrust.Sharing.proposition_3
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-31T14:16:46.794987+00:00
-- url     : https://prove2.me/submissions/9579edf8-3ede-4be1-92f2-b10fcbc7ef31

import Mathlib
import Definitions.Def_SalesTrust_Sharing_Model
import Theorems.Thm_SalesTrust_Sharing_proposition_1
import Theorems.Thm_SalesTrust_Sharing_proposition_2
import Theorems.Thm_SalesTrust_Sharing_eq_31

open SalesTrust.Sharing

theorem solution (P : Params) (hS : P.Standing) (mNE mE : Menu)
    (hNE : IsOptimalNE P mNE) (hE : IsOptimalE P mE) :
    retailerProfit P mNE ≤ retailerProfit P mE ↔ P.δ ≤ deltaTilde P := by
  have h1 := (proposition_1 P hS).2 mNE hNE
  have h2 := (proposition_2 P hS).2 mE hE
  subst h1; subst h2
  have h31 := eq_31 P hS
  obtain ⟨hp0, hp1, hV, -, hd0, hd1⟩ := hS
  set s := Real.sqrt (1 + P.p) with hs
  have hs1 : 1 < s := by
    rw [hs, Real.lt_sqrt (by norm_num)]; linarith
  have hss : s ^ 2 = 1 + P.p := Real.sq_sqrt (by linarith)
  have hdt : deltaTilde P = 1 / (1 + s) := rfl
  -- key: δ ≤ δ̃ ↔ 0 ≤ 1 - δ(2 + δ p)
  have hkey : P.δ ≤ deltaTilde P ↔ 0 ≤ 1 - P.δ * (2 + P.δ * P.p) := by
    rw [hdt, le_div_iff₀ (by linarith)]
    have hfac : 1 - P.δ * (2 + P.δ * P.p) = (1 - P.δ * (1 + s)) * (1 - P.δ + s * P.δ) := by
      have : P.p = s ^ 2 - 1 := by linarith
      rw [this]; ring
    have hpos : 0 < 1 - P.δ + s * P.δ := by nlinarith
    rw [hfac]
    constructor
    · intro h; exact mul_nonneg (by linarith) hpos.le
    · intro h
      have := nonneg_of_mul_nonneg_left h hpos
      linarith
  rw [hkey, ← sub_nonneg, h31]
  rcases eq_or_lt_of_le hd0 with h0 | h0
  · -- δ = 0
    rw [← h0]
    constructor
    · intro _; norm_num
    · intro _; simp
  · have hK : 0 < P.δ * P.p ^ 3 * (1 - P.δ) * (P.VH - P.VL) ^ 2 /
        (2 * (1 - P.p) * (1 + P.δ * P.p) ^ 2) := by
      apply div_pos
      · apply mul_pos (mul_pos (mul_pos h0 (pow_pos hp0 3)) (by linarith))
        exact pow_pos (by linarith) 2
      · apply mul_pos (mul_pos (by norm_num) (by linarith))
        exact pow_pos (by nlinarith) 2
    constructor
    · intro h; exact (mul_nonneg_iff_of_pos_left hK).mp h
    · intro h; exact mul_nonneg hK.le h
