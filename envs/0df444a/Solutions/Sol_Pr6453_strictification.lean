-- Prove2me | solution 1 for Pr6453.strictification
-- status  : ACCEPTED   (prove)
-- author  : @gustasmickus
-- created : 2026-11-08T16:31:15.892102+00:00
-- url     : https://prove2.me/submissions/d252ca26-29c1-4b4e-9cec-01c0b3dcb695

/-
PR #6453: the strictification checks and the compiler grid, and the three tail ratios.
-/
import Definitions.Def_Pr6453_RankMoments
import Definitions.Def_Pr6453_Strictification

set_option autoImplicit false
set_option exponentiation.threshold 5000
set_option maxRecDepth 100000

namespace Pr6453

noncomputable section

/-! ## The strictification checks that are pure arithmetic -/

/-- The block estimate applies: `(31/32)^128 < 1/16`. -/
theorem decay_block : (decay : ℝ) ^ 128 < 1 / 16 := by
  unfold decay
  norm_num

/-- Completion, splitting and rounding: `12^64 < 13^63`. -/
theorem cutoff_floor : (cutoff : ℕ) ^ 64 < floor' ^ 63 := by
  unfold cutoff floor'
  norm_num

/-- Shifted exits and complement capacity: `2·(12^1920)^64 ≤ (145^1920)^63`. -/
theorem shifted_exits : 2 * ((cutoff : ℕ) ^ power) ^ 64 ≤ (145 ^ power) ^ 63 := by
  unfold cutoff power
  have h : 2 * (12 : ℕ) ^ 64 ≤ 145 ^ 63 := by norm_num
  have h2 : (2 * (12 : ℕ) ^ 64) ^ 1920 ≤ (145 ^ 63) ^ 1920 := Nat.pow_le_pow_left h 1920
  have h3 : 2 * ((12 : ℕ) ^ 1920) ^ 64 ≤ (2 * (12 : ℕ) ^ 64) ^ 1920 := by
    have hle : 2 ≤ (2 : ℕ) ^ 1920 := by norm_num
    have e : (2 * (12 : ℕ) ^ 64) ^ 1920 = (2 : ℕ) ^ 1920 * ((12 : ℕ) ^ 1920) ^ 64 := by
      rw [Nat.mul_pow, Nat.pow_right_comm]
    rw [e]
    exact Nat.mul_le_mul_right _ hle
  have h4 : (145 ^ 63) ^ 1920 = (145 ^ 1920) ^ 63 := by
    rw [Nat.pow_right_comm]
  rw [h4] at h2
  exact le_trans h3 h2

/-- The complementary capacity: `(63/64)^2100 < η`. -/
theorem theta_eta : (theta : ℝ) ^ logarithmPower < etaLower := by
  unfold theta logarithmPower etaLower
  norm_num

/-- The compiler's initial range: `145^(1920·t) < 2^2100`, the `compiler.factor` bound. -/
theorem compiler_range : (145 : ℝ) ^ ((power : ℝ) * (tested : ℝ)) < 2 ^ logarithmPower := by
  unfold power tested logarithmPower
  have hexp : ((1920 : ℕ) : ℝ) * (((3287019 : ℚ) / 1000000000 : ℚ) : ℝ)
      = (1920 : ℝ) * (3287019 / 1000000000 : ℝ) := by push_cast; ring
  rw [hexp]
  have hmono : (145 : ℝ) ^ ((1920 : ℝ) * (3287019 / 1000000000 : ℝ)) ≤ (145 : ℝ) ^ (7 : ℝ) := by
    apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
    norm_num
  have h7 : (145 : ℝ) ^ (7 : ℝ) = (145 : ℝ) ^ 7 := Real.rpow_natCast 145 7
  have hbig : (145 : ℝ) ^ 7 < (2 : ℝ) ^ 2100 := by
    have : (145 : ℕ) ^ 7 < 2 ^ 2100 := by decide
    exact_mod_cast this
  calc (145 : ℝ) ^ ((1920 : ℝ) * (3287019 / 1000000000 : ℝ)) ≤ (145 : ℝ) ^ (7 : ℝ) := hmono
    _ = (145 : ℝ) ^ 7 := h7
    _ < 2 ^ 2100 := hbig

/-- The absorbed tail: `1/(1 + power·reserve) + 4·(31/32)^1920 < 1`. -/
theorem tail_normalized :
    1 / (1 + (power : ℝ) * (reserve : ℝ)) + 4 * (decay : ℝ) ^ power < 1 := by
  unfold power reserve decay
  norm_num

/-- The negative control: the coarse block bound `4·(1/16)^15` cannot fund the claim. -/
theorem coarse_tail_fails :
    1 < 1 / (1 + (power : ℝ) * (reserve : ℝ)) + 4 * ((1 : ℝ) / 16) ^ (power / 128) := by
  unfold power reserve
  norm_num

/-- The compiler grid: the test exponent fits the grid. -/
theorem compiler_grid : H = 138100200000000 ∧ integerTestExponent < H := by
  unfold H integerTestExponent
  norm_num

/-! ## The three ratios that need shifted moments -/

/-- `α`, the ratio of the two rank moments at the tested saving. -/
def alpha : ℝ := moment paid (1 - (tested : ℝ)) / moment targets (1 - (tested : ℝ))

/-- `γ`, the paid moment one step `1/7` further out, against the split. -/
def gammaTail : ℝ :=
  moment paid (1 - (tested : ℝ) + 1 / 7) / ((12 : ℝ) ^ (1 / 7) * moment targets (1 - (tested : ℝ)))

/-- `δ`, the rounding charged against the split. -/
def deltaTail : ℝ :=
  (13652 * 13) / ((12 : ℝ) ^ (tested : ℝ) * moment targets (1 - (tested : ℝ)))

/-- **The strictification and the compiler grid.** -/
theorem strictification :
    (decay : ℝ) ^ 128 < 1 / 16 ∧
      (cutoff : ℕ) ^ 64 < floor' ^ 63 ∧
      2 * ((cutoff : ℕ) ^ power) ^ 64 ≤ (145 ^ power) ^ 63 ∧
      (theta : ℝ) ^ logarithmPower < (etaLower : ℝ) ∧
      (145 : ℝ) ^ ((power : ℝ) * (tested : ℝ)) < 2 ^ logarithmPower ∧
      1 / (1 + (power : ℝ) * (reserve : ℝ)) + 4 * (decay : ℝ) ^ power < 1 ∧
      1 < 1 / (1 + (power : ℝ) * (reserve : ℝ)) + 4 * ((1 : ℝ) / 16) ^ (power / 128) ∧
      H = 138100200000000 ∧ integerTestExponent < H :=
  ⟨decay_block, cutoff_floor, shifted_exits, theta_eta, compiler_range, tail_normalized,
    coarse_tail_fails, compiler_grid.1, compiler_grid.2⟩

end
end Pr6453

/-- **The strictification of PR #6453 and its compiler grid.** -/
theorem solution :
    (Pr6453.decay : ℝ) ^ 128 < 1 / 16 ∧
      (Pr6453.cutoff : ℕ) ^ 64 < Pr6453.floor' ^ 63 ∧
      2 * ((Pr6453.cutoff : ℕ) ^ Pr6453.power) ^ 64 ≤ (145 ^ Pr6453.power) ^ 63 ∧
      (Pr6453.theta : ℝ) ^ Pr6453.logarithmPower < (Pr6453.etaLower : ℝ) ∧
      (145 : ℝ) ^ ((Pr6453.power : ℝ) * (Pr6453.tested : ℝ)) < 2 ^ Pr6453.logarithmPower ∧
      1 / (1 + (Pr6453.power : ℝ) * (Pr6453.reserve : ℝ)) +
        4 * (Pr6453.decay : ℝ) ^ Pr6453.power < 1 ∧
      1 < 1 / (1 + (Pr6453.power : ℝ) * (Pr6453.reserve : ℝ)) +
        4 * ((1 : ℝ) / 16) ^ (Pr6453.power / 128) ∧
      Pr6453.H = 138100200000000 ∧ Pr6453.integerTestExponent < Pr6453.H :=
  Pr6453.strictification
