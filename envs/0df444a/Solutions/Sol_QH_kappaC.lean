-- Prove2me | solution 1 for QH.kappaC
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T03:38:23.973016+00:00
-- url     : https://prove2.me/submissions/f8bdc4e0-f5a2-4a71-8677-34e20b856223

import Definitions.Def_Development_AutomorphicArithmetic_MeanSquareBounds_PrimeSetTwoBounds
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_TailFinal
import Definitions.Def_Development_AutomorphicArithmetic_MeanSquareBounds_TailKExp
import Definitions.Def_Development_AutomorphicArithmetic_MeanSquareBounds_kappaC
import Theorems.Thm_Formalism_HermitianLattices_Ext_BoxTail_tail_mertens
import Theorems.Thm_QH_tailK


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset Formalism.HermitianLattices.ZeroFreeRegionGL2 Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds
open QH
namespace QH
theorem _root_.solution :
    ∃ C : ℝ, 0 < C ∧ ∀ ε : ℝ, 0 < ε → ε ≤ 1 → ∃ Y₀ : ℝ, ∀ Y ≥ Y₀, ∀ (Q : ℝ) (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N),
      Y ^ (ε / 6) ≤ Real.log Q → Real.log Q ≤ Y ^ (ε / 4) → GoodC Q χ → ‖logDerivLAtOne χ‖ ≤ C * Real.log Y := by
  obtain ⟨C0, hC0, hM⟩ := Formalism.HermitianLattices.Ext.BoxTail.tail_mertens
  refine ⟨400 * C0 + 1, by positivity, ?_⟩
  intro ε hε hε1
  obtain ⟨Y1, hY1⟩ := tailK ε 1 hε hε1 le_rfl
  refine ⟨max Y1 3, ?_⟩
  intro Y hY Q N _ χ hQ1 hQ2 hG
  have hYY1 : Y ≥ Y1 := le_trans (le_max_left _ _) hY
  have hY3 : (3 : ℝ) ≤ Y := le_trans (le_max_right _ _) hY
  have hY0 : (0 : ℝ) < Y := by linarith
  have hT := hY1 Y hYY1 Q N χ hQ1 hQ2 hG
  have e1 : (Y ^ (1 : ℝ)) ^ 400 = Y ^ (400 : ℕ) := by simp
  rw [e1, Real.rpow_one] at hT
  set z : ℝ := Y ^ (400 : ℕ) with hz
  have hlogY : 1 ≤ Real.log Y := by
    rw [Real.le_log_iff_exp_le hY0]
    have := Real.exp_one_lt_d9
    linarith
  have hz2 : (2 : ℝ) ≤ z := by
    have : Y ≤ Y ^ (400 : ℕ) := le_self_pow₀ (by linarith) (by norm_num)
    linarith
  have htail : ‖tailL χ z‖ ≤ 1 := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hY0] at hT
    have hYe : Y ^ ε ≤ Y := by
      have := Real.rpow_le_rpow_of_exponent_le (x := Y) (by linarith) hε1
      simpa using this
    have : Y * ‖tailL χ z‖ ≤ Y * 1 := by linarith
    exact le_of_mul_le_mul_left this hY0
  have hsum : ‖∑ n ∈ Icc 1 ⌊z⌋₊, (ArithmeticFunction.vonMangoldt n : ℂ) * χ n / n‖ ≤ 400 * C0 * Real.log Y := by
    calc ‖∑ n ∈ Icc 1 ⌊z⌋₊, (ArithmeticFunction.vonMangoldt n : ℂ) * χ n / n‖
        ≤ ∑ n ∈ Icc 1 ⌊z⌋₊, ‖(ArithmeticFunction.vonMangoldt n : ℂ) * χ n / n‖ := norm_sum_le _ _
      _ ≤ ∑ n ∈ Icc 1 ⌊z⌋₊, ArithmeticFunction.vonMangoldt n / n := by
        apply Finset.sum_le_sum
        intro n hn
        rw [norm_div, norm_mul, Complex.norm_real, Real.norm_eq_abs,
          abs_of_nonneg ArithmeticFunction.vonMangoldt_nonneg, Complex.norm_natCast]
        apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
        have := DirichletCharacter.norm_le_one χ (n : ZMod N)
        have h0 := (ArithmeticFunction.vonMangoldt_nonneg (n := n))
        nlinarith
      _ ≤ C0 * Real.log z := hM z hz2
      _ = 400 * C0 * Real.log Y := by rw [hz, Real.log_pow]; push_cast; ring
  have hL : logDerivLAtOne χ = -tailL χ z - ∑ n ∈ Icc 1 ⌊z⌋₊, (ArithmeticFunction.vonMangoldt n : ℂ) * χ n / n := by
    unfold tailL
    ring
  rw [hL]
  calc ‖-tailL χ z - ∑ n ∈ Icc 1 ⌊z⌋₊, (ArithmeticFunction.vonMangoldt n : ℂ) * χ n / n‖
      ≤ ‖tailL χ z‖ + ‖∑ n ∈ Icc 1 ⌊z⌋₊, (ArithmeticFunction.vonMangoldt n : ℂ) * χ n / n‖ := by
        refine (norm_sub_le _ _).trans ?_
        rw [norm_neg]
    _ ≤ 1 + 400 * C0 * Real.log Y := add_le_add htail hsum
    _ ≤ (400 * C0 + 1) * Real.log Y := by nlinarith
end QH
