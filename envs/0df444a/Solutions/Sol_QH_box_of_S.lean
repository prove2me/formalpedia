-- Prove2me | solution 1 for QH.box_of_S
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T12:04:06.094408+00:00
-- url     : https://prove2.me/submissions/dd133ab3-dd76-4267-a915-d7186cb44836

import Definitions.Def_Development_AutomorphicArithmetic_MeanSquareBounds_PrimeSetTwoBounds
import Definitions.Def_Development_AutomorphicArithmetic_MeanSquareBounds_TailKExp
import Definitions.Def_Development_AutomorphicArithmetic_MeanSquareBounds_kappaC
import Definitions.Def_Formalism_GL3MeanSquares_ZeroFreeRegionGl2PrimeChoiceResults
import Definitions.Def_Development_AutomorphicArithmetic_MeanSquareBounds_BoxOfS
import Theorems.Thm_Formalism_HermitianLattices_ZeroFreeRegionGL2_finite_splitting_of_group
import Theorems.Thm_QH_kappaC
import Theorems.Thm_QH_tailK

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open Finset Formalism.HermitianLattices.ZeroFreeRegionGL2 Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds
namespace QH
private lemma num_box {ε τ Y y : ℝ} (hε : ε ≤ 1 / 4) (hτ : 0 < τ) (hY : 16 ≤ Y) (hy : Y ≤ y) :
    Y ^ ε ≤ y ^ (1 / 2 + τ) / 2 := by
  have hY1 : (1 : ℝ) ≤ Y := by linarith
  have hY0 : (0 : ℝ) < Y := by linarith
  have h1 : Y ^ ε ≤ Y ^ (1 / 4 : ℝ) := Real.rpow_le_rpow_of_exponent_le hY1 hε
  have h2 : (2 : ℝ) ≤ Y ^ (1 / 4 : ℝ) := by
    have h16 : (16 : ℝ) ^ (1 / 4 : ℝ) = 2 := by
      rw [show (16 : ℝ) = 2 ^ (4 : ℝ) by norm_num, ← Real.rpow_mul (by norm_num)]
      norm_num
    rw [← h16]
    exact Real.rpow_le_rpow (by norm_num) hY (by norm_num)
  have h3 : Y ^ (1 / 2 : ℝ) = Y ^ (1 / 4 : ℝ) * Y ^ (1 / 4 : ℝ) := by
    rw [← Real.rpow_add hY0]; norm_num
  have h4 : Y ^ (1 / 2 : ℝ) ≤ y ^ (1 / 2 : ℝ) := Real.rpow_le_rpow hY0.le hy (by norm_num)
  have h5 : y ^ (1 / 2 : ℝ) ≤ y ^ (1 / 2 + τ) :=
    Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)
  nlinarith
end QH
end

set_option autoImplicit false
open Finset Formalism.HermitianLattices.ZeroFreeRegionGL2 Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds
open QH
namespace QH
theorem _root_.solution :
    ∃ C : ℝ, 0 < C ∧ ∀ ε τ K : ℝ, 0 < ε → ε ≤ 1 / 4 → 0 < τ → 1 ≤ K → ∃ Y₀ : ℝ, ∀ Y ≥ Y₀, ∀ (Q : ℝ) (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N) (q : ℕ) (κ : ℕ → ℂ),
      Y ^ (ε / 6) ≤ Real.log Q → Real.log Q ≤ Y ^ (ε / 4) → GoodC Q χ → (∀ n : ℕ, χ (n : ZMod N) = κ n * J q n) →
      (∀ y ∈ Set.Icc Y (Y ^ K), ‖S ((Y ^ K) ^ 400) y q κ‖ ≤ y ^ (1 / 2 + τ) / 2) → Box Q C τ Y (Y ^ K) χ := by
  obtain ⟨C, hC, hk⟩ := kappaC
  refine ⟨C, hC, fun ε τ K hε hε4 hτ hK => ?_⟩
  obtain ⟨Y₁, h1⟩ := hk ε hε (by linarith)
  obtain ⟨Y₂, h2⟩ := tailK ε K hε (by linarith) hK
  refine ⟨max (max Y₁ Y₂) 16, fun Y hY Q N _ χ q κ hlo hhi hg hχ hS => ?_⟩
  have hY1 : Y₁ ≤ Y := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hY
  have hY2 : Y₂ ≤ Y := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hY
  have hY16 : 16 ≤ Y := le_trans (le_max_right _ _) hY
  refine ⟨hg, h1 Y hY1 Q N χ hlo hhi hg, fun y hy => ?_⟩
  have ht := h2 Y hY2 Q N χ hlo hhi hg
  have hy0 : 0 < y := by linarith [hy.1]
  have hX1 : 1 ≤ Y ^ K := by linarith [hy.1, hy.2]
  have hyz : y ≤ (Y ^ K) ^ 400 := le_trans hy.2 (le_self_pow₀ hX1 (by norm_num))
  rw [finite_splitting_of_group N χ y ((Y ^ K) ^ 400) hy0 hyz]
  have hSz : Sz χ y ((Y ^ K) ^ 400) = S ((Y ^ K) ^ 400) y q κ := by
    unfold Sz S
    apply Finset.sum_congr rfl
    intro n _
    rw [hχ n, J, mul_assoc]
  have htail : ‖(y : ℂ) * tailL χ ((Y ^ K) ^ 400)‖ ≤ Y ^ ε := by
    refine le_trans ?_ ht
    rw [norm_mul, norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_of_nonneg hy0.le,
      Real.norm_of_nonneg (by linarith)]
    exact mul_le_mul_of_nonneg_right hy.2 (norm_nonneg _)
  have hn := num_box hε4 hτ hY16 hy.1
  have hs := hS y hy
  calc ‖- Sz χ y ((Y ^ K) ^ 400) - (y : ℂ) * tailL χ ((Y ^ K) ^ 400)‖
      ≤ ‖- Sz χ y ((Y ^ K) ^ 400)‖ + ‖(y : ℂ) * tailL χ ((Y ^ K) ^ 400)‖ := norm_sub_le _ _
    _ ≤ y ^ (1 / 2 + τ) := by rw [norm_neg, hSz]; linarith
end QH
