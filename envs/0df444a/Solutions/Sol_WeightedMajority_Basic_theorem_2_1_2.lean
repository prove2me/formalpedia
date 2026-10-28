-- Prove2me | solution 2 for WeightedMajority.Basic.theorem_2_1
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-27T13:59:30.626535+00:00
-- url     : https://prove2.me/submissions/63daa72a-f478-4fed-8e60-c6085500be26

import Mathlib
import Definitions.Def_WeightedMajority_Basic_IsWMRun
import Theorems.Thm_WeightedMajority_Basic_weight_potential

-- carved verbatim out of submission 00ffda6e-12b5-4236-a1ad-bec356986abc, lines 121-156

section
open WeightedMajority.Basic

theorem solution {n T : ℕ} (β : ℝ) (hβ₀ : 0 ≤ β) (hβ₁ : β < 1)
    (initial : Fin n → ℝ) (hinitial : ∀ i, 0 < initial i)
    (x : Fin T → Fin n → Bool) (label : Fin T → Bool)
    (w : ℕ → Fin n → ℝ) (prediction : Fin T → Bool)
    (hrun : IsWMRun β initial x label w prediction)
    (hfinal : 0 < totalWeight w T) :
    (mistakeCount prediction label : ℝ) ≤
      Real.log (totalWeight w 0 / totalWeight w T) /
        Real.log (2 / (1 + β)) := by
  have hp := WeightedMajority.Basic.weight_potential β hβ₀ hβ₁ initial hinitial x label w prediction hrun
  have hq : 0 < (1 + β) / 2 := by linarith
  have hq1 : (1 + β) / 2 < 1 := by linarith
  have h0 : 0 < totalWeight w 0 := by
    by_contra hh
    have hm := mul_nonpos_of_nonpos_of_nonneg (le_of_not_gt hh) (pow_nonneg hq.le (mistakeCount prediction label))
    linarith
  have hl := Real.log_le_log hfinal hp
  rw [Real.log_mul h0.ne' (pow_pos hq _).ne', Real.log_pow] at hl
  have hr : Real.log (totalWeight w 0 / totalWeight w T) =
      Real.log (totalWeight w 0) - Real.log (totalWeight w T) :=
    Real.log_div h0.ne' hfinal.ne'
  have hd : Real.log (2 / (1 + β)) = -Real.log ((1 + β) / 2) := by
    have he : (2 : ℝ) / (1 + β) = ((1 + β) / 2)⁻¹ := by
      field_simp
    rw [he, Real.log_inv]
  have hdpos : 0 < Real.log (2 / (1 + β)) := by
    rw [hd]
    have hh := Real.log_neg hq hq1
    linarith
  rw [le_div_iff₀ hdpos, hr, hd]
  nlinarith

end
