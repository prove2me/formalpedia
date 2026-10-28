-- Prove2me | solution 2 for RobustPower.AdaptGap.theorem_5_1_robust_le_four_adapt
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-27T14:54:48.313989+00:00
-- url     : https://prove2.me/submissions/fec88085-e303-498d-b15c-f87e2d9f7482

import Mathlib
import Definitions.Def_RobustPower_AdaptGap_Problems
import Theorems.Thm_RobustPower_AdaptGap_eq_5_3_5_4_cost_bound
import Theorems.Thm_RobustPower_AdaptGap_eq_5_2_doubled_feasible

-- carved verbatim out of submission d6e8b6ee-ff42-4a0a-8296-b95be77fce71, lines 105-126

section
open Matrix RobustPower.AdaptGap

theorem solution {m n₁ n₂ : ℕ} {Ω : Type*}
    (A : Matrix (Fin m) (Fin n₁) ℝ) (B : Matrix (Fin m) (Fin n₂) ℝ)
    (b : Ω → Fin m → ℝ) (c : Fin n₁ → ℝ) (d : Ω → Fin n₂ → ℝ)
    (I₁ : Set (Fin n₁)) (I₂ : Set (Fin n₂))
    (hc : 0 ≤ c) (hb : ∀ ω, 0 ≤ b ω) (hd : ∀ ω, 0 ≤ d ω)
    (hsym : RobustPower.StochGap.IsSymmetric (scenarioSet b d)) :
    zRob A B b c d I₁ I₂ ≤ (4 : EReal) * zAdapt A B b c d I₁ I₂ := by
  obtain ⟨u, hu⟩ := hsym
  obtain ⟨ω₀, rfl⟩ := hu.1
  apply (EReal.div_le_iff_le_mul (by norm_num : (0 : EReal) < 4) (EReal.natCast_ne_top 4)).mp
  apply le_iInf
  intro x
  apply le_iInf
  intro y
  apply le_iInf
  intro hfeas
  apply (EReal.div_le_iff_le_mul (by norm_num : (0 : EReal) < 4) (EReal.natCast_ne_top 4)).mpr
  have hf := RobustPower.AdaptGap.eq_5_2_doubled_feasible A B b d I₁ I₂ x y ω₀ hb hd hfeas hu
  have hz : zRob A B b c d I₁ I₂ ≤ robCost c d ((2 : ℝ) • x) ((2 : ℝ) • y ω₀) :=
    iInf_le_of_le _ (iInf_le_of_le _ (iInf_le _ hf))
  exact hz.trans (RobustPower.AdaptGap.eq_5_3_5_4_cost_bound A B b c d I₁ I₂ x y ω₀ hc hb hd hfeas hu)

end
