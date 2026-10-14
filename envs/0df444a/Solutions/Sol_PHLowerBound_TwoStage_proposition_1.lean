-- Prove2me | solution 1 for PHLowerBound.TwoStage.proposition_1
-- status  : ACCEPTED   (prove)
-- author  : @arexychen
-- created : 2026-10-13T02:43:51.947023+00:00
-- url     : https://prove2.me/submissions/bc4d8600-0eee-4e04-84a2-95ed72c3cacc

import Definitions.Def_PHLowerBound_TwoStage_Setting
open PHLowerBound.TwoStage Matrix
open scoped BigOperators

theorem solution {Ξ : Type*} [Fintype Ξ]
    {n₁ p₁ n₂ p₂ m₁ m₂ : ℕ} (P : SMIP Ξ n₁ p₁ n₂ p₂ m₁ m₂)
    (hX : ∀ ξ, (P.X ξ).Nonempty) (hopt : P.HasOptimalSolution)
    (w : Ξ → Fin n₁ → ℝ) (hw : ∑ ξ, P.p ξ • w ξ = 0) :
    P.D w ≤ P.zStar := by
  classical
  unfold SMIP.zStar
  refine le_iInf fun v => le_iInf fun hv => ?_
  have hx (ξ : Ξ) : (v.2 ξ).1 = v.1 := by
    exact (smul_right_injective _ (ne_of_gt (P.p_pos ξ))) (sub_eq_zero.mp (hv.2.2 ξ))
  have hcancel : ∑ ξ, P.p ξ * (w ξ ⬝ᵥ v.1) = 0 := by
    have hh := congrArg (fun a => a ⬝ᵥ v.1) hw
    simpa only [sum_dotProduct, smul_dotProduct, smul_eq_mul, zero_dotProduct] using hh
  have hreal : (∑ ξ, P.p ξ * (P.c ⬝ᵥ (v.2 ξ).1 + P.g ξ ⬝ᵥ (v.2 ξ).2 + w ξ ⬝ᵥ (v.2 ξ).1)) = P.efsObj v := by
    simp_rw [mul_add, Finset.sum_add_distrib]
    simp_rw [hx]
    simp only [hcancel, add_zero, SMIP.efsObj, hx, mul_add, Finset.sum_add_distrib]
  calc
    P.D w ≤ ∑ ξ, ((P.p ξ : ℝ) : EReal) * ((P.c ⬝ᵥ (v.2 ξ).1 + P.g ξ ⬝ᵥ (v.2 ξ).2 + w ξ ⬝ᵥ (v.2 ξ).1 : ℝ) : EReal) := by
      apply Finset.sum_le_sum
      intro ξ _
      apply mul_le_mul_of_nonneg_left
      · exact iInf₂_le (v.2 ξ) (hv.2.1 ξ)
      · exact_mod_cast (le_of_lt (P.p_pos ξ))
    _ = ((∑ ξ, P.p ξ * (P.c ⬝ᵥ (v.2 ξ).1 + P.g ξ ⬝ᵥ (v.2 ξ).2 + w ξ ⬝ᵥ (v.2 ξ).1) : ℝ) : EReal) := by
      simp only [← EReal.coe_mul]
      induction (Finset.univ : Finset Ξ) using Finset.induction_on with
      | empty => simp
      | @insert a s ha ih => simp only [Finset.sum_insert ha, ← EReal.coe_add, ih]
    _ = (P.efsObj v : EReal) := by rw [hreal]

