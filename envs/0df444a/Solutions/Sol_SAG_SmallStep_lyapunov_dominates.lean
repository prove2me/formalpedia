-- Prove2me | solution 1 for SAG.SmallStep.lyapunov_dominates
-- status  : ACCEPTED   (prove)
-- author  : @涼宮 ハルヒ
-- created : 2026-10-24T03:37:19.86342+00:00
-- url     : https://prove2.me/submissions/5b0263aa-0108-4e75-a9a7-844238005aa5

import Definitions.Def_SAG_SmallStep_lyapunov
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

open Finset SAG.SmallStep
open scoped RealInnerProductSpace

namespace D24SAGDomination

lemma expand {p n : ℕ} (α : ℝ) (u : Fin n → EuclideanSpace ℝ (Fin p))
    (w : EuclideanSpace ℝ (Fin p)) :
    quadForm (lyapA α) (lyapB α) (ContinuousLinearMap.id ℝ _) u w =
      3 * (n : ℝ) * α ^ 2 * (∑ i, ‖u i‖ ^ 2) +
      (α ^ 2 / n * (1 / (n : ℝ) - 2)) * ‖∑ i, u i‖ ^ 2 -
      2 * (α * (1 - 1 / (n : ℝ))) * ⟪∑ i, u i, w⟫ + ‖w‖ ^ 2 := by
  classical
  have hij (i j : Fin n) :
      ⟪u i, lyapA α i j (u j)⟫ =
        (if i = j then 3 * (n : ℝ) * α ^ 2 * ⟪u i, u j⟫ else 0) +
        (α ^ 2 / n * (1 / (n : ℝ) - 2)) * ⟪u i, u j⟫ := by
    by_cases h : i = j <;> simp [lyapA, h, inner_add_right, real_inner_smul_right]
  have hA : blockBil (lyapA α) u u =
      3 * (n : ℝ) * α ^ 2 * (∑ i, ‖u i‖ ^ 2) +
        (α ^ 2 / n * (1 / (n : ℝ) - 2)) * ‖∑ i, u i‖ ^ 2 := by
    simp only [blockBil, hij, sum_add_distrib, sum_ite_eq', sum_ite_eq, mem_univ,
      if_true, real_inner_self_eq_norm_sq]
    simp_rw [← mul_sum, ← inner_sum, ← sum_inner, real_inner_self_eq_norm_sq]
  have hB : colBil (lyapB α) u w =
      -(α * (1 - 1 / (n : ℝ))) * ⟪∑ i, u i, w⟫ := by
    simp only [colBil, lyapB, ContinuousLinearMap.smul_apply, ContinuousLinearMap.id_apply,
      real_inner_smul_right, ← mul_sum, ← sum_inner]
  rw [quadForm, hA, hB]
  simp only [ContinuousLinearMap.id_apply, real_inner_self_eq_norm_sq]
  ring

lemma lower_bound {p n : ℕ} (hn : 0 < n) (α : ℝ)
    (u : Fin n → EuclideanSpace ℝ (Fin p)) (w : EuclideanSpace ℝ (Fin p)) :
    (1 / 3) * ‖w‖ ^ 2 ≤
      quadForm (lyapA α) (lyapB α) (ContinuousLinearMap.id ℝ _) u w := by
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hr0 : 0 ≤ 1 / (n : ℝ) := by positivity
  have hr1 : 1 / (n : ℝ) ≤ 1 := (div_le_one hn0).2 hn1
  have hr2 : (1 / (n : ℝ)) ^ 2 ≤ 1 / (n : ℝ) := by nlinarith
  have hsum : ‖∑ i, u i‖ ^ 2 ≤ (n : ℝ) * ∑ i, ‖u i‖ ^ 2 := by
    calc
      ‖∑ i, u i‖ ^ 2 ≤ (∑ i, ‖u i‖) ^ 2 := by
        exact pow_le_pow_left₀ (norm_nonneg _) (norm_sum_le _ _) 2
      _ ≤ (n : ℝ) * ∑ i, ‖u i‖ ^ 2 := by
        simpa using (sq_sum_le_card_mul_sum_sq (s := univ) (f := fun i => ‖u i‖))
  have hc : 0 ≤ 3 + (1 / (n : ℝ)) * (1 / (n : ℝ) - 2) -
      (3 / 2 : ℝ) * (1 - 1 / (n : ℝ)) ^ 2 := by nlinarith
  have hc' := mul_nonneg (mul_nonneg (sq_nonneg α) hc) (sq_nonneg ‖∑ i, u i‖)
  have hs' := mul_le_mul_of_nonneg_left hsum (by positivity : 0 ≤ 3 * α ^ 2)
  have hsq := sq_nonneg ‖w - ((3 / 2 : ℝ) * α * (1 - 1 / (n : ℝ))) • ∑ i, u i‖
  rw [norm_sub_sq_real] at hsq
  simp only [real_inner_smul_right, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs] at hsq
  rw [real_inner_comm (∑ i, u i) w] at hsq
  rw [expand]
  simp only [div_eq_mul_inv] at hc' hs' hsq ⊢
  nlinarith

end D24SAGDomination

theorem solution {p n : ℕ} (hn : 0 < n)
    (f' : Fin n → EuclideanSpace ℝ (Fin p) → EuclideanSpace ℝ (Fin p))
    (xstar : EuclideanSpace ℝ (Fin p)) (α : ℝ) (hα : 0 < α)
    (θ : (Fin n → EuclideanSpace ℝ (Fin p)) × EuclideanSpace ℝ (Fin p)) :
    (1 / 3) * ‖θ.2 - xstar‖ ^ 2 ≤ lyapunov f' α xstar θ := by
  exact D24SAGDomination.lower_bound hn α (fun i => θ.1 i - f' i xstar) (θ.2 - xstar)

#print axioms solution
