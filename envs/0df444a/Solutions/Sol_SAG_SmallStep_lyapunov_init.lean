-- Prove2me | solution 1 for SAG.SmallStep.lyapunov_init
-- status  : ACCEPTED   (prove)
-- author  : @涼宮 ハルヒ
-- created : 2026-10-24T03:39:25.487647+00:00
-- url     : https://prove2.me/submissions/e7caa48d-e36a-40be-a2b8-4bd4ea8b5576

import Definitions.Def_SAG_SmallStep_lyapunov
import Definitions.Def_SAGA_Convex_finiteSum
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.Calculus.FDeriv.Add
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

open Finset SAG.SmallStep InnerProductSpace
open scoped RealInnerProductSpace

namespace D24SAGInit

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

lemma gradients_sum_zero {p n : ℕ} (hn : 0 < n)
    (f : Fin n → EuclideanSpace ℝ (Fin p) → ℝ)
    (f' : Fin n → EuclideanSpace ℝ (Fin p) → EuclideanSpace ℝ (Fin p))
    (xstar : EuclideanSpace ℝ (Fin p))
    (hgrad : ∀ i x, HasGradientAt (f i) (f' i x) x)
    (hmin : ∀ x, SAGA.Convex.fAvg f xstar ≤ SAGA.Convex.fAvg f x) :
    ∑ i, f' i xstar = 0 := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hminSum : ∀ x, (∑ i, f i xstar) ≤ ∑ i, f i x := by
    intro x
    have h := hmin x
    unfold SAGA.Convex.fAvg at h
    exact (mul_le_mul_iff_right₀ (by positivity : 0 < 1 / (n : ℝ))).1 h
  have hd : HasFDerivAt (fun x => ∑ i, f i x)
      (∑ i, toDual ℝ (EuclideanSpace ℝ (Fin p)) (f' i xstar)) xstar :=
    HasFDerivAt.fun_sum fun i _ => (hgrad i xstar).hasFDerivAt
  have hlocal : IsLocalMin (fun x => ∑ i, f i x) xstar :=
    Filter.Eventually.of_forall hminSum
  have hz := hlocal.hasFDerivAt_eq_zero hd
  apply (toDual ℝ (EuclideanSpace ℝ (Fin p))).injective
  simpa only [map_sum, map_zero] using hz

end D24SAGInit

theorem solution {p n : ℕ} (hn : 0 < n)
    (f : Fin n → EuclideanSpace ℝ (Fin p) → ℝ)
    (f' : Fin n → EuclideanSpace ℝ (Fin p) → EuclideanSpace ℝ (Fin p)) (L : ℝ) (hL : 0 < L)
    (hgrad : ∀ i x, HasGradientAt (f i) (f' i x) x)
    (xstar : EuclideanSpace ℝ (Fin p))
    (hmin : ∀ x, SAGA.Convex.fAvg f xstar ≤ SAGA.Convex.fAvg f x)
    (x0 : EuclideanSpace ℝ (Fin p)) :
    lyapunov f' (1 / (2 * (n : ℝ) * L)) xstar (fun _ => 0, x0)
      = 3 * ((1 / (n : ℝ)) * ∑ i, ‖f' i xstar‖ ^ 2) / (4 * L ^ 2) + ‖x0 - xstar‖ ^ 2 := by
  have hsum := D24SAGInit.gradients_sum_zero hn f f' xstar hgrad hmin
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn)
  unfold lyapunov
  rw [D24SAGInit.expand]
  simp only [zero_sub, sum_neg_distrib, hsum, neg_zero, norm_zero, norm_neg, zero_pow, inner_zero_left,
    ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, mul_zero, sub_zero, add_zero]
  field_simp [hn0, ne_of_gt hL]
  <;> ring

#print axioms solution
