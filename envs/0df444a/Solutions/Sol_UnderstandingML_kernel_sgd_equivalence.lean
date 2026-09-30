-- Prove2me | solution 1 for UnderstandingML.kernel_sgd_equivalence
-- status  : ACCEPTED   (prove)
-- author  : @Gabewhigham
-- created : 2026-09-25T18:56:24.07497+00:00
-- url     : https://prove2.me/submissions/9d3c6777-8b7c-4445-b743-961c8889eeeb

import Definitions.Def_UnderstandingML_Kernel

open MeasureTheory
open scoped InnerProductSpace

universe u

open UnderstandingML

theorem solution {X : Type u} {F : Type*} [NormedAddCommGroup F]
    [InnerProductSpace ℝ F] [CompleteSpace F] {m : ℕ} (ψ : X → F) (K : X → X → ℝ)
    (hK : ∀ a b, K a b = ⟪ψ a, ψ b⟫_ℝ) (x : Fin m → X) (y : Fin m → ℝ) (lam : ℝ)
    (idx : ℕ → Fin m) :
    (∀ t, svmSgdTheta ψ x y lam idx t = ∑ j, kernelSgdBeta K x y lam idx t j • ψ (x j)) ∧
    ∀ T, svmSgdAverage ψ x y lam idx T =
      ∑ j, kernelSgdAlphaBar K x y lam idx T j • ψ (x j) := by
  have htheta : ∀ t, svmSgdTheta ψ x y lam idx t =
      ∑ j, kernelSgdBeta K x y lam idx t j • ψ (x j) := by
    intro t
    induction t with
    | zero => simp [svmSgdTheta, kernelSgdBeta]
    | succ t ih =>
      -- the two tests agree
      have htest : y (idx t) * ⟪(1 / (lam * (t + 1))) • svmSgdTheta ψ x y lam idx t,
            ψ (x (idx t))⟫_ℝ =
          y (idx t) * ∑ j, (1 / (lam * (t + 1))) * kernelSgdBeta K x y lam idx t j *
            K (x j) (x (idx t)) := by
        rw [ih, real_inner_smul_left, sum_inner, Finset.mul_sum]
        congr 1
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [real_inner_smul_left, hK]
        ring
      simp only [svmSgdTheta, kernelSgdBeta]
      rw [htest]
      split_ifs with h
      · rw [ih]
        have : ∀ j, Function.update (kernelSgdBeta K x y lam idx t) (idx t)
              (kernelSgdBeta K x y lam idx t (idx t) + y (idx t)) j =
            kernelSgdBeta K x y lam idx t j + if j = idx t then y (idx t) else 0 := by
          intro j
          by_cases hj : j = idx t
          · subst hj; simp
          · simp [hj]
        simp only [this, add_smul, Finset.sum_add_distrib, ite_smul, zero_smul,
          Finset.sum_ite_eq', Finset.mem_univ, if_true]
      · exact ih
  refine ⟨htheta, fun T => ?_⟩
  simp only [svmSgdAverage, kernelSgdAlphaBar, htheta, Pi.smul_apply, Finset.sum_apply,
    smul_eq_mul, Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Finset.mul_sum, Finset.sum_smul]
