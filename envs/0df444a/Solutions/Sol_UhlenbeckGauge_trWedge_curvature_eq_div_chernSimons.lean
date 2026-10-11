-- Prove2me | solution 1 for UhlenbeckGauge.trWedge_curvature_eq_div_chernSimons
-- status  : ACCEPTED   (prove)
-- author  : @waitingintime
-- created : 2026-10-10T17:06:25.57687+00:00
-- url     : https://prove2.me/submissions/55acbce3-c5d8-44d6-bde6-26f13e349d2a

import Definitions.Def_uhlenbeck_gauge_box_defs
open UhlenbeckGauge Matrix
set_option maxRecDepth 10000
set_option maxHeartbeats 0
set_option autoImplicit false
noncomputable section
namespace CSAlgebra
def epsilon (μ ν ρ σ : Fin 4) : ℂ :=
  if (μ = 0 ∧ ν = 1 ∧ ρ = 2 ∧ σ = 3) ∨
      (μ = 0 ∧ ν = 2 ∧ ρ = 3 ∧ σ = 1) ∨
      (μ = 0 ∧ ν = 3 ∧ ρ = 1 ∧ σ = 2) ∨
      (μ = 1 ∧ ν = 0 ∧ ρ = 3 ∧ σ = 2) ∨
      (μ = 1 ∧ ν = 2 ∧ ρ = 0 ∧ σ = 3) ∨
      (μ = 1 ∧ ν = 3 ∧ ρ = 2 ∧ σ = 0) ∨
      (μ = 2 ∧ ν = 0 ∧ ρ = 1 ∧ σ = 3) ∨
      (μ = 2 ∧ ν = 1 ∧ ρ = 3 ∧ σ = 0) ∨
      (μ = 2 ∧ ν = 3 ∧ ρ = 0 ∧ σ = 1) ∨
      (μ = 3 ∧ ν = 0 ∧ ρ = 2 ∧ σ = 1) ∨
      (μ = 3 ∧ ν = 1 ∧ ρ = 0 ∧ σ = 2) ∨
      (μ = 3 ∧ ν = 2 ∧ ρ = 1 ∧ σ = 0) then 1 else
  if (μ = 0 ∧ ν = 1 ∧ ρ = 3 ∧ σ = 2) ∨
      (μ = 0 ∧ ν = 2 ∧ ρ = 1 ∧ σ = 3) ∨
      (μ = 0 ∧ ν = 3 ∧ ρ = 2 ∧ σ = 1) ∨
      (μ = 1 ∧ ν = 0 ∧ ρ = 2 ∧ σ = 3) ∨
      (μ = 1 ∧ ν = 2 ∧ ρ = 3 ∧ σ = 0) ∨
      (μ = 1 ∧ ν = 3 ∧ ρ = 0 ∧ σ = 2) ∨
      (μ = 2 ∧ ν = 0 ∧ ρ = 3 ∧ σ = 1) ∨
      (μ = 2 ∧ ν = 1 ∧ ρ = 0 ∧ σ = 3) ∨
      (μ = 2 ∧ ν = 3 ∧ ρ = 1 ∧ σ = 0) ∨
      (μ = 3 ∧ ν = 0 ∧ ρ = 1 ∧ σ = 2) ∨
      (μ = 3 ∧ ν = 1 ∧ ρ = 2 ∧ σ = 0) ∨
      (μ = 3 ∧ ν = 2 ∧ ρ = 0 ∧ σ = 1) then -1 else 0

lemma levi_repeat01 (a b c : Fin 4) : levi a a b c = 0 := by
  unfold levi
  norm_cast
  exact Matrix.det_zero_of_row_eq (i := (0 : Fin 4)) (j := 1) (by decide) rfl

lemma levi_repeat02 (a b c : Fin 4) : levi a b a c = 0 := by
  unfold levi
  norm_cast
  exact Matrix.det_zero_of_row_eq (i := (0 : Fin 4)) (j := 2) (by decide) rfl

lemma levi_repeat03 (a b c : Fin 4) : levi a b c a = 0 := by
  unfold levi
  norm_cast
  exact Matrix.det_zero_of_row_eq (i := (0 : Fin 4)) (j := 3) (by decide) rfl

lemma levi_repeat12 (a b c : Fin 4) : levi a b b c = 0 := by
  unfold levi
  norm_cast
  exact Matrix.det_zero_of_row_eq (i := (1 : Fin 4)) (j := 2) (by decide) rfl

lemma levi_repeat13 (a b c : Fin 4) : levi a b c b = 0 := by
  unfold levi
  norm_cast
  exact Matrix.det_zero_of_row_eq (i := (1 : Fin 4)) (j := 3) (by decide) rfl

lemma levi_repeat23 (a b c : Fin 4) : levi a b c c = 0 := by
  unfold levi
  norm_cast
  exact Matrix.det_zero_of_row_eq (i := (2 : Fin 4)) (j := 3) (by decide) rfl

lemma levi_eval (μ ν ρ σ : Fin 4) : levi μ ν ρ σ = epsilon μ ν ρ σ := by
  fin_cases μ <;> fin_cases ν <;> fin_cases ρ <;> fin_cases σ <;>
    simp +decide [epsilon, levi_repeat01, levi_repeat02, levi_repeat03,
      levi_repeat12, levi_repeat13, levi_repeat23]
  all_goals unfold levi
  all_goals rw [Matrix.det_succ_row_zero]
  all_goals norm_num [Matrix.det_fin_three, Fin.sum_univ_four,
    Matrix.of_apply, Pi.single_apply, Matrix.submatrix_apply, Matrix.cons_val]
  all_goals dsimp
  all_goals simp +decide
  all_goals norm_num

lemma rotate3 {n : ℕ} (a b c : Mat n) :
    trace (a * (b * c)) = trace (b * (c * a)) := by
  rw [trace_mul_comm a (b * c), Matrix.mul_assoc]
lemma rotate4 {n : ℕ} (a b c d : Mat n) :
    trace (a * (b * (c * d))) = trace (b * (c * (d * a))) := by
  rw [trace_mul_comm a (b * (c * d)), Matrix.mul_assoc, Matrix.mul_assoc]
lemma identity {n : ℕ} (a : Fin 4 → Mat n) (p : Fin 4 → Fin 4 → Mat n)
    (q : Fin 4 → Fin 4 → Fin 4 → Mat n)
    (hq : ∀ μ ρ σ, q μ ρ σ = q ρ μ σ) :
    (1 / 4 : ℂ) * ∑ μ, ∑ ν, ∑ ρ, ∑ σ, levi μ ν ρ σ *
      trace ((p μ ν - p ν μ + (a μ * a ν - a ν * a μ)) *
        (p ρ σ - p σ ρ + (a ρ * a σ - a σ * a ρ))) =
    ∑ μ, ∑ ν, ∑ ρ, ∑ σ, levi μ ν ρ σ *
      (trace (p μ ν * p ρ σ + a ν * q μ ρ σ) +
        (2 / 3 : ℂ) * trace
          (p μ ν * a ρ * a σ + a ν * p μ ρ * a σ + a ν * a ρ * p μ σ)) := by
  have t0 : trace (a 0 * (a 1 * p 2 3)) = trace (p 2 3 * (a 0 * a 1)) := by
    rw [rotate3, rotate3]
  have t1 : trace (a 0 * (a 1 * p 3 2)) = trace (p 3 2 * (a 0 * a 1)) := by
    rw [rotate3, rotate3]
  have t2 : trace (a 0 * (a 2 * p 1 3)) = trace (p 1 3 * (a 0 * a 2)) := by
    rw [rotate3, rotate3]
  have t3 : trace (a 0 * (a 2 * p 3 1)) = trace (p 3 1 * (a 0 * a 2)) := by
    rw [rotate3, rotate3]
  have t4 : trace (a 0 * (a 3 * p 1 2)) = trace (p 1 2 * (a 0 * a 3)) := by
    rw [rotate3, rotate3]
  have t5 : trace (a 0 * (a 3 * p 2 1)) = trace (p 2 1 * (a 0 * a 3)) := by
    rw [rotate3, rotate3]
  have t6 : trace (a 0 * (p 1 2 * a 3)) = trace (p 1 2 * (a 3 * a 0)) := by
    rw [rotate3]
  have t7 : trace (a 0 * (p 1 3 * a 2)) = trace (p 1 3 * (a 2 * a 0)) := by
    rw [rotate3]
  have t8 : trace (a 0 * (p 2 1 * a 3)) = trace (p 2 1 * (a 3 * a 0)) := by
    rw [rotate3]
  have t9 : trace (a 0 * (p 2 3 * a 1)) = trace (p 2 3 * (a 1 * a 0)) := by
    rw [rotate3]
  have t10 : trace (a 0 * (p 3 1 * a 2)) = trace (p 3 1 * (a 2 * a 0)) := by
    rw [rotate3]
  have t11 : trace (a 0 * (p 3 2 * a 1)) = trace (p 3 2 * (a 1 * a 0)) := by
    rw [rotate3]
  have t12 : trace (a 1 * (a 0 * (a 2 * a 3))) = trace (a 0 * (a 2 * (a 3 * a 1))) := by
    rw [rotate4]
  have t13 : trace (a 1 * (a 0 * (a 3 * a 2))) = trace (a 0 * (a 3 * (a 2 * a 1))) := by
    rw [rotate4]
  have t14 : trace (a 1 * (a 0 * p 2 3)) = trace (p 2 3 * (a 1 * a 0)) := by
    rw [rotate3, rotate3]
  have t15 : trace (a 1 * (a 0 * p 3 2)) = trace (p 3 2 * (a 1 * a 0)) := by
    rw [rotate3, rotate3]
  have t16 : trace (a 1 * (a 2 * (a 0 * a 3))) = trace (a 0 * (a 3 * (a 1 * a 2))) := by
    rw [rotate4, rotate4]
  have t17 : trace (a 1 * (a 2 * (a 3 * a 0))) = trace (a 0 * (a 1 * (a 2 * a 3))) := by
    rw [rotate4, rotate4, rotate4]
  have t18 : trace (a 1 * (a 2 * p 0 3)) = trace (p 0 3 * (a 1 * a 2)) := by
    rw [rotate3, rotate3]
  have t19 : trace (a 1 * (a 2 * p 3 0)) = trace (p 3 0 * (a 1 * a 2)) := by
    rw [rotate3, rotate3]
  have t20 : trace (a 1 * (a 3 * (a 0 * a 2))) = trace (a 0 * (a 2 * (a 1 * a 3))) := by
    rw [rotate4, rotate4]
  have t21 : trace (a 1 * (a 3 * (a 2 * a 0))) = trace (a 0 * (a 1 * (a 3 * a 2))) := by
    rw [rotate4, rotate4, rotate4]
  have t22 : trace (a 1 * (a 3 * p 0 2)) = trace (p 0 2 * (a 1 * a 3)) := by
    rw [rotate3, rotate3]
  have t23 : trace (a 1 * (a 3 * p 2 0)) = trace (p 2 0 * (a 1 * a 3)) := by
    rw [rotate3, rotate3]
  have t24 : trace (a 1 * (p 0 2 * a 3)) = trace (p 0 2 * (a 3 * a 1)) := by
    rw [rotate3]
  have t25 : trace (a 1 * (p 0 3 * a 2)) = trace (p 0 3 * (a 2 * a 1)) := by
    rw [rotate3]
  have t26 : trace (a 1 * (p 2 0 * a 3)) = trace (p 2 0 * (a 3 * a 1)) := by
    rw [rotate3]
  have t27 : trace (a 1 * (p 2 3 * a 0)) = trace (p 2 3 * (a 0 * a 1)) := by
    rw [rotate3]
  have t28 : trace (a 1 * (p 3 0 * a 2)) = trace (p 3 0 * (a 2 * a 1)) := by
    rw [rotate3]
  have t29 : trace (a 1 * (p 3 2 * a 0)) = trace (p 3 2 * (a 0 * a 1)) := by
    rw [rotate3]
  have t30 : trace (a 2 * (a 0 * (a 1 * a 3))) = trace (a 0 * (a 1 * (a 3 * a 2))) := by
    rw [rotate4]
  have t31 : trace (a 2 * (a 0 * (a 3 * a 1))) = trace (a 0 * (a 3 * (a 1 * a 2))) := by
    rw [rotate4]
  have t32 : trace (a 2 * (a 0 * p 1 3)) = trace (p 1 3 * (a 2 * a 0)) := by
    rw [rotate3, rotate3]
  have t33 : trace (a 2 * (a 0 * p 3 1)) = trace (p 3 1 * (a 2 * a 0)) := by
    rw [rotate3, rotate3]
  have t34 : trace (a 2 * (a 1 * (a 0 * a 3))) = trace (a 0 * (a 3 * (a 2 * a 1))) := by
    rw [rotate4, rotate4]
  have t35 : trace (a 2 * (a 1 * (a 3 * a 0))) = trace (a 0 * (a 2 * (a 1 * a 3))) := by
    rw [rotate4, rotate4, rotate4]
  have t36 : trace (a 2 * (a 1 * p 0 3)) = trace (p 0 3 * (a 2 * a 1)) := by
    rw [rotate3, rotate3]
  have t37 : trace (a 2 * (a 1 * p 3 0)) = trace (p 3 0 * (a 2 * a 1)) := by
    rw [rotate3, rotate3]
  have t38 : trace (a 2 * (a 3 * (a 0 * a 1))) = trace (a 0 * (a 1 * (a 2 * a 3))) := by
    rw [rotate4, rotate4]
  have t39 : trace (a 2 * (a 3 * (a 1 * a 0))) = trace (a 0 * (a 2 * (a 3 * a 1))) := by
    rw [rotate4, rotate4, rotate4]
  have t40 : trace (a 2 * (a 3 * p 0 1)) = trace (p 0 1 * (a 2 * a 3)) := by
    rw [rotate3, rotate3]
  have t41 : trace (a 2 * (a 3 * p 1 0)) = trace (p 1 0 * (a 2 * a 3)) := by
    rw [rotate3, rotate3]
  have t42 : trace (a 2 * (p 0 1 * a 3)) = trace (p 0 1 * (a 3 * a 2)) := by
    rw [rotate3]
  have t43 : trace (a 2 * (p 0 3 * a 1)) = trace (p 0 3 * (a 1 * a 2)) := by
    rw [rotate3]
  have t44 : trace (a 2 * (p 1 0 * a 3)) = trace (p 1 0 * (a 3 * a 2)) := by
    rw [rotate3]
  have t45 : trace (a 2 * (p 1 3 * a 0)) = trace (p 1 3 * (a 0 * a 2)) := by
    rw [rotate3]
  have t46 : trace (a 2 * (p 3 0 * a 1)) = trace (p 3 0 * (a 1 * a 2)) := by
    rw [rotate3]
  have t47 : trace (a 2 * (p 3 1 * a 0)) = trace (p 3 1 * (a 0 * a 2)) := by
    rw [rotate3]
  have t48 : trace (a 3 * (a 0 * (a 1 * a 2))) = trace (a 0 * (a 1 * (a 2 * a 3))) := by
    rw [rotate4]
  have t49 : trace (a 3 * (a 0 * (a 2 * a 1))) = trace (a 0 * (a 2 * (a 1 * a 3))) := by
    rw [rotate4]
  have t50 : trace (a 3 * (a 0 * p 1 2)) = trace (p 1 2 * (a 3 * a 0)) := by
    rw [rotate3, rotate3]
  have t51 : trace (a 3 * (a 0 * p 2 1)) = trace (p 2 1 * (a 3 * a 0)) := by
    rw [rotate3, rotate3]
  have t52 : trace (a 3 * (a 1 * (a 0 * a 2))) = trace (a 0 * (a 2 * (a 3 * a 1))) := by
    rw [rotate4, rotate4]
  have t53 : trace (a 3 * (a 1 * (a 2 * a 0))) = trace (a 0 * (a 3 * (a 1 * a 2))) := by
    rw [rotate4, rotate4, rotate4]
  have t54 : trace (a 3 * (a 1 * p 0 2)) = trace (p 0 2 * (a 3 * a 1)) := by
    rw [rotate3, rotate3]
  have t55 : trace (a 3 * (a 1 * p 2 0)) = trace (p 2 0 * (a 3 * a 1)) := by
    rw [rotate3, rotate3]
  have t56 : trace (a 3 * (a 2 * (a 0 * a 1))) = trace (a 0 * (a 1 * (a 3 * a 2))) := by
    rw [rotate4, rotate4]
  have t57 : trace (a 3 * (a 2 * (a 1 * a 0))) = trace (a 0 * (a 3 * (a 2 * a 1))) := by
    rw [rotate4, rotate4, rotate4]
  have t58 : trace (a 3 * (a 2 * p 0 1)) = trace (p 0 1 * (a 3 * a 2)) := by
    rw [rotate3, rotate3]
  have t59 : trace (a 3 * (a 2 * p 1 0)) = trace (p 1 0 * (a 3 * a 2)) := by
    rw [rotate3, rotate3]
  have t60 : trace (a 3 * (p 0 1 * a 2)) = trace (p 0 1 * (a 2 * a 3)) := by
    rw [rotate3]
  have t61 : trace (a 3 * (p 0 2 * a 1)) = trace (p 0 2 * (a 1 * a 3)) := by
    rw [rotate3]
  have t62 : trace (a 3 * (p 1 0 * a 2)) = trace (p 1 0 * (a 2 * a 3)) := by
    rw [rotate3]
  have t63 : trace (a 3 * (p 1 2 * a 0)) = trace (p 1 2 * (a 0 * a 3)) := by
    rw [rotate3]
  have t64 : trace (a 3 * (p 2 0 * a 1)) = trace (p 2 0 * (a 1 * a 3)) := by
    rw [rotate3]
  have t65 : trace (a 3 * (p 2 1 * a 0)) = trace (p 2 1 * (a 0 * a 3)) := by
    rw [rotate3]
  have t66 : trace (p 1 2 * p 0 3) = trace (p 0 3 * p 1 2) := by
    exact trace_mul_comm _ _
  have t67 : trace (p 1 3 * p 0 2) = trace (p 0 2 * p 1 3) := by
    exact trace_mul_comm _ _
  have t68 : trace (p 2 0 * p 1 3) = trace (p 1 3 * p 2 0) := by
    exact trace_mul_comm _ _
  have t69 : trace (p 2 1 * p 0 3) = trace (p 0 3 * p 2 1) := by
    exact trace_mul_comm _ _
  have t70 : trace (p 2 3 * p 0 1) = trace (p 0 1 * p 2 3) := by
    exact trace_mul_comm _ _
  have t71 : trace (p 2 3 * p 1 0) = trace (p 1 0 * p 2 3) := by
    exact trace_mul_comm _ _
  have t72 : trace (p 3 0 * p 1 2) = trace (p 1 2 * p 3 0) := by
    exact trace_mul_comm _ _
  have t73 : trace (p 3 0 * p 2 1) = trace (p 2 1 * p 3 0) := by
    exact trace_mul_comm _ _
  have t74 : trace (p 3 1 * p 0 2) = trace (p 0 2 * p 3 1) := by
    exact trace_mul_comm _ _
  have t75 : trace (p 3 1 * p 2 0) = trace (p 2 0 * p 3 1) := by
    exact trace_mul_comm _ _
  have t76 : trace (p 3 2 * p 0 1) = trace (p 0 1 * p 3 2) := by
    exact trace_mul_comm _ _
  have t77 : trace (p 3 2 * p 1 0) = trace (p 1 0 * p 3 2) := by
    exact trace_mul_comm _ _
  simp +decide only [Fin.sum_univ_four, levi_eval, epsilon, Fin.reduceFinMk,
    Nat.reduceAdd, Nat.reduceSub, Nat.reduceMul, Fin.isValue,
    decide_true, decide_false, ite_true, ite_false,
    zero_mul, one_mul, neg_mul, neg_neg, zero_add, add_zero]
  simp only [Matrix.add_mul, Matrix.mul_add, Matrix.sub_mul, Matrix.mul_sub,
    trace_add, trace_sub, Matrix.mul_assoc]
  simp only [t0, t1, t2, t3, t4, t5, t6, t7, t8, t9, t10, t11, t12, t13, t14, t15, t16, t17, t18, t19, t20, t21, t22, t23, t24, t25, t26, t27, t28, t29, t30, t31, t32, t33, t34, t35, t36, t37, t38, t39, t40, t41, t42, t43, t44, t45, t46, t47, t48, t49, t50, t51, t52, t53, t54, t55, t56, t57, t58, t59, t60, t61, t62, t63, t64, t65, t66, t67, t68, t69, t70, t71, t72, t73, t74, t75, t76, t77]
  rw [hq 1 0 2, hq 1 0 3, hq 2 0 1, hq 2 0 3, hq 2 1 0, hq 2 1 3, hq 3 0 1, hq 3 0 2, hq 3 1 0, hq 3 1 2, hq 3 2 0, hq 3 2 1]
  ring
end CSAlgebra

open UhlenbeckGauge Matrix
open scoped ContDiff
set_option autoImplicit false
set_option maxHeartbeats 0
noncomputable section
private def D (μ : Fin 4) (f : R4 → ℂ) (x : R4) : ℂ :=
  fderiv ℝ f x (Pi.single μ 1)
private abbrev Smooth {n : ℕ} (f : R4 → Mat n) :=
  ∀ i j, ContDiff ℝ ∞ (fun x => f x i j)
private lemma Dsum {ι : Type} [Fintype ι] (μ : Fin 4) (f : ι → R4 → ℂ)
    (hf : ∀ i, ContDiff ℝ ∞ (f i)) (x : R4) :
    D μ (fun y => ∑ i, f i y) x = ∑ i, D μ (f i) x := by
  unfold D
  rw [fderiv_fun_sum (fun i _ => (hf i).differentiable (by simp) x)]
  simp
private lemma Dmul (μ : Fin 4) (f g : R4 → ℂ)
    (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g) (x : R4) :
    D μ (fun y => f y * g y) x = D μ f x * g x + f x * D μ g x := by
  unfold D
  rw [fderiv_fun_mul (hf.differentiable (by simp) x) (hg.differentiable (by simp) x)]
  simp only [_root_.add_apply, _root_.smul_apply, smul_eq_mul]
  ring
private lemma Dadd (μ : Fin 4) (f g : R4 → ℂ)
    (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g) (x : R4) :
    D μ (fun y => f y + g y) x = D μ f x + D μ g x := by
  unfold D
  rw [fderiv_fun_add (hf.differentiable (by simp) x) (hg.differentiable (by simp) x)]
  rfl
private lemma Dconstmul (μ : Fin 4) (c : ℂ) (f : R4 → ℂ)
    (hf : ContDiff ℝ ∞ f) (x : R4) :
    D μ (fun y => c * f y) x = c * D μ f x := by
  unfold D
  rw [fderiv_const_mul (hf.differentiable (by simp) x)]
  rfl
private lemma smooth_pd {n : ℕ} (μ : Fin 4) (f : R4 → Mat n) (hf : Smooth f) :
    Smooth (partialDeriv μ f) := by
  intro i j
  exact ((hf i j).fderiv_right (by simp)).clm_apply contDiff_const
private lemma smooth_mul {n : ℕ} (f g : R4 → Mat n) (hf : Smooth f) (hg : Smooth g) :
    Smooth (fun y => f y * g y) := by
  intro i j
  change ContDiff ℝ ∞ (fun x => ∑ k, f x i k * g x k j)
  exact ContDiff.sum (fun k _ => (hf i k).mul (hg k j))
private lemma smooth_trace {n : ℕ} (f : R4 → Mat n) (hf : Smooth f) :
    ContDiff ℝ ∞ (fun y => trace (f y)) := by
  exact ContDiff.sum (fun i _ => hf i i)
private lemma pd_mul {n : ℕ} (μ : Fin 4) (f g : R4 → Mat n)
    (hf : Smooth f) (hg : Smooth g) (x : R4) :
    partialDeriv μ (fun y => f y * g y) x =
      partialDeriv μ f x * g x + f x * partialDeriv μ g x := by
  ext i j
  change D μ (fun y => ∑ k, f y i k * g y k j) x = _
  rw [Dsum μ _ (fun k => (hf i k).mul (hg k j))]
  simp only [Dmul μ _ _ (hf i _) (hg _ j), Matrix.add_apply, Matrix.mul_apply,
    partialDeriv, Matrix.of_apply, Finset.sum_add_distrib]
  rfl
private lemma Dtrace {n : ℕ} (μ : Fin 4) (f : R4 → Mat n) (hf : Smooth f) (x : R4) :
    D μ (fun y => trace (f y)) x = trace (partialDeriv μ f x) := by
  exact Dsum μ (fun i y => f y i i) (fun i => hf i i) x
private lemma Dcomm (μ ρ : Fin 4) (f : R4 → ℂ) (hf : ContDiff ℝ ∞ f) (x : R4) :
    D μ (D ρ f) x = D ρ (D μ f) x := by
  have hd : ContDiff ℝ ∞ (fderiv ℝ f) := hf.fderiv_right (by simp)
  unfold D
  rw [fderiv_clm_apply (hd.differentiable (by simp) x) (differentiableAt_const _),
    fderiv_clm_apply (hd.differentiable (by simp) x) (differentiableAt_const _)]
  simp only [fderiv_const_apply, ContinuousLinearMap.comp_zero, zero_add,
    ContinuousLinearMap.flip_apply]
  have h2 : ContDiff ℝ 2 f :=
    hf.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)
  exact h2.contDiffAt.isSymmSndFDerivAt (by simp) _ _
private lemma pd_comm {n : ℕ} (μ ρ : Fin 4) (f : R4 → Mat n) (hf : Smooth f) (x : R4) :
    partialDeriv μ (partialDeriv ρ f) x = partialDeriv ρ (partialDeriv μ f) x := by
  ext i j
  exact Dcomm μ ρ (fun y => f y i j) (hf i j) x
private lemma Dtrace_mul {n : ℕ} (μ : Fin 4) (f g : R4 → Mat n)
    (hf : Smooth f) (hg : Smooth g) (x : R4) :
    D μ (fun y => trace (f y * g y)) x =
      trace (partialDeriv μ f x * g x + f x * partialDeriv μ g x) := by
  rw [Dtrace μ _ (smooth_mul f g hf hg), pd_mul μ f g hf hg]
private lemma Dtrace_triple {n : ℕ} (μ : Fin 4) (f g h : R4 → Mat n)
    (hf : Smooth f) (hg : Smooth g) (hh : Smooth h) (x : R4) :
    D μ (fun y => trace (f y * g y * h y)) x =
      trace (partialDeriv μ f x * g x * h x +
        f x * partialDeriv μ g x * h x + f x * g x * partialDeriv μ h x) := by
  rw [Dtrace_mul μ _ h (smooth_mul f g hf hg) hh, pd_mul μ f g hf hg]
  rw [Matrix.add_mul]
private def integrand {n : ℕ} (A : Connection n) (ν ρ σ : Fin 4) (y : R4) : ℂ :=
    trace (A y ν * partialDeriv ρ (fun z => A z σ) y) +
      (2 / 3 : ℂ) * trace (A y ν * A y ρ * A y σ)
private lemma integrand_smooth {n : ℕ} (A : Connection n) (hA : IsSUConnection A)
    (ν ρ σ : Fin 4) : ContDiff ℝ ∞ (integrand A ν ρ σ) := by
  exact (smooth_trace _ (smooth_mul _ _ (hA.1 ν)
    (smooth_pd ρ _ (hA.1 σ)))).add
    (contDiff_const.mul (smooth_trace _
      (smooth_mul _ _ (smooth_mul _ _ (hA.1 ν) (hA.1 ρ)) (hA.1 σ))))
private lemma D_integrand {n : ℕ} (A : Connection n) (hA : IsSUConnection A)
    (μ ν ρ σ : Fin 4) (x : R4) :
    D μ (integrand A ν ρ σ) x =
      trace (partialDeriv μ (fun y => A y ν) x * partialDeriv ρ (fun y => A y σ) x +
        A x ν * partialDeriv μ (partialDeriv ρ (fun y => A y σ)) x) +
      (2 / 3 : ℂ) * trace
        (partialDeriv μ (fun y => A y ν) x * A x ρ * A x σ +
          A x ν * partialDeriv μ (fun y => A y ρ) x * A x σ +
          A x ν * A x ρ * partialDeriv μ (fun y => A y σ) x) := by
  unfold integrand
  rw [Dadd μ _ _
    (smooth_trace _ (smooth_mul _ _ (hA.1 ν) (smooth_pd ρ _ (hA.1 σ))))
    (contDiff_const.mul (smooth_trace _
      (smooth_mul _ _ (smooth_mul _ _ (hA.1 ν) (hA.1 ρ)) (hA.1 σ)))),
    Dconstmul μ _ _ (smooth_trace _
      (smooth_mul _ _ (smooth_mul _ _ (hA.1 ν) (hA.1 ρ)) (hA.1 σ))),
    Dtrace_mul μ _ _ (hA.1 ν) (smooth_pd ρ _ (hA.1 σ)),
    Dtrace_triple μ _ _ _ (hA.1 ν) (hA.1 ρ) (hA.1 σ)]
private lemma D_current {n : ℕ} (A : Connection n) (hA : IsSUConnection A)
    (μ : Fin 4) (x : R4) :
    D μ (chernSimonsCurrent A μ) x =
      ∑ ν, ∑ ρ, ∑ σ, levi μ ν ρ σ *
        (trace (partialDeriv μ (fun y => A y ν) x * partialDeriv ρ (fun y => A y σ) x +
          A x ν * partialDeriv μ (partialDeriv ρ (fun y => A y σ)) x) +
          (2 / 3 : ℂ) * trace
            (partialDeriv μ (fun y => A y ν) x * A x ρ * A x σ +
              A x ν * partialDeriv μ (fun y => A y ρ) x * A x σ +
              A x ν * A x ρ * partialDeriv μ (fun y => A y σ) x)) := by
  have hK : chernSimonsCurrent A μ =
      fun y => ∑ ν, ∑ ρ, ∑ σ, levi μ ν ρ σ * integrand A ν ρ σ y := by
    funext y
    simp only [chernSimonsCurrent, integrand, trace_add, trace_smul, smul_eq_mul]
  rw [hK]
  rw [Dsum μ _ (fun ν => ContDiff.sum (fun ρ _ =>
    ContDiff.sum (fun σ _ => contDiff_const.mul (integrand_smooth A hA ν ρ σ))))]
  congr 1; funext ν
  rw [Dsum μ _ (fun ρ => ContDiff.sum (fun σ _ =>
    contDiff_const.mul (integrand_smooth A hA ν ρ σ)))]
  congr 1; funext ρ
  rw [Dsum μ _ (fun σ => contDiff_const.mul (integrand_smooth A hA ν ρ σ))]
  congr 1; funext σ
  rw [Dconstmul μ _ _ (integrand_smooth A hA ν ρ σ), D_integrand A hA]

/-- The local Chern–Simons identity, with the platform's standard normalization. -/
theorem solution {n : ℕ} (A : Connection n) (hA : IsSUConnection A) (x : R4) :
    trWedge (curvature A x) =
      ∑ μ : Fin 4, fderiv ℝ (chernSimonsCurrent A μ) x (Pi.single μ 1) := by
  change trWedge (curvature A x) = ∑ μ : Fin 4, D μ (chernSimonsCurrent A μ) x
  simp_rw [D_current A hA]
  exact CSAlgebra.identity (A x)
    (fun μ ν => partialDeriv μ (fun y => A y ν) x)
    (fun μ ρ σ => partialDeriv μ (partialDeriv ρ (fun y => A y σ)) x)
    (fun μ ρ σ => pd_comm μ ρ (fun y => A y σ) (hA.1 σ) x)

