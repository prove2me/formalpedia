-- Prove2me | solution 1 for UhlenbeckGauge.norm_add_hodgeStar_sq
-- status  : ACCEPTED   (prove)
-- author  : @waitingintime
-- created : 2026-10-10T15:59:25.20649+00:00
-- url     : https://prove2.me/submissions/a5c077a4-ece3-47f2-925e-2f3ebcecdb68

import Definitions.Def_uhlenbeck_gauge_box_defs
open UhlenbeckGauge Matrix
set_option maxRecDepth 10000
set_option maxHeartbeats 0
noncomputable section
private def epsilon (μ ν ρ σ : Fin 4) : ℂ :=
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

private lemma levi_repeat01 (a b c : Fin 4) : levi a a b c = 0 := by
  unfold levi
  norm_cast
  exact Matrix.det_zero_of_row_eq (i := (0 : Fin 4)) (j := 1) (by decide) rfl

private lemma levi_repeat02 (a b c : Fin 4) : levi a b a c = 0 := by
  unfold levi
  norm_cast
  exact Matrix.det_zero_of_row_eq (i := (0 : Fin 4)) (j := 2) (by decide) rfl

private lemma levi_repeat03 (a b c : Fin 4) : levi a b c a = 0 := by
  unfold levi
  norm_cast
  exact Matrix.det_zero_of_row_eq (i := (0 : Fin 4)) (j := 3) (by decide) rfl

private lemma levi_repeat12 (a b c : Fin 4) : levi a b b c = 0 := by
  unfold levi
  norm_cast
  exact Matrix.det_zero_of_row_eq (i := (1 : Fin 4)) (j := 2) (by decide) rfl

private lemma levi_repeat13 (a b c : Fin 4) : levi a b c b = 0 := by
  unfold levi
  norm_cast
  exact Matrix.det_zero_of_row_eq (i := (1 : Fin 4)) (j := 3) (by decide) rfl

private lemma levi_repeat23 (a b c : Fin 4) : levi a b c c = 0 := by
  unfold levi
  norm_cast
  exact Matrix.det_zero_of_row_eq (i := (2 : Fin 4)) (j := 3) (by decide) rfl

private lemma levi_eval (μ ν ρ σ : Fin 4) : levi μ ν ρ σ = epsilon μ ν ρ σ := by
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
private lemma hodge_01 {n : ℕ} (F : TwoForm n) (hF : IsAntisymm F) :
    hodgeStar F 0 1 = F 2 3 := by
  simp +decide [hodgeStar, Fin.sum_univ_four, levi_eval, epsilon]
  rw [hF 2 3]
  ext i j
  simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.neg_apply, smul_eq_mul]
  ring

private lemma hodge_02 {n : ℕ} (F : TwoForm n) (hF : IsAntisymm F) :
    hodgeStar F 0 2 = -F 1 3 := by
  simp +decide [hodgeStar, Fin.sum_univ_four, levi_eval, epsilon]
  rw [hF 1 3]
  ext i j
  simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.neg_apply, smul_eq_mul]
  ring

private lemma hodge_03 {n : ℕ} (F : TwoForm n) (hF : IsAntisymm F) :
    hodgeStar F 0 3 = F 1 2 := by
  simp +decide [hodgeStar, Fin.sum_univ_four, levi_eval, epsilon]
  rw [hF 1 2]
  ext i j
  simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.neg_apply, smul_eq_mul]
  ring

private lemma hodge_12 {n : ℕ} (F : TwoForm n) (hF : IsAntisymm F) :
    hodgeStar F 1 2 = F 0 3 := by
  simp +decide [hodgeStar, Fin.sum_univ_four, levi_eval, epsilon]
  rw [hF 0 3]
  ext i j
  simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.neg_apply, smul_eq_mul]
  ring

private lemma hodge_13 {n : ℕ} (F : TwoForm n) (hF : IsAntisymm F) :
    hodgeStar F 1 3 = -F 0 2 := by
  simp +decide [hodgeStar, Fin.sum_univ_four, levi_eval, epsilon]
  rw [hF 0 2]
  ext i j
  simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.neg_apply, smul_eq_mul]
  ring

private lemma hodge_23 {n : ℕ} (F : TwoForm n) (hF : IsAntisymm F) :
    hodgeStar F 2 3 = F 0 1 := by
  simp +decide [hodgeStar, Fin.sum_univ_four, levi_eval, epsilon]
  rw [hF 0 1]
  ext i j
  simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.neg_apply, smul_eq_mul]
  ring

private lemma trace_norm_cast {n : ℕ} (A : Mat n) :
    ((trace (A * Aᴴ)).re : ℂ) = trace (A * Aᴴ) := by
  have h : star (trace (A * Aᴴ)) = trace (A * Aᴴ) := by
    rw [← trace_conjTranspose, conjTranspose_mul, conjTranspose_conjTranspose]
  apply Complex.ext
  · simp
  · have := congrArg Complex.im h
    simp only [Complex.star_def, Complex.conj_im] at this
    simp only [Complex.ofReal_im]
    linarith

private lemma normSq_six {n : ℕ} (F : TwoForm n) :
    normSq F = (trace (F 0 1 * (F 0 1)ᴴ)).re +
      (trace (F 0 2 * (F 0 2)ᴴ)).re + (trace (F 0 3 * (F 0 3)ᴴ)).re +
      (trace (F 1 2 * (F 1 2)ᴴ)).re + (trace (F 1 3 * (F 1 3)ᴴ)).re +
      (trace (F 2 3 * (F 2 3)ᴴ)).re := by
  simp [normSq, Fin.sum_univ_four, add_assoc]

private lemma normSq_cast_six {n : ℕ} (F : TwoForm n) :
    (normSq F : ℂ) = trace (F 0 1 * (F 0 1)ᴴ) +
      trace (F 0 2 * (F 0 2)ᴴ) + trace (F 0 3 * (F 0 3)ᴴ) +
      trace (F 1 2 * (F 1 2)ᴴ) + trace (F 1 3 * (F 1 3)ᴴ) +
      trace (F 2 3 * (F 2 3)ᴴ) := by
  rw [normSq_six]
  push_cast
  rw [trace_norm_cast, trace_norm_cast, trace_norm_cast, trace_norm_cast,
    trace_norm_cast, trace_norm_cast]

private lemma trWedge_six {n : ℕ} (F : TwoForm n) (hF : IsAntisymm F) :
    trWedge F = 2 * (trace (F 0 1 * F 2 3) - trace (F 0 2 * F 1 3) +
      trace (F 0 3 * F 1 2)) := by
  simp +decide [trWedge, Fin.sum_univ_four, levi_eval, epsilon]
  rw [hF 0 1, hF 0 2, hF 0 3, hF 1 2, hF 1 3, hF 2 3]
  simp only [mul_neg, neg_mul, trace_neg]
  rw [trace_mul_comm (F 2 3) (F 0 1), trace_mul_comm (F 1 3) (F 0 2),
    trace_mul_comm (F 1 2) (F 0 3)]
  ring

theorem solution {n : ℕ} (F : TwoForm n) (hF : IsAntisymm F)
    (hsu : IsSuNValued F) :
    ((normSq (F + hodgeStar F) : ℝ) : ℂ) = 2 * (normSq F : ℂ) - 2 * trWedge F ∧
    ((normSq (F - hodgeStar F) : ℝ) : ℂ) = 2 * (normSq F : ℂ) + 2 * trWedge F := by
  constructor <;>
    rw [normSq_cast_six, normSq_cast_six, trWedge_six F hF] <;>
    simp only [Pi.add_apply, Pi.sub_apply, hodge_01 F hF, hodge_02 F hF,
      hodge_03 F hF, hodge_12 F hF, hodge_13 F hF, hodge_23 F hF,
      conjTranspose_add, conjTranspose_sub, conjTranspose_neg,
      (hsu 0 1).1, (hsu 0 2).1, (hsu 0 3).1,
      (hsu 1 2).1, (hsu 1 3).1, (hsu 2 3).1,
      add_mul, mul_add, sub_mul, mul_sub, neg_mul, mul_neg, neg_neg,
      trace_add, trace_sub, trace_neg] <;>
    rw [trace_mul_comm (F 2 3) (F 0 1), trace_mul_comm (F 1 3) (F 0 2),
      trace_mul_comm (F 1 2) (F 0 3)] <;> ring

