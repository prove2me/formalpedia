-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Gap48.P33.classicalized_output_loss
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-22T22:47:41.893049+00:00
-- url     : https://prove2.me/submissions/e3a7ddbf-1115-4931-b66a-6519c533cd7a

import Definitions.Def_QAlgorithms_Papers_Independent_Gap48_P33



open Polynomial

namespace X6G41D

variable {n : Type*} [Fintype n] [DecidableEq n]

lemma spec_sub (d : n → ℝ) : spectrum ℝ (Matrix.diagonal (fun i => (d i : ℂ))) ⊆ Set.range d := by
  intro μ hμ
  by_contra hc
  rw [spectrum.mem_iff] at hμ
  apply hμ
  have e : (μ • 1 : Matrix n n ℂ) = Matrix.diagonal (fun _ => (μ : ℂ)) := by
    ext i j
    by_cases h : i = j
    · subst h; simp [Complex.real_smul]
    · simp [Matrix.one_apply, h]
  rw [Algebra.algebraMap_eq_smul_one, e, Matrix.diagonal_sub,
    Matrix.isUnit_diagonal, Pi.isUnit_iff]
  intro i
  simp only [isUnit_iff_ne_zero, ne_eq, sub_eq_zero]
  intro h
  apply hc
  refine ⟨i, ?_⟩
  have := congrArg Complex.re h
  simpa using this.symm

lemma aeval_diag (d : n → ℝ) (P : ℝ[X]) :
    aeval (Matrix.diagonal (fun i => (d i : ℂ))) P =
      Matrix.diagonal (fun i => ((P.eval (d i) : ℝ) : ℂ)) := by
  induction P using Polynomial.induction_on' with
  | add p q hp hq => simp [hp, hq, Matrix.diagonal_add]
  | monomial k a =>
    rw [aeval_monomial, Matrix.diagonal_pow, Algebra.algebraMap_eq_smul_one, smul_one_mul,
      ← Matrix.diagonal_smul]
    congr 1; funext i
    simp only [eval_monomial, Pi.smul_apply, Pi.pow_apply, Complex.real_smul]
    push_cast; ring

lemma cfc_diag (d : n → ℝ) (f : ℝ → ℝ) :
    cfc f (Matrix.diagonal (fun i => (d i : ℂ))) = Matrix.diagonal (fun i => ((f (d i) : ℝ) : ℂ)) := by
  classical
  set S := Finset.univ.image d
  set P := Lagrange.interpolate S id f
  have hP : ∀ i, P.eval (d i) = f (d i) := by
    intro i
    have := Lagrange.eval_interpolate_at_node (s := S) (v := id) (r := f)
      (Set.injOn_id _) (Finset.mem_image_of_mem d (Finset.mem_univ i))
    rwa [id] at this
  have hsa : IsSelfAdjoint (Matrix.diagonal (fun i => (d i : ℂ))) := by
    rw [IsSelfAdjoint, Matrix.star_eq_conjTranspose, Matrix.diagonal_conjTranspose]
    congr 1; funext i; simp
  rw [cfc_congr (g := fun t => P.eval t), cfc_polynomial P _ hsa, aeval_diag]
  · congr 1; funext i; rw [hP]
  · intro t ht
    obtain ⟨i, rfl⟩ := spec_sub d ht
    exact (hP i).symm

end X6G41D

namespace X6P33C
open QAlgorithms QAlgorithms.Papers.Independent.Gap48.P33
open QAlgorithms.Papers.Independent.Information100.P27 (shannon)
open QAlgorithms.Papers.Independent.Dependency50.P19 (mutualInformation)
open Real

theorem vn_diag {ι : Type*} [Fintype ι] [DecidableEq ι] (f : ι → ℝ) :
    vnEntropy (Matrix.diagonal fun i => (f i : ℂ)) = ∑ i, negMulLog (f i) / log 2 := by
  unfold vnEntropy
  rw [X6G41D.cfc_diag, Matrix.trace_diagonal, Complex.re_sum, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [Complex.ofReal_re, Real.logb, negMulLog]
  ring

theorem shannon_eq {Y : Type} [Fintype Y] (q : Y → ℝ) :
    shannon q = ∑ i, negMulLog (q i) / log 2 := by
  unfold shannon
  rw [← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [Real.logb, negMulLog]
  ring

theorem h2_eq (x : ℝ) : binEntropy2 x = (negMulLog x + negMulLog (1 - x)) / log 2 := by
  rw [binEntropy2, binEntropy_eq_negMulLog_add_negMulLog_one_sub]

theorem output_eq (p q : ℝ) (hq : 0 ≤ q) (hq1 : q ≤ 1) :
    classicalOutput p q = Matrix.diagonal (fun rq =>
      (((if rq.1 = rq.2 then 2 * p / 3 else 1 - 2 * p / 3) *
        (if rq.1 then q else 1 - q) : ℝ) : ℂ)) := by
  have h1 : ((Real.sqrt q : ℂ)) * (starRingEnd ℂ) (Real.sqrt q : ℂ) = (q : ℂ) := by
    rw [Complex.conj_ofReal, ← Complex.ofReal_mul, Real.mul_self_sqrt hq]
  have h2 : ((Real.sqrt (1 - q) : ℂ)) * (starRingEnd ℂ) (Real.sqrt (1 - q) : ℂ) = ((1 - q : ℝ) : ℂ) := by
    rw [Complex.conj_ofReal, ← Complex.ofReal_mul, Real.mul_self_sqrt (by linarith)]
  have s1 : ((Real.sqrt q : ℂ)) ^ 2 = (q : ℂ) := by
    rw [← Complex.ofReal_pow, Real.sq_sqrt hq]
  have s2 : ((Real.sqrt (1 - q) : ℂ)) ^ 2 = 1 - (q : ℂ) := by
    rw [← Complex.ofReal_pow, Real.sq_sqrt (by linarith)]; push_cast; ring
  ext ⟨a, b⟩ ⟨c, d⟩
  cases a <;> cases b <;> cases c <;> cases d <;>
    simp [classicalOutput, idTensorSuperop, pauliDepolarizing, classicalInput, pureDensity, qBasis,
      pauliX, pauliY, pauliZ, Matrix.mul_apply, Matrix.diagonal] <;>
    ring_nf <;> simp only [s1, s2, Complex.I_sq] <;> ring

theorem tl_diag {α β : Type*} [Fintype α] [DecidableEq α] [DecidableEq β] (f : α × β → ℝ) :
    traceLeft (Matrix.diagonal fun i => (f i : ℂ)) =
      Matrix.diagonal fun b => ((∑ a, f (a, b) : ℝ) : ℂ) := by
  ext b b'
  by_cases h : b = b'
  · subst h; simp [traceLeft, Matrix.diagonal]
  · simp [traceLeft, Matrix.diagonal, h]

theorem tr_diag {α β : Type*} [Fintype β] [DecidableEq α] [DecidableEq β] (f : α × β → ℝ) :
    traceRight (Matrix.diagonal fun i => (f i : ℂ)) =
      Matrix.diagonal fun a => ((∑ b, f (a, b) : ℝ) : ℂ) := by
  ext a a'
  by_cases h : a = a'
  · subst h; simp [traceRight, Matrix.diagonal]
  · simp [traceRight, Matrix.diagonal, h]

theorem vn_out (p q : ℝ) (hq : 0 ≤ q) (hq1 : q ≤ 1) :
    vnEntropy (classicalOutput p q) = shannon (classicalSpectrum p q) := by
  rw [output_eq p q hq hq1, vn_diag, shannon_eq, Fintype.sum_prod_type, Fin.sum_univ_four]
  simp [Fintype.sum_bool, classicalSpectrum]
  ring_nf

theorem vn_tl (p q : ℝ) (hq : 0 ≤ q) (hq1 : q ≤ 1) :
    vnEntropy (traceLeft (classicalOutput p q)) = binEntropy2 (q + (2 * p / 3) * (1 - 2 * q)) := by
  rw [output_eq p q hq hq1, tl_diag, vn_diag, h2_eq]
  simp [Fintype.sum_bool]
  ring_nf

theorem vn_tr (p q : ℝ) (hq : 0 ≤ q) (hq1 : q ≤ 1) :
    vnEntropy (traceRight (classicalOutput p q)) = binEntropy2 q := by
  rw [output_eq p q hq hq1, tr_diag, vn_diag, h2_eq]
  simp [Fintype.sum_bool]
  ring_nf

theorem shannon_spec (p q : ℝ) :
    shannon (classicalSpectrum p q) = binEntropy2 q + binEntropy2 (2 * p / 3) := by
  rw [shannon_eq, Fin.sum_univ_four, h2_eq, h2_eq]
  simp only [classicalSpectrum]
  simp
  have e1 : 2 * p * (1 - q) / 3 = (1 - q) * (2 * p / 3) := by ring
  have e2 : 2 * p * q / 3 = q * (2 * p / 3) := by ring
  have e3 : (1 - 2 * p / 3) * (1 - q) = (1 - q) * (1 - 2 * p / 3) := by ring
  have e4 : (1 - 2 * p / 3) * q = q * (1 - 2 * p / 3) := by ring
  rw [e1, e2, e3, e4]
  simp only [negMulLog_mul]
  ring

theorem mi_eq (p q : ℝ) (hq : 0 ≤ q) (hq1 : q ≤ 1) :
    mutualInformation (classicalOutput p q) =
      binEntropy2 (q + (2 * p / 3) * (1 - 2 * q)) - binEntropy2 (2 * p / 3) := by
  unfold mutualInformation
  rw [vn_tr p q hq hq1, vn_tl p q hq hq1, vn_out p q hq hq1, shannon_spec]
  ring

theorem h2_le_one (x : ℝ) : binEntropy2 x ≤ 1 := by
  rw [binEntropy2, div_le_one (Real.log_pos (by norm_num))]
  exact binEntropy_le_log_two

theorem h2_half : binEntropy2 (1 / 2) = 1 := by
  rw [binEntropy2, show (1 / 2 : ℝ) = 2⁻¹ by norm_num, Real.binEntropy_two_inv,
    div_self (Real.log_pos (by norm_num)).ne']

theorem output_loss (p q : ℝ) (hq : 0 ≤ q) (hq1 : q ≤ 1) :
    classicalOutput p q = Matrix.diagonal (fun rq =>
      (((if rq.1 = rq.2 then 2 * p / 3 else 1 - 2 * p / 3) *
        (if rq.1 then q else 1 - q) : ℝ) : ℂ)) ∧
    measuredLoss p q = shannon (classicalSpectrum p q) -
      binEntropy2 (q + (2 * p / 3) * (1 - 2 * q)) ∧
    mutualInformation (classicalOutput p q) = binEntropy2 q - measuredLoss p q := by
  refine ⟨output_eq p q hq hq1, ?_, ?_⟩
  · unfold measuredLoss; rw [vn_out p q hq hq1, vn_tl p q hq hq1]
  · unfold measuredLoss mutualInformation; rw [vn_tr p q hq hq1]; ring

theorem capacity (p : ℝ) :
    IsGreatest {z : ℝ | ∃ q : ℝ, 0 ≤ q ∧ q ≤ 1 ∧ z = mutualInformation (classicalOutput p q)}
      (1 - binEntropy2 (2 * p / 3)) ∧
    mutualInformation (classicalOutput p (1 / 2)) = 1 - binEntropy2 (2 * p / 3) := by
  have half : mutualInformation (classicalOutput p (1 / 2)) = 1 - binEntropy2 (2 * p / 3) := by
    rw [mi_eq p (1 / 2) (by norm_num) (by norm_num)]
    norm_num [h2_half]
  refine ⟨⟨⟨1 / 2, by norm_num, by norm_num, half.symm⟩, ?_⟩, half⟩
  rintro z ⟨q, hq, hq1, rfl⟩
  rw [mi_eq p q hq hq1]
  linarith [h2_le_one (q + (2 * p / 3) * (1 - 2 * q))]

end X6P33C

open QAlgorithms QAlgorithms.Papers.Independent.Gap48.P33
open QAlgorithms.Papers.Independent.Information100.P27 (shannon)
open QAlgorithms.Papers.Independent.Dependency50.P19 (mutualInformation)

theorem solution (p q : ℝ)
    (hp : 0 ≤ p) (hp1 : p ≤ 1) (hq : 0 ≤ q) (hq1 : q ≤ 1) :
    classicalOutput p q = Matrix.diagonal (fun rq =>
      (((if rq.1 = rq.2 then 2 * p / 3 else 1 - 2 * p / 3) *
        (if rq.1 then q else 1 - q) : ℝ) : ℂ)) ∧
    measuredLoss p q = shannon (classicalSpectrum p q) -
      binEntropy2 (q + (2 * p / 3) * (1 - 2 * q)) ∧
    mutualInformation (classicalOutput p q) = binEntropy2 q - measuredLoss p q :=
  X6P33C.output_loss p q hq hq1
