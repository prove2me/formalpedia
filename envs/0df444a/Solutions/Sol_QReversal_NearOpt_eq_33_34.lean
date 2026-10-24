-- Prove2me | solution 1 for QReversal.NearOpt.eq_33_34
-- status  : ACCEPTED   (prove)
-- author  : @xwh
-- created : 2026-10-23T10:12:41.953104+00:00
-- url     : https://prove2.me/submissions/59bcac60-6aca-41e2-81c0-510857d49d69

import Mathlib
import Definitions.Def_PeresTerno_kraus_basics
import Definitions.Def_QReversal_NearOpt_Setting

open Matrix PeresTerno
open scoped MatrixOrder ComplexOrder

noncomputable section
namespace QReversal.NearOpt.NormalizationProof

variable {n ι κ L : Type*} [Fintype n] [Fintype ι] [Fintype κ]

lemma update_posSemidef (A : ι → Matrix n n ℂ) {X : Matrix n n ℂ}
    (hX : X.PosSemidef) : (krausUpdate A X).PosSemidef := by
  exact Matrix.posSemidef_sum _ fun i _ => hX.mul_mul_conjTranspose_same (A i)

lemma update_sub (A : ι → Matrix n n ℂ) (X Y : Matrix n n ℂ) :
    krausUpdate A (X-Y) = krausUpdate A X - krausUpdate A Y := by
  simp [krausUpdate, mul_sub, sub_mul, Finset.sum_sub_distrib]

lemma update_mono (A : ι → Matrix n n ℂ) {X Y : Matrix n n ℂ} (h : X ≤ Y) :
    krausUpdate A X ≤ krausUpdate A Y := by
  rw [Matrix.le_iff] at h ⊢
  rw [← update_sub]
  exact update_posSemidef A h

lemma trace_re_mono {X Y : Matrix n n ℂ} (h : X ≤ Y) : X.trace.re ≤ Y.trace.re := by
  have hp := (Matrix.le_iff.mp h).trace_nonneg
  have hr := (Complex.nonneg_iff.mp hp).1
  simpa only [Matrix.trace_sub, Complex.sub_re, sub_nonneg] using hr

/- Reused from the inspected accepted proof 090ebed5-52f3-4f18-8273-d47470c08eb3
   (QReversal.PGMBound.theorem_5), also frozen in PGM2_Completion.lean.
   The proof applies without a positive-definiteness assumption. -/
lemma trace_psd_product_nonneg {X Z : Matrix n n ℂ}
    (hX : X.PosSemidef) (hZ : Z.PosSemidef) : 0 ≤ (X*Z).trace.re := by
  classical
  have hs : (CFC.sqrt X).PosSemidef := (CFC.sqrt_nonneg X).posSemidef
  have hp := hZ.mul_mul_conjTranspose_same (CFC.sqrt X)
  rw [hs.isHermitian.eq] at hp
  have ht := hp.trace_nonneg
  have heq : (CFC.sqrt X * Z * CFC.sqrt X).trace = (X*Z).trace := by
    rw [Matrix.trace_mul_cycle, CFC.sqrt_mul_sqrt_self X hX.nonneg]
  rw [heq] at ht
  exact (Complex.nonneg_iff.mp ht).1

lemma trace_update (A : ι → Matrix n n ℂ) (X : Matrix n n ℂ) :
    (krausUpdate A X).trace = ((∑ i, (A i)ᴴ * A i) * X).trace := by
  simp only [krausUpdate, Matrix.trace_sum, Finset.sum_mul]
  congr 1
  funext i
  rw [Matrix.trace_mul_cycle]

lemma trace_update_tp [DecidableEq n] (A : ι → Matrix n n ℂ) (hA : IsTracePreserving A)
    (X : Matrix n n ℂ) : (krausUpdate A X).trace = X.trace := by
  rw [trace_update, hA, one_mul]

lemma trace_update_tni [DecidableEq n] (A : ι → Matrix n n ℂ) (hA : IsTraceNonincreasing A)
    {X : Matrix n n ℂ} (hX : X.PosSemidef) :
    (krausUpdate A X).trace.re ≤ X.trace.re := by
  have ht := trace_psd_product_nonneg (Matrix.le_iff.mp hA) hX
  rw [sub_mul, one_mul, Matrix.trace_sub, Complex.sub_re, ← trace_update] at ht
  linarith

lemma avg_density [Fintype L] (p : L → ℝ) (X : L → Matrix n n ℂ)
    (hp : ∀ l, 0 ≤ p l) (hp1 : ∑ l, p l = 1)
    (hX : ∀ l, IsDensityMatrix (X l)) : IsDensityMatrix (avgState p X) := by
  constructor
  · apply Matrix.posSemidef_sum
    intro l _
    exact (hX l).1.smul (by exact_mod_cast hp l)
  · simp only [avgState, Matrix.trace_sum, Matrix.trace_smul, (hX _).2, smul_eq_mul, mul_one]
    exact_mod_cast hp1

lemma update_sum [Fintype L] (A : ι → Matrix n n ℂ) (X : L → Matrix n n ℂ) :
    krausUpdate A (∑ l, X l) = ∑ l, krausUpdate A (X l) := by
  simp only [krausUpdate, Finset.mul_sum, Finset.sum_mul]
  exact Finset.sum_comm

lemma update_smul (A : ι → Matrix n n ℂ) (c : ℂ) (X : Matrix n n ℂ) :
    krausUpdate A (c • X) = c • krausUpdate A X := by
  simp [krausUpdate, Finset.smul_sum]

lemma trace_update_composite (R : κ → Matrix n n ℂ) (B : ι → Matrix n n ℂ)
    (X : Matrix n n ℂ) :
    (krausUpdate R (krausUpdate B X)).trace.re =
      ∑ i, ∑ j, (R i * B j * X * (B j)ᴴ * (R i)ᴴ).trace.re := by
  simp [krausUpdate, Finset.mul_sum, Finset.sum_mul, Matrix.trace_sum, mul_assoc]

lemma trace_composite_avg [Fintype L] (R : κ → Matrix n n ℂ)
    (B : ι → Matrix n n ℂ) (p : L → ℝ) (X : L → Matrix n n ℂ) :
    (krausUpdate R (krausUpdate B (avgState p X))).trace.re =
      ∑ l, p l * (krausUpdate R (krausUpdate B (X l))).trace.re := by
  simp only [avgState, update_sum, update_smul, Matrix.trace_sum, Matrix.trace_smul,
    smul_eq_mul, Complex.re_sum, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul,
    sub_zero]

end QReversal.NearOpt.NormalizationProof

open QReversal.NearOpt QReversal.NearOpt.NormalizationProof

theorem solution {n L ι κ : Type*} [Fintype n] [DecidableEq n] [Fintype L] [Fintype ι]
    [Fintype κ]
    (A : ι → Matrix n n ℂ) (hA : IsTracePreserving A)
    (p : L → ℝ) (ρs : L → Matrix n n ℂ) (hE : IsCommutingEnsemble p ρs)
    (ρ : Matrix n n ℂ) (hρ : ρ = avgState p ρs)
    (R B : κ → Matrix n n ℂ) (hR : IsTraceNonincreasing R)
    (hBA : krausUpdate B ρ ≤ krausUpdate A ρ) :
    ∑ l, p l * ∑ i, ∑ j, (Matrix.trace (R i * B j * ρs l * (B j)ᴴ * (R i)ᴴ)).re =
        ∑ l, p l * (Matrix.trace (krausUpdate R (krausUpdate B (ρs l)))).re ∧
      ∑ l, p l * (Matrix.trace (krausUpdate R (krausUpdate B (ρs l)))).re =
        (Matrix.trace (krausUpdate R (krausUpdate B ρ))).re ∧
      (Matrix.trace (krausUpdate R (krausUpdate B ρ))).re ≤
        (Matrix.trace (krausUpdate R (krausUpdate A ρ))).re ∧
      (Matrix.trace (krausUpdate R (krausUpdate A ρ))).re ≤ 1 := by
  have hden : IsDensityMatrix ρ := hρ ▸ avg_density p ρs hE.1 hE.2.1 hE.2.2.1
  refine ⟨?_, ?_, trace_re_mono (update_mono R hBA), ?_⟩
  · simp_rw [trace_update_composite]
  · rw [hρ, trace_composite_avg]
  · calc
      _ ≤ (krausUpdate A ρ).trace.re := trace_update_tni R hR (update_posSemidef A hden.1)
      _ = 1 := by rw [trace_update_tp A hA, hden.2]; rfl
