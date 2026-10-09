-- Prove2me | solution 1 for TroppMatrixConcentration.ch7_block_intrinsic
-- status  : ACCEPTED   (prove)
-- author  : @tc
-- created : 2026-10-09T01:32:35.767343+00:00
-- url     : https://prove2.me/submissions/d09cadf0-7773-4f98-90f1-ec38f7692b7a

import Definitions.Def_TroppMatrixConcentration_ch7_intrinsic
import Mathlib.Data.Matrix.ColumnRowPartitioned
import Mathlib.LinearAlgebra.Matrix.PosDef

open MeasureTheory ProbabilityTheory
open scoped Matrix.Norms.L2Operator ComplexOrder

namespace TroppMatrixConcentration.Ch7BlockIntrinsic

open Matrix

variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]

/-- Compression by an isometry does not increase the L2 operator norm. -/
lemma ch7bi_norm_compress_le {k : Type*} [Fintype k] [DecidableEq k]
    (E : Matrix k m ℂ) (hE : Eᴴ * E = 1) (M : Matrix k k ℂ) :
    ‖Eᴴ * M * E‖ ≤ ‖M‖ := by
  have hE1 : ‖E‖ ≤ 1 := by
    have h1 : ‖(1 : Matrix m m ℂ)‖ ≤ 1 := by
      rw [← diagonal_one, l2_opNorm_diagonal]
      exact (pi_norm_le_iff_of_nonneg zero_le_one).mpr fun _ => by simp
    have h2 : ‖E‖ * ‖E‖ ≤ 1 := by
      rw [← l2_opNorm_conjTranspose_mul_self, hE]; exact h1
    nlinarith [norm_nonneg E]
  calc ‖Eᴴ * M * E‖ ≤ ‖Eᴴ * M‖ * ‖E‖ := l2_opNorm_mul _ _
    _ ≤ ‖Eᴴ‖ * ‖M‖ * ‖E‖ := by gcongr; exact l2_opNorm_mul _ _
    _ ≤ 1 * ‖M‖ * 1 := by
      rw [l2_opNorm_conjTranspose]; gcongr
    _ = ‖M‖ := by ring

/-- The L2 operator norm of a block-diagonal matrix is the max of the block norms. -/
lemma ch7bi_norm_fromBlocks_diag (P : Matrix m m ℂ) (Q : Matrix n n ℂ) :
    ‖fromBlocks P 0 0 Q‖ = max ‖P‖ ‖Q‖ := by
  apply le_antisymm
  · rw [cstar_norm_def]
    set c := max ‖P‖ ‖Q‖
    refine ContinuousLinearMap.opNorm_le_bound _ (le_max_of_le_left (norm_nonneg _)) fun x => ?_
    let x₁ : EuclideanSpace ℂ m := WithLp.toLp 2 (fun i => x (Sum.inl i))
    let x₂ : EuclideanSpace ℂ n := WithLp.toLp 2 (fun i => x (Sum.inr i))
    have h1 := l2_opNorm_mulVec P x₁
    have h2 := l2_opNorm_mulVec Q x₂
    have hx : ‖x‖ ^ 2 = ‖x₁‖ ^ 2 + ‖x₂‖ ^ 2 := by
      simp [EuclideanSpace.norm_sq_eq, Fintype.sum_sum_type, x₁, x₂]
    have hT : ‖toEuclideanCLM (n := m ⊕ n) (𝕜 := ℂ) (fromBlocks P 0 0 Q) x‖ ^ 2 =
        ‖(EuclideanSpace.equiv m ℂ).symm (P *ᵥ x₁)‖ ^ 2 +
          ‖(EuclideanSpace.equiv n ℂ).symm (Q *ᵥ x₂)‖ ^ 2 := by
      rw [EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq]
      simp [fromBlocks_mulVec, Fintype.sum_sum_type, x₁, x₂, Function.comp_def]
    have hP : ‖P‖ ≤ c := le_max_left _ _
    have hQ : ‖Q‖ ≤ c := le_max_right _ _
    refine (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp ?_
    rw [hT, mul_pow, hx, mul_add]
    gcongr
    · calc _ ≤ (‖P‖ * ‖x₁‖) ^ 2 := by gcongr
        _ ≤ _ := by rw [mul_pow]; gcongr
    · calc _ ≤ (‖Q‖ * ‖x₂‖) ^ 2 := by gcongr
        _ ≤ _ := by rw [mul_pow]; gcongr
  · apply max_le
    · have h := ch7bi_norm_compress_le (fromRows (1 : Matrix m m ℂ) (0 : Matrix n m ℂ))
        (by ext i j; simp [mul_apply, Fintype.sum_sum_type, one_apply, eq_comm])
        (fromBlocks P 0 0 Q)
      have heq : P = (fromRows (1 : Matrix m m ℂ) (0 : Matrix n m ℂ))ᴴ * fromBlocks P 0 0 Q *
          (fromRows (1 : Matrix m m ℂ) (0 : Matrix n m ℂ)) := by
        ext i j; simp [mul_apply, Fintype.sum_sum_type, one_apply]
      exact (congrArg norm heq).trans_le h
    · have h := ch7bi_norm_compress_le (fromRows (0 : Matrix m n ℂ) (1 : Matrix n n ℂ))
        (by ext i j; simp [mul_apply, Fintype.sum_sum_type, one_apply, eq_comm])
        (fromBlocks P 0 0 Q)
      have heq : Q = (fromRows (0 : Matrix m n ℂ) (1 : Matrix n n ℂ))ᴴ * fromBlocks P 0 0 Q *
          (fromRows (0 : Matrix m n ℂ) (1 : Matrix n n ℂ)) := by
        ext i j; simp [mul_apply, Fintype.sum_sum_type, one_apply]
      exact (congrArg norm heq).trans_le h

omit [DecidableEq m] [DecidableEq n] in
/-- A block-diagonal matrix with PSD blocks is PSD. -/
lemma ch7bi_posSemidef_fromBlocks_diag {P : Matrix m m ℂ} {Q : Matrix n n ℂ}
    (hP : P.PosSemidef) (hQ : Q.PosSemidef) : (fromBlocks P 0 0 Q).PosSemidef := by
  refine PosSemidef.of_dotProduct_mulVec_nonneg
    (IsHermitian.fromBlocks hP.1 (by simp) hQ.1) fun x => ?_
  have e : star x ⬝ᵥ (fromBlocks P 0 0 Q *ᵥ x) =
      star (x ∘ Sum.inl) ⬝ᵥ (P *ᵥ (x ∘ Sum.inl)) +
        star (x ∘ Sum.inr) ⬝ᵥ (Q *ᵥ (x ∘ Sum.inr)) := by
    rw [fromBlocks_mulVec]
    simp [dotProduct, Fintype.sum_sum_type]
  rw [e]
  exact add_nonneg (hP.dotProduct_mulVec_nonneg _) (hQ.dotProduct_mulVec_nonneg _)

omit [DecidableEq m] [DecidableEq n] in
lemma ch7bi_trace_fromBlocks_diag (P : Matrix m m ℂ) (Q : Matrix n n ℂ) :
    trace (fromBlocks P 0 0 Q) = trace P + trace Q := by
  simp [trace, Fintype.sum_sum_type]

omit [DecidableEq m] in
/-- For PSD `A`, the real part of the trace is nonnegative. -/
lemma ch7bi_trace_re_nonneg {A : Matrix m m ℂ} (hA : A.PosSemidef) : 0 ≤ (trace A).re :=
  (Complex.nonneg_iff.mp hA.trace_nonneg).1

/-- The scalar inequalities behind the block bounds. -/
lemma ch7bi_scalar {t₁ t₂ n₁ n₂ : ℝ} (ht₁ : 0 ≤ t₁) (ht₂ : 0 ≤ t₂) (hn₁ : 0 ≤ n₁) (hn₂ : 0 ≤ n₂)
    (h₁ : n₁ = 0 → t₁ = 0) (h₂ : n₂ = 0 → t₂ = 0) :
    min (t₁ / n₁) (t₂ / n₂) ≤ (t₁ + t₂) / max n₁ n₂ ∧
      (t₁ + t₂) / max n₁ n₂ ≤ t₁ / n₁ + t₂ / n₂ := by
  rcases hn₁.eq_or_lt with e₁ | p₁
  · subst e₁
    have := h₁ rfl; subst this
    rw [max_eq_right hn₂]; simp
  rcases hn₂.eq_or_lt with e₂ | p₂
  · subst e₂
    have := h₂ rfl; subst this
    rw [max_eq_left hn₁]; simp
  rcases le_total n₂ n₁ with h | h
  · rw [max_eq_left h, add_div]
    refine ⟨?_, ?_⟩
    · exact (min_le_left _ _).trans (le_add_of_nonneg_right (div_nonneg ht₂ hn₁))
    · gcongr
  · rw [max_eq_right h, add_div]
    refine ⟨?_, ?_⟩
    · exact (min_le_right _ _).trans (le_add_of_nonneg_left (div_nonneg ht₁ hn₂))
    · gcongr

end TroppMatrixConcentration.Ch7BlockIntrinsic

open TroppMatrixConcentration TroppMatrixConcentration.Ch7BlockIntrinsic

theorem solution {m n : ℕ} [NeZero m] [NeZero n]
    (V₁ : Matrix (Fin m) (Fin m) ℂ) (V₂ : Matrix (Fin n) (Fin n) ℂ)
    (hV₁ : V₁.PosSemidef) (hV₂ : V₂.PosSemidef) :
    let V := Matrix.fromBlocks V₁ 0 0 V₂
    V.PosSemidef ∧
    spectralNorm V = max (spectralNorm V₁) (spectralNorm V₂) ∧
    intrinsicDimension V =
      ((Matrix.trace V₁).re + (Matrix.trace V₂).re) /
        max (spectralNorm V₁) (spectralNorm V₂) ∧
    min (intrinsicDimension V₁) (intrinsicDimension V₂) ≤ intrinsicDimension V ∧
    intrinsicDimension V ≤ intrinsicDimension V₁ + intrinsicDimension V₂ := by
  intro V
  have hnorm : spectralNorm V = max (spectralNorm V₁) (spectralNorm V₂) :=
    ch7bi_norm_fromBlocks_diag V₁ V₂
  have hdim : intrinsicDimension V =
      ((Matrix.trace V₁).re + (Matrix.trace V₂).re) /
        max (spectralNorm V₁) (spectralNorm V₂) := by
    unfold intrinsicDimension
    rw [hnorm, show V = Matrix.fromBlocks V₁ 0 0 V₂ from rfl, ch7bi_trace_fromBlocks_diag,
      Complex.add_re]
  have hz : ∀ {k : ℕ} (A : Matrix (Fin k) (Fin k) ℂ), spectralNorm A = 0 →
      (Matrix.trace A).re = 0 := by
    intro k A h
    have : A = 0 := norm_eq_zero.mp h
    simp [this]
  have hs := ch7bi_scalar (ch7bi_trace_re_nonneg hV₁) (ch7bi_trace_re_nonneg hV₂)
    (norm_nonneg V₁) (norm_nonneg V₂) (hz V₁) (hz V₂)
  refine ⟨ch7bi_posSemidef_fromBlocks_diag hV₁ hV₂, hnorm, hdim, ?_, ?_⟩
  · rw [hdim]; exact hs.1
  · rw [hdim]; exact hs.2
