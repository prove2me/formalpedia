-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Dependency50.P26.completePOVM_givesTester
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-20T00:49:09.735511+00:00
-- url     : https://prove2.me/submissions/b1a90eca-7352-4a3a-8c98-69473887ab34

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P26

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder

open QAlgorithms

attribute [local instance] Classical.decEq Classical.propDecidable

open QAlgorithms.Papers QAlgorithms.Papers.Independent QAlgorithms.Papers.Independent.Dependency50 QAlgorithms.Papers.Independent.Dependency50.P26

theorem g52b_trace_traceLeft {α β : Type*} [Fintype α] [Fintype β]
    (R : Matrix (α × β) (α × β) ℂ) : (traceLeft R).trace = R.trace := by
  simp only [Matrix.trace, Matrix.diag, traceLeft, Matrix.of_apply, Fintype.sum_prod_type]
  exact Finset.sum_comm

theorem g52b_trace_norm (s : Signature) : ∀ (n : ℕ) (R : Matrix (Basis s n) (Basis s n) ℂ),
    Normalized s n R → R.trace = (inputDimension s n : ℂ)
  | 0, R, h => by
      have h' : R = 1 := h
      subst h'
      rw [Matrix.trace_one]
      simp only [inputDimension, Finset.range_zero, Finset.prod_empty, Nat.cast_one]
      show ((Fintype.card Unit : ℕ) : ℂ) = 1
      simp
  | n + 1, R, h => by
      obtain ⟨-, Q, hQ, hT⟩ := h
      have e : R.trace = (traceLeft R).trace :=
        (g52b_trace_traceLeft (α := Fin (s.output n)) (β := Fin (s.input n) × Basis s n) R).symm
      rw [e, hT, show Matrix.kronecker (1 : Matrix (Fin (s.input n)) (Fin (s.input n)) ℂ) Q =
        Matrix.kroneckerMap (· * ·) 1 Q from rfl, Matrix.trace_kronecker, Matrix.trace_one, g52b_trace_norm s n Q hQ]
      simp [inputDimension, Finset.prod_range_succ, mul_comm]

theorem g52b_tr_nonneg {ι : Type*} [Fintype ι] (A B : Matrix ι ι ℂ) (hA : A.PosSemidef)
    (hB : B.PosSemidef) : 0 ≤ (A * B).trace.re := by
  obtain ⟨m, v, rfl⟩ := Matrix.posSemidef_iff_eq_sum_vecMulVec.mp hA
  rw [Finset.sum_mul, Matrix.trace_sum, Complex.re_sum]
  refine Finset.sum_nonneg fun i _ => ?_
  have : (Matrix.vecMulVec (v i) (star (v i)) * B).trace = star (v i) ⬝ᵥ (B *ᵥ v i) := by
    simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.vecMulVec_apply, dotProduct,
      Matrix.mulVec, Finset.mul_sum, Pi.star_apply]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => by ring
  rw [this]
  exact (Complex.nonneg_iff.mp (hB.dotProduct_mulVec_nonneg _)).1

/-- PDF pp.19–20, Theorem 13: scale an arbitrary informationally complete POVM by the
product of input dimensions (odd source labels there are zero-based even labels here). -/
theorem solution (s : Signature) (n k : ℕ) (hn : 0 < n)
    (E : Fin k → Matrix (Basis s n) (Basis s n) ℂ)
    (hE : POVM E) (hic : InformationallyComplete E) :
    let P := fun i => (((inputDimension s n : ℕ) : ℂ)⁻¹) • E i
    CombTester s n k P ∧ InformationallyComplete P := by
  intro P
  obtain ⟨hk, hEpsd, hEsum⟩ := hE
  have hdn : 0 < inputDimension s n := by
    unfold inputDimension
    exact Finset.prod_pos fun j _ => s.input_pos j
  have hdC : ((inputDimension s n : ℕ) : ℂ) ≠ 0 := by exact_mod_cast hdn.ne'
  have hc : (0:ℂ) ≤ ((inputDimension s n : ℕ) : ℂ)⁻¹ := by
    have : ((inputDimension s n : ℕ) : ℂ)⁻¹ = (((inputDimension s n : ℝ)⁻¹ : ℝ) : ℂ) := by
      push_cast; rfl
    rw [this]
    exact Complex.zero_le_real.mpr (by positivity)
  have hPpsd : ∀ i, (P i).PosSemidef := fun i => (hEpsd i).smul hc
  refine ⟨⟨hn, hk, hPpsd, fun R hR => ⟨fun i => ?_, ?_⟩⟩, fun X => ?_⟩
  · have hRpsd : R.PosSemidef := by
      obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn.ne'
      exact hR.1
    exact g52b_tr_nonneg _ _ (hPpsd i).transpose hRpsd
  · have hsum : ∑ i, (P i).transpose * R = ((inputDimension s n : ℕ) : ℂ)⁻¹ • R := by
      calc ∑ i, (P i).transpose * R
          = ∑ i, ((inputDimension s n : ℕ) : ℂ)⁻¹ • ((E i).transpose * R) := by
            simp [P, Matrix.transpose_smul, Matrix.smul_mul]
        _ = ((inputDimension s n : ℕ) : ℂ)⁻¹ • ((∑ i, E i).transpose * R) := by
            rw [← Finset.smul_sum, ← Finset.sum_mul, Matrix.transpose_sum]
        _ = ((inputDimension s n : ℕ) : ℂ)⁻¹ • R := by
            rw [hEsum, Matrix.transpose_one, Matrix.one_mul]
    simp only [QAlgorithms.effectProb]
    rw [← Complex.re_sum, ← Matrix.trace_sum, hsum, Matrix.trace_smul,
      g52b_trace_norm s n R hR, smul_eq_mul, inv_mul_cancel₀ hdC, Complex.one_re]
  · obtain ⟨c, hcX⟩ := hic X
    refine ⟨fun i => ((inputDimension s n : ℕ) : ℂ) * c i, ?_⟩
    rw [hcX]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [P, Matrix.transpose_smul, smul_smul]
    congr 1
    field_simp


end

