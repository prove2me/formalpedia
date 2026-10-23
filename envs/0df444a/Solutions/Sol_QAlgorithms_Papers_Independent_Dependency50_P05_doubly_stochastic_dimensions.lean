-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Dependency50.P05.doubly_stochastic_dimensions
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-22T06:00:45.433301+00:00
-- url     : https://prove2.me/submissions/adc62661-6984-45b2-b8c7-4ab628a8d5e7

import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P05
noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder

namespace X6P05

open QAlgorithms.Papers.Independent.Dependency50.P05

lemma trace_eq_trace_traceRight {α β : Type*} [Fintype α] [Fintype β]
    (M : Matrix (α × β) (α × β) ℂ) : M.trace = (QAlgorithms.traceRight M).trace := by
  simp [Matrix.trace, QAlgorithms.traceRight, Fintype.sum_prod_type]

lemma traceRight_uniform (a b : ℕ) (hb : 0 < b) :
    QAlgorithms.traceRight ((b : ℂ)⁻¹ • (1 : Matrix (Fin a × Fin b) (Fin a × Fin b) ℂ)) = 1 := by
  ext j k
  simp only [QAlgorithms.traceRight, Matrix.of_apply, Matrix.smul_apply, Matrix.one_apply,
    Prod.mk.injEq, and_true, smul_eq_mul]
  by_cases h : j = k
  · subst h
    have : (b : ℂ) ≠ 0 := by exact_mod_cast hb.ne'
    simp [this]
  · simp [h]

/-- trace of an operator whose right partial trace is the identity -/
lemma trace_of_traceRight_one {a b : ℕ} (M : Matrix (Fin a × Fin b) (Fin a × Fin b) ℂ)
    (h : QAlgorithms.traceRight M = 1) : M.trace = (a : ℂ) := by
  rw [trace_eq_trace_traceRight, h]; simp

end X6P05

open QAlgorithms.Papers.Independent.Dependency50.P05 X6P05 in
theorem solution {A B : System} (T : Supermap A B)
    (hT : IsDoublyStochastic T) : A.input * B.output = B.input * A.output := by
  obtain ⟨⟨_, hTtp⟩, S, hdual, ⟨_, hStp⟩⟩ := hT
  set X : Matrix (ChoiRegister A) (ChoiRegister A) ℂ := ((A.output : ℂ))⁻¹ • 1 with hX
  set Y : Matrix (ChoiRegister B) (ChoiRegister B) ℂ := ((B.output : ℂ))⁻¹ • 1 with hY
  have hXr : QAlgorithms.traceRight X = 1 := traceRight_uniform _ _ A.output_pos
  have hYr : QAlgorithms.traceRight Y = 1 := traceRight_uniform _ _ B.output_pos
  have hTX : (T X).trace = (B.input : ℂ) := trace_of_traceRight_one _ (hTtp X hXr)
  have hSY : (S Y).trace = (A.input : ℂ) := trace_of_traceRight_one _ (hStp Y hYr)
  have hd := hdual X Y
  have hb : (A.output : ℂ) ≠ 0 := by exact_mod_cast A.output_pos.ne'
  have hd' : (B.output : ℂ) ≠ 0 := by exact_mod_cast B.output_pos.ne'
  have lhs : ((T X)ᴴ * Y).trace = (B.output : ℂ)⁻¹ * (B.input : ℂ) := by
    rw [hY, Matrix.mul_smul, Matrix.mul_one, Matrix.trace_smul, Matrix.trace_conjTranspose, hTX]
    simp
  have rhs : (Xᴴ * S Y).trace = (A.output : ℂ)⁻¹ * (A.input : ℂ) := by
    rw [hX, Matrix.conjTranspose_smul, Matrix.conjTranspose_one, Matrix.smul_mul,
      Matrix.one_mul, Matrix.trace_smul, hSY]
    simp
  rw [lhs, rhs] at hd
  have key : ((A.input * B.output : ℕ) : ℂ) = ((B.input * A.output : ℕ) : ℂ) := by
    push_cast
    field_simp at hd
    linear_combination -hd
  exact_mod_cast key
