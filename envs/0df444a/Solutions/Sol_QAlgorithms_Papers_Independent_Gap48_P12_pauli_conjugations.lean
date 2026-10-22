-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Gap48.P12.pauli_conjugations
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-21T22:26:46.222693+00:00
-- url     : https://prove2.me/submissions/ce7f0332-588b-49b9-8811-0c0dbbc6f4e6

import Definitions.Def_QAlgorithms_Papers_Independent_Gap48_P12
noncomputable section

open QAlgorithms QAlgorithms.Papers.Independent.Gap48.P12


theorem g73v_expT : Complex.exp (Complex.I * Real.pi / 4) =
    ((Real.sqrt 2 : ℝ) : ℂ)⁻¹ + ((Real.sqrt 2 : ℝ) : ℂ)⁻¹ * Complex.I := by
  have : Complex.I * Real.pi / 4 = ((Real.pi / 4 : ℝ) : ℂ) * Complex.I := by push_cast; ring
  rw [this, Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin, Real.cos_pi_div_four,
    Real.sin_pi_div_four]
  have h2 : Real.sqrt 2 / 2 = (Real.sqrt 2)⁻¹ := by
    have := Real.sq_sqrt (show (0:ℝ) ≤ 2 by norm_num)
    have hp : Real.sqrt 2 ≠ 0 := by positivity
    field_simp; linarith
  rw [h2]; push_cast; ring

theorem g73v_sq : ((Real.sqrt 2 : ℝ) : ℂ) ^ 2 = 2 := by
  rw [← Complex.ofReal_pow, Real.sq_sqrt (by norm_num)]; push_cast; ring

theorem g73v_ne : ((Real.sqrt 2 : ℝ) : ℂ) ≠ 0 := by
  have : Real.sqrt 2 ≠ 0 := by positivity
  exact_mod_cast this

theorem g73v_conjs : (starRingEnd ℂ) ((Real.sqrt 2 : ℝ) : ℂ) = ((Real.sqrt 2 : ℝ) : ℂ) := Complex.conj_ofReal _


local notation "Mat" => Matrix Bool Bool ℂ

local notation "Vec" => EuclideanSpace ℂ Bool

local notation "wordMatrix" => fun (B : CircuitBasis) (w : CircuitWord) =>
  QAlgorithms.Papers.Independent.Next46.P21.wordMatrix (chronologicalInstructions B w)

/-- PDF p.11, Eqs.(10)–(12): all nine exact Pauli conjugations. -/
theorem solution :
    hadamard * pauliX * star hadamard = pauliZ ∧
    hadamard * pauliY * star hadamard = -pauliY ∧
    hadamard * pauliZ * star hadamard = pauliX ∧
    phaseS * pauliX * star phaseS = pauliY ∧
    phaseS * pauliY * star phaseS = -pauliX ∧
    phaseS * pauliZ * star phaseS = pauliZ ∧
    gateT * pauliX * star gateT = (((Real.sqrt 2)⁻¹ : ℝ) : ℂ) • (pauliX + pauliY) ∧
    gateT * pauliY * star gateT = (((Real.sqrt 2)⁻¹ : ℝ) : ℂ) • (pauliY - pauliX) ∧
    gateT * pauliZ * star gateT = pauliZ := by
  have hs := g73v_sq
  have hn := g73v_ne
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
  ext i j <;> cases i <;> cases j <;>
    simp [Matrix.mul_apply, hadamard, pauliX, pauliY, pauliZ, phaseS, gateT, Matrix.star_apply,
      g73v_expT, Complex.conj_ofReal] <;>
    field_simp <;> ring_nf <;> simp [hs] <;> ring_nf


end
