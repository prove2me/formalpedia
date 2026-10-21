-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Information100.P48.adc_choi
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-20T08:12:11.086057+00:00
-- url     : https://prove2.me/submissions/22a01a85-2f8e-47b7-aa69-d0ebc4d336a5

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P48

noncomputable section
open scoped Matrix ComplexConjugate ComplexOrder
open QAlgorithms QAlgorithms.Papers.Independent.Information100.P48

namespace G55ADC

lemma choi_eq (g : ℝ) (hg0 : 0 ≤ g) (hg1 : g ≤ 1) : choi (adc g) = adcChoiMatrix g := by
  have h1 : (Real.sqrt (1 - g) : ℂ) * (Real.sqrt (1 - g) : ℂ) = ((1 - g : ℝ) : ℂ) := by
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt (by linarith)]
  have h2 : (Real.sqrt g : ℂ) * (Real.sqrt g : ℂ) = (g : ℂ) := by
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt hg0]
  have h1' : (Real.sqrt (1 - g) : ℂ) ^ 2 = 1 - (g : ℂ) := by rw [sq, h1]; push_cast; ring
  have h2' : (Real.sqrt g : ℂ) ^ 2 = (g : ℂ) := by rw [sq, h2]
  ext ⟨a, b⟩ ⟨c, d⟩
  cases a <;> cases b <;> cases c <;> cases d <;>
    simp [choi, QAlgorithms.idTensorSuperop, adc, k0, k1, bellDensity, Matrix.mul_apply, adcChoiMatrix,
      pairMatrix, pairIndex, Fintype.sum_bool, Matrix.diagonal_apply, h1, h2] <;> ring_nf <;> simp [h1', h2'] <;> ring


lemma dens (g : ℝ) (hg0 : 0 ≤ g) (hg1 : g ≤ 1) : IsDensityMatrix (adcChoiMatrix g) := by
  set v : Bool × Bool → ℂ := fun p => if p = (false, false) then ((Real.sqrt 2)⁻¹ : ℂ)
    else if p = (true, true) then (Real.sqrt (1 - g) : ℂ) * ((Real.sqrt 2)⁻¹ : ℂ) else 0 with hv
  have h2 : ((Real.sqrt 2 : ℝ) : ℂ) * ((Real.sqrt 2 : ℝ) : ℂ) = 2 := by
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt (by norm_num)]; norm_num
  have h1 : (Real.sqrt (1 - g) : ℂ) * (Real.sqrt (1 - g) : ℂ) = ((1 - g : ℝ) : ℂ) := by
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt (by linarith)]
  have hs2 : ((Real.sqrt 2 : ℝ) : ℂ) ≠ 0 := by
    have : (0 : ℝ) < Real.sqrt 2 := by positivity
    exact_mod_cast this.ne'
  have h2' : ((Real.sqrt 2 : ℝ) : ℂ) ^ 2 = 2 := by rw [sq, h2]
  have h1' : (Real.sqrt (1 - g) : ℂ) ^ 2 = 1 - (g : ℂ) := by rw [sq, h1]; push_cast; ring
  have e : adcChoiMatrix g = Matrix.vecMulVec v (star v) +
      Matrix.diagonal (fun p : Bool × Bool => if p = (true, false) then ((g / 2 : ℝ) : ℂ) else 0) := by
    ext ⟨a, b⟩ ⟨c, d⟩
    cases a <;> cases b <;> cases c <;> cases d <;>
      simp [adcChoiMatrix, pairMatrix, pairIndex, hv, Matrix.vecMulVec_apply, Matrix.diagonal_apply] <;>
      field_simp <;> (try rw [h2]) <;> (try ring_nf) <;> (try simp [h1, h2, h1', h2']) <;> (try ring_nf) <;> (try simp [h1', h2'])
  refine ⟨?_, ?_⟩
  · rw [e]
    refine (Matrix.posSemidef_vecMulVec_self_star v).add (Matrix.PosSemidef.diagonal fun p => ?_)
    simp only [Pi.zero_apply]; split_ifs
    · exact_mod_cast (by positivity : (0 : ℝ) ≤ g / 2)
    · exact le_refl _
  · simp [Matrix.trace, adcChoiMatrix, pairMatrix, pairIndex, Fintype.sum_prod_type]
    push_cast; ring


lemma ctensor (g : ℝ) : correlationTensor (adcChoiMatrix g) =
    Matrix.diagonal ![Real.sqrt (1 - g), -Real.sqrt (1 - g), 1 - g] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [correlationTensor, pauli, pauliX, pauliY, pauliZ, adcChoiMatrix, pairMatrix, pairIndex,
      Matrix.mul_apply, Matrix.trace, Fintype.sum_prod_type, Matrix.kronecker, Matrix.diagonal_apply] <;>
    ring_nf


lemma chsh_formula (g : ℝ) (a0 a1 b0 b1 : Fin 3 → ℝ) :
    spatialCHSH (adcChoiMatrix g) a0 a1 b0 b1 =
      Real.sqrt (1 - g) * (a0 0 * (b0 0 + b1 0) - a0 1 * (b0 1 + b1 1) + a1 0 * (b0 0 - b1 0)
        - a1 1 * (b0 1 - b1 1)) + (1 - g) * (a0 2 * (b0 2 + b1 2) + a1 2 * (b0 2 - b1 2)) := by
  simp only [spatialCHSH, bloch, Fin.sum_univ_three, pauli]
  simp [pauliX, pauliY, pauliZ, adcChoiMatrix, pairMatrix, pairIndex, Matrix.mul_apply, Matrix.trace,
    Fintype.sum_prod_type, Matrix.kronecker, Matrix.diagonal_apply]
  ring_nf


lemma cs3 (a0 a1 a2 p0 p1 p2 : ℝ) :
    (a0 * p0 + a1 * p1 + a2 * p2) ^ 2 ≤ (a0 ^ 2 + a1 ^ 2 + a2 ^ 2) * (p0 ^ 2 + p1 ^ 2 + p2 ^ 2) := by
  nlinarith [sq_nonneg (a0 * p1 - a1 * p0), sq_nonneg (a0 * p2 - a2 * p0), sq_nonneg (a1 * p2 - a2 * p1)]

lemma half_bound (s t : ℝ) (hs : 0 ≤ s) (ht : |t| ≤ s) (a : Fin 3 → ℝ) (ha : ∑ i, a i ^ 2 = 1)
    (u0 u1 u2 : ℝ) :
    s * (a 0 * u0 - a 1 * u1) + t * (a 2 * u2) ≤ s * Real.sqrt (u0 ^ 2 + u1 ^ 2 + u2 ^ 2) := by
  rw [Fin.sum_univ_three] at ha
  have hc := cs3 (a 0) (a 1) (a 2) (s * u0) (-(s * u1)) (t * u2)
  rw [ha, one_mul] at hc
  have ht2 : t ^ 2 ≤ s ^ 2 := by
    have := sq_abs t; nlinarith [abs_nonneg t]
  have hle : (s * u0) ^ 2 + (-(s * u1)) ^ 2 + (t * u2) ^ 2 ≤ (s * Real.sqrt (u0 ^ 2 + u1 ^ 2 + u2 ^ 2)) ^ 2 := by
    have hq := Real.sq_sqrt (show 0 ≤ u0 ^ 2 + u1 ^ 2 + u2 ^ 2 by positivity)
    rw [show (s * Real.sqrt (u0 ^ 2 + u1 ^ 2 + u2 ^ 2)) ^ 2 = s ^ 2 * (Real.sqrt (u0 ^ 2 + u1 ^ 2 + u2 ^ 2)) ^ 2 by ring,
      hq]
    nlinarith [sq_nonneg u2, mul_le_mul_of_nonneg_right ht2 (sq_nonneg u2)]
  have := Real.abs_le_sqrt (hc.trans hle)
  rw [Real.sqrt_sq (by positivity)] at this
  have e : s * (a 0 * u0 - a 1 * u1) + t * (a 2 * u2) = a 0 * (s * u0) + a 1 * (-(s * u1)) + a 2 * (t * u2) := by ring
  rw [e]; exact (le_abs_self _).trans this

lemma greatest (g : ℝ) (hg0 : 0 ≤ g) (hg1 : g ≤ 1) :
    IsGreatest (spatialValues (adcChoiMatrix g)) (2 * Real.sqrt (2 * (1 - g))) := by
  set s := Real.sqrt (1 - g) with hs
  have hs0 : 0 ≤ s := Real.sqrt_nonneg _
  have hss : s * s = 1 - g := Real.mul_self_sqrt (by linarith)
  have hs1 : s ≤ 1 := by nlinarith
  have ht : |1 - g| ≤ s := by rw [abs_of_nonneg (by linarith)]; nlinarith
  have htarget : 2 * Real.sqrt (2 * (1 - g)) = 2 * Real.sqrt 2 * s := by
    rw [Real.sqrt_mul (by norm_num)]; ring
  have h2 : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
  have h2pos : 0 < Real.sqrt 2 := by positivity
  constructor
  · refine ⟨![1, 0, 0], ![0, -1, 0], ![(Real.sqrt 2)⁻¹, (Real.sqrt 2)⁻¹, 0],
      ![(Real.sqrt 2)⁻¹, -(Real.sqrt 2)⁻¹, 0], ?_, ?_, ?_, ?_, ?_⟩
    · simp [UnitDirection, Fin.sum_univ_three]
    · simp [UnitDirection, Fin.sum_univ_three]
    · simp [UnitDirection, Fin.sum_univ_three]; field_simp; nlinarith
    · simp [UnitDirection, Fin.sum_univ_three]; field_simp; nlinarith
    · rw [chsh_formula, htarget]
      simp
      field_simp
      nlinarith
  · rintro v ⟨a0, a1, b0, b1, ha0, ha1, hb0, hb1, rfl⟩
    rw [chsh_formula, htarget]
    have e1 := half_bound s (1 - g) hs0 ht a0 ha0 (b0 0 + b1 0) (b0 1 + b1 1) (b0 2 + b1 2)
    have e2 := half_bound s (1 - g) hs0 ht a1 ha1 (b0 0 - b1 0) (b0 1 - b1 1) (b0 2 - b1 2)
    unfold UnitDirection at hb0 hb1
    rw [Fin.sum_univ_three] at hb0 hb1
    set U := (b0 0 + b1 0) ^ 2 + (b0 1 + b1 1) ^ 2 + (b0 2 + b1 2) ^ 2
    set W := (b0 0 - b1 0) ^ 2 + (b0 1 - b1 1) ^ 2 + (b0 2 - b1 2) ^ 2
    have hUW : U + W = 4 := by simp only [U, W]; nlinarith
    have hU0 : 0 ≤ U := by positivity
    have hW0 : 0 ≤ W := by positivity
    have hsum : Real.sqrt U + Real.sqrt W ≤ 2 * Real.sqrt 2 := by
      have hu := Real.sq_sqrt hU0
      have hw := Real.sq_sqrt hW0
      have h22 := Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)
      nlinarith [sq_nonneg (Real.sqrt U - Real.sqrt W), Real.sqrt_nonneg U, Real.sqrt_nonneg W]
    have : s * Real.sqrt U + s * Real.sqrt W ≤ 2 * Real.sqrt 2 * s := by nlinarith
    linarith


lemma thr (g : ℝ) (hg1 : g ≤ 1) : (2 < 2 * Real.sqrt (2 * (1 - g)) ↔ g < 1 / 2) := by
  constructor
  · intro h
    have h1 : 1 < Real.sqrt (2 * (1 - g)) := by linarith
    rw [Real.lt_sqrt (by norm_num)] at h1
    linarith
  · intro h
    have : 1 < Real.sqrt (2 * (1 - g)) := by
      rw [Real.lt_sqrt (by norm_num)]; linarith
    linarith

lemma succ1 (g : ℝ) (hg0 : 0 ≤ g) (hg1 : g ≤ 1) : success (adc g) = 1 := by
  have h1 : (Real.sqrt (1 - g) : ℂ) * (Real.sqrt (1 - g) : ℂ) = ((1 - g : ℝ) : ℂ) := by
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt (by linarith)]
  have h2 : (Real.sqrt g : ℂ) * (Real.sqrt g : ℂ) = (g : ℂ) := by
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt hg0]
  simp [success, adc, k0, k1, mixedQubit, Matrix.mul_apply, Matrix.trace, Fintype.sum_bool, Matrix.diagonal_apply]
  rw [Real.mul_self_sqrt (by linarith), Real.mul_self_sqrt hg0]
  ring


lemma corr (g : ℝ) (hg0 : 0 ≤ g) (hg1 : g ≤ 1) (a b : Fin 3 → ℝ) :
    correlator (adc g) (bloch a) (bloch b) =
      (choi (adc g) * Matrix.kronecker (bloch a).transpose (bloch b)).trace.re := by
  have hs1 := Real.mul_self_sqrt (show (0 : ℝ) ≤ 1 - g by linarith)
  have hs2 := Real.mul_self_sqrt hg0
  unfold correlator conditionalJoint
  rw [succ1 g hg0 hg1, choi_eq g hg0 hg1]
  simp only [div_one, rawJoint, projector, outcomeSign, Fintype.sum_bool, bloch, Fin.sum_univ_three, pauli]
  simp [pauliX, pauliY, pauliZ, adc, k0, k1, adcChoiMatrix, pairMatrix, pairIndex, Matrix.mul_apply,
    Matrix.trace, Fintype.sum_prod_type, Matrix.kronecker, Matrix.diagonal_apply, Fintype.sum_bool]
  ring_nf
  rw [Real.sq_sqrt (show (0 : ℝ) ≤ 1 - g by linarith), Real.sq_sqrt hg0]
  ring

end G55ADC

open G55ADC in
/-- Appendix A, PDF p.11, Eqs.(A4)–(A8): ADC Choi matrix, tensor and attained
spatial CHSH maximum. The temporal correspondence transposes Alice's observable. -/
theorem solution (g : ℝ) (hg0 : 0 ≤ g) (hg1 : g ≤ 1) :
    choi (adc g) = adcChoiMatrix g ∧
    IsDensityMatrix (choi (adc g)) ∧
    correlationTensor (choi (adc g)) =
      Matrix.diagonal ![Real.sqrt (1 - g), -Real.sqrt (1 - g), 1 - g] ∧
    IsGreatest (spatialValues (choi (adc g))) (2 * Real.sqrt (2 * (1 - g))) ∧
    (2 < 2 * Real.sqrt (2 * (1 - g)) ↔ g < 1 / 2) ∧
    (∀ a b : Fin 3 → ℝ, UnitDirection a → UnitDirection b →
      correlator (adc g) (bloch a) (bloch b) =
        (choi (adc g) * Matrix.kronecker (bloch a).transpose (bloch b)).trace.re) := by
  have h := choi_eq g hg0 hg1
  refine ⟨h, by rw [h]; exact dens g hg0 hg1, by rw [h]; exact ctensor g, by rw [h]; exact greatest g hg0 hg1,
    thr g hg1, fun a b _ _ => corr g hg0 hg1 a b⟩
