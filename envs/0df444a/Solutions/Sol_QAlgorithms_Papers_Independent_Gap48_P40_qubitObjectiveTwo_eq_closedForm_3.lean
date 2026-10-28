-- Prove2me | solution 3 for QAlgorithms.Papers.Independent.Gap48.P40.qubitObjectiveTwo_eq_closedForm
-- status  : ACCEPTED   (prove)
-- author  : @Alien60
-- created : 2026-10-28T18:19:19.728994+00:00
-- url     : https://prove2.me/submissions/2ec15708-77d2-4277-ba4d-a80a4cba8ff4

import Definitions.Def_QAlgorithms_Papers_Independent_Gap48_P40

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder Topology Matrix.Norms.L2Operator

open Filter MeasureTheory Asymptotics

open QAlgorithms

open QAlgorithms.Papers.Independent.Dependency50.P21 (relativeEntropy)

open QAlgorithms.Papers.Independent.Information100.P50 (IsUINorm)

open QAlgorithms.Papers.Independent.Information100.P56 (entropy)

open QAlgorithms.Papers.Independent.Information100.P60 (copies)

open QAlgorithms.Papers.Independent.Information100.P44 (Mat)


namespace P40L10Aux

/-- Real symmetric `2 × 2` matrix `[[a, c], [c, d]]` viewed as a complex matrix. -/
def M2 (a c d : ℝ) : Mat 2 := !![(a : ℂ), (c : ℂ); (c : ℂ), (d : ℂ)]

lemma M2_sa (a c d : ℝ) : IsSelfAdjoint (M2 a c d) := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [M2, Matrix.star_apply]

lemma spec_M2 {a c d l1 l2 x : ℝ} (hs : l1 + l2 = a + d) (hp : l1 * l2 = a * d - c ^ 2)
    (hx : x ∈ spectrum ℝ (M2 a c d)) : x = l1 ∨ x = l2 := by
  rw [spectrum.mem_iff, Matrix.isUnit_iff_isUnit_det, isUnit_iff_ne_zero, not_not,
    Algebra.algebraMap_eq_smul_one, Matrix.det_fin_two] at hx
  simp [M2, Matrix.smul_apply, Matrix.one_apply] at hx
  have h' : (((x - a) * (x - d) - c * c : ℝ) : ℂ) = 0 := by push_cast; linear_combination hx
  have h'' : (x - l1) * (x - l2) = 0 := by
    have := (Complex.ofReal_eq_zero).mp h'
    linear_combination this + 0 * hs + (-x) * hs + hp
  rcases mul_eq_zero.mp h'' with h | h
  · exact Or.inl (by linarith)
  · exact Or.inr (by linarith)

lemma cfc_M2 {a c d l1 l2 : ℝ} (hs : l1 + l2 = a + d) (hp : l1 * l2 = a * d - c ^ 2)
    (f : ℝ → ℝ) :
    cfc f (M2 a c d) = algebraMap ℝ (Mat 2) (f l2 - (f l1 - f l2) / (l1 - l2) * l2) +
      ((f l1 - f l2) / (l1 - l2)) • M2 a c d := by
  have hsa := M2_sa a c d
  set b0 := (f l1 - f l2) / (l1 - l2)
  set a0 := f l2 - b0 * l2
  rw [cfc_congr (g := fun x => (fun _ => a0) x + (fun x => b0 * x) x)]
  · rw [cfc_add (a := M2 a c d) (fun _ => a0) (fun x => b0 * x) continuousOn_const
      ((continuous_const.mul continuous_id).continuousOn),
      cfc_const (ha := hsa), cfc_const_mul_id (ha := hsa)]
  · intro x hx
    rcases spec_M2 hs hp hx with rfl | rfl
    · by_cases h : x = l2
      · subst h; simp [a0]
      · have : b0 * (x - l2) = f x - f l2 := div_mul_cancel₀ _ (sub_ne_zero.mpr h)
        simp only [a0]; linear_combination -this
    · simp [a0]

lemma trace_cfc_M2 {a c d l1 l2 : ℝ} (hs : l1 + l2 = a + d) (hp : l1 * l2 = a * d - c ^ 2)
    (f : ℝ → ℝ) : (cfc f (M2 a c d)).trace.re = f l1 + f l2 := by
  rw [cfc_M2 hs hp, Algebra.algebraMap_eq_smul_one]
  obtain ⟨b, hb⟩ : ∃ b, b = (f l1 - f l2) / (l1 - l2) := ⟨_, rfl⟩
  rw [← hb, Matrix.trace_fin_two]
  simp [M2]
  by_cases h : l1 = l2
  · subst h; simp [hb]
  · have : b * (l1 - l2) = f l1 - f l2 := by rw [hb]; exact div_mul_cancel₀ _ (sub_ne_zero.mpr h)
    linear_combination this - b * hs

lemma trace_mul_cfc_M2 {a c d l1 l2 : ℝ} (hs : l1 + l2 = a + d) (hp : l1 * l2 = a * d - c ^ 2)
    (f : ℝ → ℝ) (p q r : ℝ) :
    (M2 p q r * cfc f (M2 a c d)).trace.re =
      (f l2 - (f l1 - f l2) / (l1 - l2) * l2) * (p + r) +
        (f l1 - f l2) / (l1 - l2) * (p * a + 2 * q * c + r * d) := by
  rw [cfc_M2 hs hp, Algebra.algebraMap_eq_smul_one]
  generalize (f l1 - f l2) / (l1 - l2) = b
  rw [Matrix.trace_fin_two, Matrix.mul_apply, Matrix.mul_apply, Fin.sum_univ_two, Fin.sum_univ_two]
  simp [M2]
  ring

lemma supported_M2 {p q r a c d : ℝ} (h : a * d - c ^ 2 ≠ 0) :
    QAlgorithms.Papers.Independent.Dependency50.P21.IsSupported (M2 p q r) (M2 a c d) := by
  intro v hv
  simp only [LinearMap.mem_ker, Matrix.mulVecLin_apply] at hv ⊢
  have hdet : (M2 a c d).det ≠ 0 := by
    rw [Matrix.det_fin_two]; simp [M2]
    exact_mod_cast (by rw [← sq]; exact h : (a * d - c * c : ℝ) ≠ 0)
  rw [Matrix.eq_zero_of_mulVec_eq_zero hdet hv, Matrix.mulVec_zero]

end P40L10Aux

namespace P40L10Aux

lemma sqrt_half_mul {t : ℝ} (h0 : -1 ≤ t) (h1 : t ≤ 1) :
    Real.sqrt ((1 + t) / 2) * Real.sqrt ((1 - t) / 2) = Real.sqrt (1 - t ^ 2) / 2 := by
  rw [← Real.sqrt_mul (by linarith), show (1 + t) / 2 * ((1 - t) / 2) = (1 - t ^ 2) / 2 ^ 2 by ring,
    Real.sqrt_div' _ (by positivity), Real.sqrt_sq (by norm_num)]

lemma dens_eq (D1 D2 e t : ℝ) (h0 : -1 ≤ t) (h1 : t ≤ 1) :
    Matrix.diagonal ![(D1 : ℂ), (D2 : ℂ)] + (e : ℂ) • pureDensity (WithLp.toLp 2
      ![(Real.sqrt ((1 + t) / 2) : ℂ), (Real.sqrt ((1 - t) / 2) : ℂ)] : EuclideanSpace ℂ (Fin 2)) =
      M2 (D1 + e * (1 + t) / 2) (e * Real.sqrt (1 - t ^ 2) / 2) (D2 + e * (1 - t) / 2) := by
  have hm := sqrt_half_mul h0 h1
  have hp : Real.sqrt ((1 + t) / 2) * Real.sqrt ((1 + t) / 2) = (1 + t) / 2 :=
    Real.mul_self_sqrt (by linarith)
  have hq : Real.sqrt ((1 - t) / 2) * Real.sqrt ((1 - t) / 2) = (1 - t) / 2 :=
    Real.mul_self_sqrt (by linarith)
  generalize Real.sqrt ((1 + t) / 2) = u at *
  generalize Real.sqrt ((1 - t) / 2) = v at *
  generalize Real.sqrt (1 - t ^ 2) = z at *
  have hm' : (u : ℂ) * v = z / 2 := by exact_mod_cast hm
  have hp' : (u : ℂ) * u = (1 + t) / 2 := by exact_mod_cast hp
  have hq' : (v : ℂ) * v = (1 - t) / 2 := by exact_mod_cast hq
  ext i j; fin_cases i <;> fin_cases j <;> simp [M2, pureDensity]
  · linear_combination (e : ℂ) * hp'
  · linear_combination (e : ℂ) * hm'
  · linear_combination (e : ℂ) * hm'
  · linear_combination (e : ℂ) * hq'

end P40L10Aux

open P40L10Aux QAlgorithms.Papers.Independent.Gap48.P40 in
theorem solution (beta T t : ℝ) (hbeta : 0 < beta ∧ beta ≤ 1 / 2)
    (hT : beta < T ∧ T ≤ 1 - beta) (ht : t ∈ Set.Icc (-1 : ℝ) 1) :
    qubitObjectiveTwo beta T t =
      (let x := beta - T + (1 - beta - T) * t
       let y2 := (1 - beta - T) ^ 2 * (1 - t ^ 2)
       let rs := Real.sqrt (x ^ 2 + y2)
       let rr := Real.sqrt ((x + 2 * T) ^ 2 + y2)
       let w := ((x + 2 * T) * x + y2) / rs
       (1 + rr) / 2 * Real.log ((1 + rr) / 2) + (1 - rr) / 2 * Real.log ((1 - rr) / 2) -
         ((1 + w) / 2 * Real.log ((1 + rs) / 2) + (1 - w) / 2 * Real.log ((1 - rs) / 2))) := by
  obtain ⟨hb0, hb1⟩ := hbeta
  obtain ⟨hT0, hT1⟩ := hT
  obtain ⟨ht0, ht1⟩ := ht
  have hs2 : Real.sqrt (1 - t ^ 2) ^ 2 = 1 - t ^ 2 := Real.sq_sqrt (by nlinarith)
  have hρ := dens_eq (beta + T) 0 (1 - beta - T) t ht0 ht1
  have hσ := dens_eq beta T (1 - beta - T) t ht0 ht1
  push_cast at hρ hσ
  unfold qubitObjectiveTwo
  dsimp only
  push_cast
  rw [hρ, hσ]
  have hη : 0 ≤ 1 - beta - T := by linarith
  have hRR2 := Real.sq_sqrt (show 0 ≤ (beta - T + (1 - beta - T) * t + 2 * T) ^ 2 +
    (1 - beta - T) ^ 2 * (1 - t ^ 2) by nlinarith)
  have hRS2 := Real.sq_sqrt (show 0 ≤ (beta - T + (1 - beta - T) * t) ^ 2 +
    (1 - beta - T) ^ 2 * (1 - t ^ 2) by nlinarith)
  generalize Real.sqrt ((beta - T + (1 - beta - T) * t + 2 * T) ^ 2 +
    (1 - beta - T) ^ 2 * (1 - t ^ 2)) = RR at *
  generalize Real.sqrt ((beta - T + (1 - beta - T) * t) ^ 2 +
    (1 - beta - T) ^ 2 * (1 - t ^ 2)) = RS at *
  generalize Real.sqrt (1 - t ^ 2) = s at *
  have hdet : (beta + (1 - beta - T) * (1 + t) / 2) * (T + (1 - beta - T) * (1 - t) / 2) -
      ((1 - beta - T) * s / 2) ^ 2 ≠ 0 := by
    have e : (beta + (1 - beta - T) * (1 + t) / 2) * (T + (1 - beta - T) * (1 - t) / 2) -
        ((1 - beta - T) * s / 2) ^ 2 = beta * T + beta * (1 - beta - T) * (1 - t) / 2 +
          T * (1 - beta - T) * (1 + t) / 2 := by
      linear_combination (-(1 - beta - T) ^ 2 / 4) * hs2
    rw [e]
    have h1 : 0 < beta * T := mul_pos hb0 (by linarith)
    have h2 : 0 ≤ beta * (1 - beta - T) * (1 - t) :=
      mul_nonneg (mul_nonneg hb0.le hη) (by linarith)
    have h3 : 0 ≤ T * (1 - beta - T) * (1 + t) :=
      mul_nonneg (mul_nonneg (by linarith) hη) (by linarith)
    linarith
  rw [relativeEntropy, if_pos (supported_M2 hdet), EReal.toReal_coe, Matrix.trace_sub,
    Complex.sub_re, trace_cfc_M2 (l1 := (1 + RR) / 2) (l2 := (1 - RR) / 2) (by ring)
      (by linear_combination (-1 / 4 : ℝ) * hRR2 + ((1 - beta - T) ^ 2 / 4) * hs2),
    trace_mul_cfc_M2 (l1 := (1 + RS) / 2) (l2 := (1 - RS) / 2) (by ring)
      (by linear_combination (-1 / 4 : ℝ) * hRS2 + ((1 - beta - T) ^ 2 / 4) * hs2)]
  beta_reduce
  rw [show (1 + RS) / 2 - (1 - RS) / 2 = RS by ring]
  by_cases h0 : RS = 0
  · subst h0; simp; ring
  · have hK : (Real.log ((1 + RS) / 2) - Real.log ((1 - RS) / 2)) / RS * RS =
        Real.log ((1 + RS) / 2) - Real.log ((1 - RS) / 2) := div_mul_cancel₀ _ h0
    linear_combination (-1 / 2 : ℝ) * hK -
      ((Real.log ((1 + RS) / 2) - Real.log ((1 - RS) / 2)) / RS * (1 - beta - T) ^ 2 / 2) * hs2

end
