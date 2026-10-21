-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Claimed50.P10.flow_periodic_ellipses
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-20T10:22:31.112802+00:00
-- url     : https://prove2.me/submissions/5959b058-5106-4a9b-9955-3a40a8930ad5

import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P10
noncomputable section
open MeasureTheory
open scoped BigOperators Matrix Nat
open QAlgorithms.Papers.Independent.Claimed50.P10

theorem g58b_M2 : hamiltonianMatrix * hamiltonianMatrix = (-7 : ℝ) • (1 : Matrix (Fin 4) (Fin 4) ℝ) := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [hamiltonianMatrix, Matrix.mul_apply, Fin.sum_univ_four] <;> norm_num

theorem g58b_pow_even (θ : ℝ) (n : ℕ) :
    (θ • hamiltonianMatrix) ^ (2 * n) = (θ ^ (2 * n) * (-7) ^ n) • (1 : Matrix (Fin 4) (Fin 4) ℝ) := by
  have : hamiltonianMatrix ^ (2 * n) = ((-7 : ℝ) ^ n) • (1 : Matrix (Fin 4) (Fin 4) ℝ) := by
    rw [pow_mul, sq, g58b_M2, smul_pow, one_pow]
  rw [smul_pow, this, smul_smul]

theorem g58b_pow_odd (θ : ℝ) (n : ℕ) :
    (θ • hamiltonianMatrix) ^ (2 * n + 1) = (θ ^ (2 * n + 1) * (-7) ^ n) • hamiltonianMatrix := by
  rw [pow_succ, g58b_pow_even, smul_mul_smul, one_mul]; congr 1; ring

theorem g58b_exp (θ : ℝ) :
    NormedSpace.exp (θ • hamiltonianMatrix) =
      Real.cos (Real.sqrt 7 * θ) • (1 : Matrix (Fin 4) (Fin 4) ℝ) +
        (Real.sin (Real.sqrt 7 * θ) / Real.sqrt 7) • hamiltonianMatrix := by
  rw [NormedSpace.exp_eq_tsum ℝ]
  refine HasSum.tsum_eq ?_
  have h7 : Real.sqrt 7 ^ 2 = 7 := Real.sq_sqrt (by norm_num)
  have h7p : 0 < Real.sqrt 7 := by positivity
  refine HasSum.even_add_odd ?_ ?_
  · have hc := (Real.hasSum_cos (Real.sqrt 7 * θ)).smul_const (1 : Matrix (Fin 4) (Fin 4) ℝ)
    convert hc using 1
    all_goals try rfl
    funext n
    rw [g58b_pow_even, smul_smul]
    congr 1
    rw [mul_pow, pow_mul (Real.sqrt 7), h7]
    have : ((2 * n)! : ℝ) ≠ 0 := by positivity
    field_simp
    rw [show (-7 : ℝ) ^ n = (-1) ^ n * 7 ^ n by rw [← mul_pow]; norm_num]
    ring
  · have hc := ((Real.hasSum_sin (Real.sqrt 7 * θ)).div_const (Real.sqrt 7)).smul_const
      hamiltonianMatrix
    convert hc using 1
    all_goals try rfl
    funext n
    rw [g58b_pow_odd, smul_smul]
    congr 1
    rw [mul_pow, pow_succ (Real.sqrt 7), pow_mul (Real.sqrt 7), h7]
    have : ((2 * n + 1)! : ℝ) ≠ 0 := by positivity
    field_simp
    rw [show (-7 : ℝ) ^ n = (-1) ^ n * 7 ^ n by rw [← mul_pow]; norm_num]
    ring

theorem g58b_flow (θ : ℝ) {n : ℕ} (z : DoublePhaseSpace n) (j : Fin n) :
    let c := Real.cos (Real.sqrt 7 * θ)
    let t := Real.sin (Real.sqrt 7 * θ) / Real.sqrt 7
    hamiltonianFlow θ z 0 j = c * z 0 j + t * (-z 0 j + 2 * z 3 j) ∧
    hamiltonianFlow θ z 3 j = c * z 3 j + t * (-4 * z 0 j + z 3 j) ∧
    hamiltonianFlow θ z 1 j = c * z 1 j + t * (-z 1 j + 2 * z 2 j) ∧
    hamiltonianFlow θ z 2 j = c * z 2 j + t * (-4 * z 1 j + z 2 j) := by
  intro c t
  simp only [hamiltonianFlow]
  rw [g58b_exp]
  simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_four,
    Matrix.add_apply, Matrix.smul_apply, hamiltonianMatrix]
  refine ⟨?_, ?_, ?_, ?_⟩ <;> simp [Matrix.one_apply, c, t] <;> ring

/-- PDF p.5, Remark 5, using the independently constructed Hamiltonian flow.
It has period 2*pi/sqrt(7), preserves both displayed level surfaces, and rotates
each (x_j,xi_p_j) and (p_j,xi_x_j) pair along its ellipse. Zero pairs remain
stationary; no claim says an orbit fills a higher-dimensional level surface. -/
theorem solution {n : ℕ} (hn : 0 < n) :
    (∀ (theta : ℝ) (z : DoublePhaseSpace n),
      hamiltonianFlow (theta + 2 * Real.pi / Real.sqrt 7) z =
        hamiltonianFlow theta z) ∧
    (∀ (theta : ℝ) (z : DoublePhaseSpace n),
      ellipticEnergy ((hamiltonianFlow theta z) 0) ((hamiltonianFlow theta z) 3) =
        ellipticEnergy (z 0) (z 3) ∧
      ellipticEnergy ((hamiltonianFlow theta z) 1) ((hamiltonianFlow theta z) 2) =
        ellipticEnergy (z 1) (z 2) ∧
      (∀ j : Fin n,
        ellipticCoordinates ((hamiltonianFlow theta z) 0 j)
            ((hamiltonianFlow theta z) 3 j) =
          clockwiseRotation (Real.sqrt 7 * theta) (ellipticCoordinates (z 0 j) (z 3 j)) ∧
        ellipticCoordinates ((hamiltonianFlow theta z) 1 j)
            ((hamiltonianFlow theta z) 2 j) =
          clockwiseRotation (Real.sqrt 7 * theta) (ellipticCoordinates (z 1 j) (z 2 j)))) := by
  have h7 : Real.sqrt 7 ^ 2 = 7 := Real.sq_sqrt (by norm_num)
  have h7p : 0 < Real.sqrt 7 := by positivity
  have key : ∀ θ : ℝ, Real.cos (Real.sqrt 7 * θ) ^ 2 +
      7 * (Real.sin (Real.sqrt 7 * θ) / Real.sqrt 7) ^ 2 = 1 := by
    intro θ
    rw [div_pow, h7, mul_div_cancel₀ _ (by norm_num : (7:ℝ) ≠ 0)]
    exact Real.cos_sq_add_sin_sq _
  refine ⟨?_, ?_⟩
  · intro θ z
    funext a j
    have e1 : Real.sqrt 7 * (θ + 2 * Real.pi / Real.sqrt 7) = Real.sqrt 7 * θ + 2 * Real.pi := by
      field_simp
    simp only [hamiltonianFlow, g58b_exp, e1, Real.cos_add_two_pi, Real.sin_add_two_pi]
  · intro θ z
    refine ⟨?_, ?_, ?_⟩
    · unfold ellipticEnergy
      refine Finset.sum_congr rfl (fun j _ => ?_)
      obtain ⟨h0, h3, -, -⟩ := g58b_flow θ z j
      rw [h0, h3]
      linear_combination (2 * z 0 j ^ 2 + z 3 j ^ 2 - z 0 j * z 3 j) * key θ
    · unfold ellipticEnergy
      refine Finset.sum_congr rfl (fun j _ => ?_)
      obtain ⟨-, -, h1, h2⟩ := g58b_flow θ z j
      rw [h1, h2]
      linear_combination (2 * z 1 j ^ 2 + z 2 j ^ 2 - z 1 j * z 2 j) * key θ
    · intro j
      obtain ⟨h0, h3, h1, h2⟩ := g58b_flow θ z j
      have hs : Real.sqrt 7 * (Real.sin (Real.sqrt 7 * θ) / Real.sqrt 7) =
          Real.sin (Real.sqrt 7 * θ) := by field_simp
      constructor
      · rw [h0, h3]; funext i; fin_cases i
        · simp [ellipticCoordinates, clockwiseRotation]
          linear_combination (-(z 0 j) + 2 * z 3 j) * hs
        · simp [ellipticCoordinates, clockwiseRotation]
          linear_combination (-(z 0 j) * Real.sqrt 7) * hs + (Real.sin (Real.sqrt 7 * θ) / Real.sqrt 7 * z 0 j) * h7
      · rw [h1, h2]; funext i; fin_cases i
        · simp [ellipticCoordinates, clockwiseRotation]
          linear_combination (-(z 1 j) + 2 * z 2 j) * hs
        · simp [ellipticCoordinates, clockwiseRotation]
          linear_combination (-(z 1 j) * Real.sqrt 7) * hs + (Real.sin (Real.sqrt 7 * θ) / Real.sqrt 7 * z 1 j) * h7
