-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Intakenext100.P93.twoPauli_not_degradable
-- status  : ACCEPTED   (prove)
-- author  : @vibe-prover
-- created : 2026-11-10T16:01:53.006362+00:00
-- url     : https://prove2.me/submissions/8bf84d9b-e1ac-4574-8278-c722f535df95

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P93

set_option autoImplicit false


noncomputable section

open scoped BigOperators ComplexConjugate Matrix ComplexOrder

namespace QAlgorithms

/-- Every finite Kraus map preserves positive semidefinite matrices.
Normalization is unnecessary for this part of the channel property. -/
theorem krausApply_posSemidef_S11 {ι κ K : Type*}
    [Fintype ι] [Fintype κ] [Fintype K]
    (E : K → Matrix κ ι ℂ) {ρ : Matrix ι ι ℂ}
    (hρ : ρ.PosSemidef) : (krausApply E ρ).PosSemidef := by
  classical
  exact Matrix.posSemidef_sum Finset.univ
    (fun j _ => hρ.mul_mul_conjTranspose_same (E j))

/-- The published channel predicate supplies a finite Kraus representation. -/
theorem channel_posSemidef_S11 {ι κ : Type*}
    [Fintype ι] [Fintype κ] [DecidableEq ι]
    {D : Superop ι κ} (hD : IsChannel D) {ρ : Matrix ι ι ℂ}
    (hρ : ρ.PosSemidef) : (D ρ).PosSemidef := by
  obtain ⟨m, E, _, hE⟩ := hD
  rw [hE ρ]
  exact krausApply_posSemidef_S11 E hρ

theorem zero_basis_projector_posSemidef_S11 :
    (Matrix.diagonal (fun b : Bool => if b then (0 : ℂ) else 1)).PosSemidef := by
  apply Matrix.PosSemidef.diagonal
  intro b
  cases b <;> simp

end QAlgorithms

end


set_option autoImplicit false

noncomputable section

namespace QAlgorithms.Papers.Independent.Intakenext100.P93

open QAlgorithms
open scoped BigOperators ComplexConjugate Matrix

private theorem sqrt_noise_sq (p : ℝ) (hp0 : 0 < p) :
    (Real.sqrt (p / 2) : ℂ) ^ 2 = (p : ℂ) / 2 := by
  norm_cast
  exact Real.sq_sqrt (by positivity)

private theorem sqrt_identity_sq (p : ℝ) (hp1 : p < 1) :
    (Real.sqrt (1 - p) : ℂ) ^ 2 = 1 - (p : ℂ) := by
  norm_cast
  exact Real.sq_sqrt (by linarith)

/-- The three environment branches have squared weights p/2, p/2, and 1-p. -/
theorem twoPauliDilation_isometry (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1) :
    QAlgorithms.Papers.Independent.Information100.P67.IsIsometry (twoPauliDilation p) := by
  have hN := sqrt_noise_sq p hp0
  have hI := sqrt_identity_sq p hp1
  unfold QAlgorithms.Papers.Independent.Information100.P67.IsIsometry
  apply Matrix.ext
  intro i j
  cases i <;> cases j <;>
    simp [-Real.sqrt_div, -Real.sqrt_div', Matrix.mul_apply, Matrix.conjTranspose_apply, Fintype.sum_prod_type,
      Fin.sum_univ_succ, twoPauliDilation, pauliX, pauliZ,
      Matrix.one_apply, Matrix.diagonal_apply]
    <;> linear_combination hI + 2 * hN

/-- Tracing out the environment retains exactly the X, Z, and identity Kraus branches. -/
theorem twoPauliDilation_receiver (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1) :
    QAlgorithms.Papers.Independent.Information100.P67.receiverChannel
      (twoPauliDilation p) = twoPauliChannel p := by
  have hN := sqrt_noise_sq p hp0
  have hI := sqrt_identity_sq p hp1
  funext rho
  apply Matrix.ext
  intro i j
  cases i <;> cases j <;>
    simp [-Real.sqrt_div, -Real.sqrt_div', QAlgorithms.Papers.Independent.Information100.P67.receiverChannel,
      traceRight, twoPauliChannel, conjSuperop, Matrix.mul_apply,
      Matrix.conjTranspose_apply,
      Fin.sum_univ_succ, twoPauliDilation, pauliX, pauliZ,
      Matrix.one_apply, Matrix.diagonal_apply]
    <;> ring_nf at hN hI ⊢
    <;> simp only [hN, hI]
    <;> ring

end QAlgorithms.Papers.Independent.Intakenext100.P93

end

#print axioms QAlgorithms.Papers.Independent.Intakenext100.P93.twoPauliDilation_isometry
#print axioms QAlgorithms.Papers.Independent.Intakenext100.P93.twoPauliDilation_receiver


noncomputable section

open scoped BigOperators ComplexConjugate Matrix
open QAlgorithms
open QAlgorithms.Papers.Independent.Information100.P67

namespace QAlgorithms.Papers.Independent.Intakenext100.P93

/-- The input is not required to be positive: the degrading identity is on all operators. -/
def certificateRho (p : ℝ) : Matrix Bool Bool ℂ :=
  Matrix.diagonal fun b => if b then -(p : ℂ) / (2 * (1 - (p : ℂ)))
    else (2 - (p : ℂ)) / (2 * (1 - (p : ℂ)))

/-- A vector supported on the Z and identity environment coordinates. -/
def certificateVector (p : ℝ) : Fin 3 → ℂ :=
  ![0, (Real.sqrt (1 - p) : ℂ), -(Real.sqrt (p / 2) : ℂ)]

theorem certificate_receiver (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1) :
    receiverChannel (twoPauliDilation p) (certificateRho p) =
      Matrix.diagonal (fun b : Bool => if b then (0 : ℂ) else 1) := by
  have ha : (Real.sqrt (p / 2) : ℂ) ^ 2 = (p : ℂ) / 2 := by
    exact_mod_cast Real.sq_sqrt (by positivity : 0 ≤ p / 2)
  have hb : (Real.sqrt (1 - p) : ℂ) ^ 2 = 1 - (p : ℂ) := by
    exact_mod_cast Real.sq_sqrt (by linarith : 0 ≤ 1 - p)
  have hne : 1 - (p : ℂ) ≠ 0 := by
    exact_mod_cast (ne_of_gt (sub_pos.mpr hp1))
  ring_nf at ha hb
  apply Matrix.ext
  intro i j
  cases i <;> cases j <;>
    simp [receiverChannel, traceRight, Matrix.mul_apply,
      Fin.sum_univ_succ, twoPauliDilation, pauliX, pauliZ, Matrix.diagonal_apply,
      Matrix.conjTranspose_apply, Matrix.one_apply, certificateRho,
      -Real.sqrt_div, -Real.sqrt_div']
  all_goals
    field_simp [hne, -Real.sqrt_div, -Real.sqrt_div']
    ring_nf
    simp only [ha, hb]
    ring

theorem certificate_quadratic (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1) :
    star (certificateVector p) ⬝ᵥ
        ((complementaryChannel (twoPauliDilation p) (certificateRho p)).mulVec
          (certificateVector p)) = -((p : ℂ) ^ 2) := by
  have ha : (Real.sqrt (p / 2) : ℂ) ^ 2 = (p : ℂ) / 2 := by
    exact_mod_cast Real.sq_sqrt (by positivity : 0 ≤ p / 2)
  have hb : (Real.sqrt (1 - p) : ℂ) ^ 2 = 1 - (p : ℂ) := by
    exact_mod_cast Real.sq_sqrt (by linarith : 0 ≤ 1 - p)
  have hne : 1 - (p : ℂ) ≠ 0 := by
    exact_mod_cast (ne_of_gt (sub_pos.mpr hp1))
  ring_nf at ha hb
  simp [dotProduct, Matrix.mulVec, complementaryChannel, traceLeft,
    Matrix.mul_apply, Fin.sum_univ_succ, twoPauliDilation,
    pauliX, pauliZ, Matrix.diagonal_apply, Matrix.conjTranspose_apply,
    Matrix.one_apply, certificateRho, certificateVector,
    -Real.sqrt_div, -Real.sqrt_div']
  field_simp [hne, -Real.sqrt_div, -Real.sqrt_div']
  ring_nf
  simp only [ha, hb]
  ring

end QAlgorithms.Papers.Independent.Intakenext100.P93

end


noncomputable section

open QAlgorithms
open QAlgorithms.Papers.Independent.Intakenext100.P93
open QAlgorithms.Papers.Independent.Information100.P67
open scoped BigOperators ComplexConjugate Matrix ComplexOrder

/-- A positive receiver output would have to map to a positive complementary output,
but the explicit environment vector has negative quadratic form. -/
theorem solution (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1) :
    QAlgorithms.Papers.Independent.Information100.P67.IsIsometry (twoPauliDilation p) ∧
    QAlgorithms.Papers.Independent.Information100.P67.receiverChannel
      (twoPauliDilation p) = twoPauliChannel p ∧
    ¬ QAlgorithms.Papers.Independent.Information100.P67.IsDegradable (twoPauliDilation p) := by
  refine ⟨twoPauliDilation_isometry p hp0 hp1,
    twoPauliDilation_receiver p hp0 hp1, ?_⟩
  rintro ⟨_, D, hD, hcomp⟩
  have hpos : (complementaryChannel (twoPauliDilation p)
      (certificateRho p)).PosSemidef := by
    rw [hcomp (certificateRho p), certificate_receiver p hp0 hp1]
    exact channel_posSemidef_S11 hD zero_basis_projector_posSemidef_S11
  have hn := hpos.dotProduct_mulVec_nonneg (certificateVector p)
  rw [certificate_quadratic p hp0 hp1] at hn
  have hn' : 0 ≤ -(p ^ 2) := by exact_mod_cast hn
  nlinarith [sq_pos_of_pos hp0]

end

#print axioms solution
