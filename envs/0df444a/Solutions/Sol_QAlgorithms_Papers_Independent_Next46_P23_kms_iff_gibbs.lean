-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Next46.P23.kms_iff_gibbs
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-20T22:32:16.840683+00:00
-- url     : https://prove2.me/submissions/4ae09e60-f8fd-4f12-b72a-9077d34cd4d3

import Definitions.Def_QAlgorithms_Papers_Independent_Next46_P23
noncomputable section

open Filter MeasureTheory

open scoped BigOperators ENNReal Matrix ComplexConjugate ComplexOrder Matrix.Norms.L2Operator Topology

open QAlgorithms.Papers.Independent.Next46.P23

attribute [local instance] Classical.propDecidable Classical.decEq

open QAlgorithms.Papers.Independent.Claimed50.P15 (propagator legendre rightSlope leftSlope FiniteExperiment exponentialMoment)

open QAlgorithms.Papers.Independent.Dependency50.P05 (uniformDensity)

open QAlgorithms.Papers.Independent.Dependency50.P28 (Schwarz)

open QAlgorithms.Papers.Independent.Frontier30.P28 (inverseExponent)

open QAlgorithms.Papers.Independent.Information100.P07 (support)

open QAlgorithms.Papers.Independent.Information100.P50 (schattenNorm)

open QAlgorithms.Papers.Independent.Information100.P56 (entropy)

open QAlgorithms.Papers.Independent.Information100.P60 (Mat)

open QAlgorithms.Papers.Independent.Information100.P71 (supportPower)

open QAlgorithms (traceRight)

variable {I J : Type} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]

theorem g64d_EF (H : Mat I) (b : ℂ) :
    NormedSpace.exp ((-b) • H) * NormedSpace.exp (b • H) = 1 ∧
    NormedSpace.exp (b • H) * NormedSpace.exp ((-b) • H) = 1 := by
  have h1 : (-b) • H = -(b • H) := by rw [neg_smul]
  rw [h1, Matrix.exp_neg]
  exact ⟨Matrix.nonsing_inv_mul _ ((Matrix.isUnit_iff_isUnit_det _).mp (Matrix.isUnit_exp _)),
    Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).mp (Matrix.isUnit_exp _))⟩

theorem g64d_trace_ext (X Y : Mat I) (h : ∀ B : Mat I, (X * B).trace = (Y * B).trace) : X = Y := by
  ext i j
  have := h (Matrix.single j i 1)
  simpa [Matrix.trace_mul_single] using this

theorem g64d_ctau (H B : Mat I) (beta : ℝ) :
    complexTau H (-Complex.I * (beta : ℂ)) B =
      NormedSpace.exp ((beta : ℂ) • H) * B * NormedSpace.exp ((-(beta : ℂ)) • H) := by
  unfold complexTau
  congr 3
  · ring_nf; rw [Complex.I_sq]; ring_nf
  · ring_nf; rw [Complex.I_sq]; ring_nf

theorem solution [Nonempty I] (H rho : Mat I) (hH : H.IsHermitian)
    (hrho : QAlgorithms.IsDensityMatrix rho) (beta : ℝ) :
    KMS H rho beta ↔ rho = QAlgorithms.gibbsState ((-(beta : ℂ)) • H) := by
  set E := NormedSpace.exp ((-(beta : ℂ)) • H) with hE
  set F := NormedSpace.exp ((beta : ℂ) • H) with hF
  obtain ⟨hEF, hFE⟩ := g64d_EF H (beta : ℂ)
  rw [← hE, ← hF] at hEF hFE
  unfold KMS
  simp only [g64d_ctau]
  rw [← hE, ← hF]
  constructor
  · intro hk
    -- rho * A = E * A * rho * F
    have key : ∀ A : Mat I, rho * A = E * A * rho * F := by
      intro A
      apply g64d_trace_ext
      intro B
      have := hk A B
      calc (rho * A * B).trace = (rho * (A * B)).trace := by rw [mul_assoc]
        _ = (rho * (F * B * E * A)).trace := this
        _ = (E * A * rho * F * B).trace := by
          rw [show rho * (F * B * E * A) = (rho * F * B) * (E * A) by simp only [mul_assoc],
            Matrix.trace_mul_comm]
          simp only [mul_assoc]
    have h1 := key 1
    simp only [mul_one] at h1
    have hcomm : F * rho = rho * F := by
      calc F * rho = F * (E * rho * F) := by rw [← h1]
        _ = rho * F := by rw [← mul_assoc, ← mul_assoc, hFE, one_mul]
    have hcen : ∀ A : Mat I, (rho * F) * A = A * (rho * F) := by
      intro A
      have := congrArg (fun X => F * X) (key A)
      calc rho * F * A = F * (rho * A) := by rw [← hcomm, mul_assoc]
        _ = F * (E * A * rho * F) := this
        _ = A * (rho * F) := by
          rw [show F * (E * A * rho * F) = (F * E) * A * rho * F by simp only [mul_assoc], hFE,
            one_mul, mul_assoc]
    obtain ⟨c, hc⟩ := Matrix.mem_range_scalar_iff_commute_single'.mpr
      (fun i j => (hcen (Matrix.single i j 1)).symm)
    have hrhoE : rho = c • E := by
      calc rho = rho * F * E := by rw [mul_assoc, hFE, mul_one]
        _ = c • E := by rw [← hc]; simp [Matrix.scalar_apply, Matrix.smul_eq_diagonal_mul]
    have htr := hrho.2
    rw [hrhoE, Matrix.trace_smul, smul_eq_mul] at htr
    unfold QAlgorithms.gibbsState
    rw [← hE, hrhoE]
    congr 1
    exact (eq_inv_of_mul_eq_one_left htr).symm ▸ rfl
  · intro hg A B
    rw [hg]
    unfold QAlgorithms.gibbsState
    rw [← hE]
    simp only [Matrix.smul_mul, Matrix.trace_smul]
    congr 1
    calc (E * (A * B)).trace = (B * (E * A)).trace := by
          rw [← mul_assoc, Matrix.trace_mul_comm]
      _ = (E * (F * B * E * A)).trace := by
          rw [show E * (F * B * E * A) = (E * F) * B * (E * A) by simp only [mul_assoc], hEF,
            one_mul]
