-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Next46.P23.fock_trace_determinant
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-20T22:27:37.7491+00:00
-- url     : https://prove2.me/submissions/90eb219c-2475-43ac-bc44-ba6e8e8bfab2

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

theorem g64b_det_one_add {n : Type} [Fintype n] [DecidableEq n] (M : Matrix n n ℂ) :
    Matrix.det (1 + M) = ∑ s : Finset n, (M.submatrix (↑) (↑) : Matrix s s ℂ).det := by
  let D := (Matrix.detRowAlternating : (n → ℂ) [⋀^n]→ₗ[ℂ] ℂ)
  have h1 : Matrix.det (1 + M) = D ((fun i => M i) + (fun i => (1 : Matrix n n ℂ) i)) := by
    rw [add_comm]; rfl
  rw [h1, D.map_add_univ]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [← Matrix.det_piecewise_one_eq_submatrix_det]
  rfl

theorem g64b_minor {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) (S : Finset (Fin n)) :
    Matrix.det (fun i j : Fin S.card =>
      A (S.orderEmbOfFin rfl i) (S.orderEmbOfFin rfl (Fin.cast rfl j))) =
    (A.submatrix (↑) (↑) : Matrix S S ℂ).det := by
  rw [← Matrix.det_submatrix_equiv_self (S.orderIsoOfFin rfl).toEquiv]
  congr 1

theorem solution (n : ℕ) (A : Mat (Fin n)) :
    (fockGamma A).trace = Matrix.det (1+A) := by
  rw [g64b_det_one_add]
  simp only [Matrix.trace, Matrix.diag, fockGamma, dif_pos rfl]
  refine Finset.sum_congr rfl fun S _ => ?_
  exact g64b_minor A S

end
