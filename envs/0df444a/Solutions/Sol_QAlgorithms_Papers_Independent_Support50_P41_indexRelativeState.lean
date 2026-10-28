-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Support50.P41.indexRelativeState
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-24T14:29:16.499541+00:00
-- url     : https://prove2.me/submissions/00baa929-d269-4922-adf7-f55c3c6ae937

import Definitions.Def_QAlgorithms_Papers_Independent_Support50_P41

noncomputable section

open QAlgorithms QAlgorithms.Papers QAlgorithms.Papers.Independent QAlgorithms.Papers.Independent.Support50 QAlgorithms.Papers.Independent.Support50.P41

open QAlgorithms

open QAlgorithms.Entanglement (IsCompletelyPositive)

open QAlgorithms.Papers.Independent.Dependency50.P40 (IsPurification purificationFidelity)

open QAlgorithms.Papers.Independent.Dependency50.P45 (entropyExchange)

open QAlgorithms.Papers.Independent.Information100.P08 (canonicalPurification)

open QAlgorithms.Papers.Independent.Information100.P34 (choi dephasing)

open QAlgorithms.Papers.Independent.Dependency50.P38 (vectorizeInputFirst)

open QAlgorithms.Papers.Independent.Gap20.P06 (dilationChannel environmentOutput dilatedVector)

open QAlgorithms.Papers.Independent.Information100.P50 (complementaryMap)

open QAlgorithms.Papers.Independent.Renew46.P43 (IsCountablePOVM classicalKLTerm countableEntropy)

open scoped Matrix ComplexConjugate ComplexOrder ENNReal

attribute [local instance] Classical.propDecidable Classical.decEq

-- The accepted generic dilation functions fix classical equality on each factor.
-- Match that instance for Fin before forming their product unitary groups.

local instance (priority := 2000) (n : ℕ) : DecidableEq (Fin n) := Classical.decEq _

/-- PDF pp.31--32: inverse conjugate-linear index correspondence, normalization and unit-vector projector identity. -/
theorem solution {d : ℕ} [NeZero d] :
    (∀ v : EuclideanSpace ℂ (Fin d), indexState (indexState v) = v ∧
      relativeVector (indexState v) (omegaTilde d) = v ∧
      relativeVector (indexState v) (finiteMaxEntangled (Fin d)) = ((Real.sqrt d)⁻¹ : ℂ) • v) ∧
    (∀ (v w : EuclideanSpace ℂ (Fin d)) (z t : ℂ),
      indexState (z • v + t • w) = conj z • indexState v + conj t • indexState w) ∧
    (∀ v : EuclideanSpace ℂ (Fin d), IsState v →
      Matrix.kronecker (pureDensity (indexState v)) (pureDensity v) =
        conjSuperop (Matrix.kronecker (pureDensity (indexState v))
          (1 : Matrix (Fin d) (Fin d) ℂ)) (pureDensity (omegaTilde d))) ∧
    ‖omegaTilde d‖^2 = (d : ℝ) := by
  refine ⟨fun v => ⟨?_, ?_, ?_⟩, ?_, ?_, ?_⟩
  · ext i; simp [indexState]
  · ext j; simp [relativeVector, indexState, omegaTilde]
  · ext j; simp [relativeVector, indexState, finiteMaxEntangled, mul_comm]
  · intro v w z t; ext i; simp [indexState]
  · intro v _
    ext ⟨a, b⟩ ⟨a', b'⟩
    simp only [conjSuperop, Matrix.mul_apply, Matrix.kronecker, Matrix.kroneckerMap_apply,
      pureDensity, indexState, omegaTilde, Matrix.of_apply, Matrix.conjTranspose_apply,
      Fintype.sum_prod_type, Matrix.one_apply]
    simp [Finset.sum_ite_eq, Finset.sum_ite_eq', ite_and, apply_ite, Finset.mul_sum, Finset.sum_mul]
    ring
  · rw [EuclideanSpace.norm_sq_eq]
    simp [omegaTilde, Fintype.sum_prod_type, apply_ite]
    rw [Finset.card_filter, Fintype.sum_prod_type]
    simp


end

