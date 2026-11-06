-- Prove2me | solution 1 for QEC.Semantics.DensityOperator.vonNeumannEntropy_diagOneZero
-- status  : ACCEPTED   (prove)
-- author  : @nonlocally
-- created : 2026-11-05T18:43:01.514205+00:00
-- url     : https://prove2.me/submissions/f0804cec-6014-40d2-91f1-6215b50555e4

import Definitions.Def_QEC_Semantics_Core_Definitions
import Definitions.Def_QEC_Semantics_Entropy_FiniteDimensional
set_option autoImplicit false
universe u
open QEC
open QEC.Semantics
open scoped BigOperators ComplexOrder
noncomputable section
open QEC.Semantics.DensityOperator
variable {H : Type u}
variable [NormedAddCommGroup H] [InnerProductSpace Complex H] [FiniteQuantumSystem H]

private theorem diagonalDensity_charpoly_aux (n : Nat) (p : Fin n -> Real)
    (hp : forall i, 0 <= p i) (hsum : (∑ i, p i) = 1) :
    (diagonalDensity n p hp hsum).toOperator.charpoly =
      (Matrix.diagonal fun i => (p i : Complex)).charpoly := by
  change (Matrix.toLin (EuclideanSpace.basisFun (Fin n) Complex).toBasis
    (EuclideanSpace.basisFun (Fin n) Complex).toBasis
    (Matrix.diagonal fun i => (p i : Complex))).charpoly =
      (Matrix.diagonal fun i => (p i : Complex)).charpoly
  rw [Matrix.charpoly_toLin]

private theorem vonNeumannEntropy_diagonalDensity_aux (n : Nat) (p : Fin n -> Real)
    (hp : forall i, 0 <= p i) (hsum : (∑ i, p i) = 1) :
    (diagonalDensity n p hp hsum).vonNeumannEntropy = ∑ i, entropyTerm (p i) := by
  unfold vonNeumannEntropy finiteSpectrum
  rw [diagonalDensity_charpoly_aux]
  rw [Matrix.charpoly_diagonal]
  rw [Polynomial.roots_prod _ _ (by
    simp [Finset.prod_ne_zero_iff, Polynomial.X_sub_C_ne_zero])]
  simp [Function.comp_def, List.sum_ofFn]

theorem solution : diagOneZero.vonNeumannEntropy = 0 := by
  rw [diagOneZero, vonNeumannEntropy_diagonalDensity_aux]
  rw [Fin.sum_univ_two]
  simp
