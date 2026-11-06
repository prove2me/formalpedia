-- Prove2me | solution 1 for QEC.Semantics.DensityOperator.diagonalDensity_charpoly
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T11:44:34.696125+00:00
-- url     : https://prove2.me/submissions/b3c28e1d-e4b6-4c1e-b687-1ad974cd83f5

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
namespace QEC.Semantics.DensityOperator
theorem _root_.solution (n : Nat) (p : Fin n -> Real)
    (hp : forall i, 0 <= p i) (hsum : (∑ i, p i) = 1) :
    (diagonalDensity n p hp hsum).toOperator.charpoly =
      (Matrix.diagonal fun i => (p i : Complex)).charpoly := by
  change (Matrix.toLin (EuclideanSpace.basisFun (Fin n) Complex).toBasis
    (EuclideanSpace.basisFun (Fin n) Complex).toBasis
    (Matrix.diagonal fun i => (p i : Complex))).charpoly =
      (Matrix.diagonal fun i => (p i : Complex)).charpoly
  rw [Matrix.charpoly_toLin]
end QEC.Semantics.DensityOperator
