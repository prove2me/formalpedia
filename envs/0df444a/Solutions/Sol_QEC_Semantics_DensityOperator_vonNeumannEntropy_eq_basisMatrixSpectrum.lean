-- Prove2me | solution 1 for QEC.Semantics.DensityOperator.vonNeumannEntropy_eq_basisMatrixSpectrum
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T09:16:54.898297+00:00
-- url     : https://prove2.me/submissions/0c94bea7-0665-4132-b6e8-6207f670da9e

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
theorem _root_.solution
    (rho : DensityOperator H)
    (b : OrthonormalBasis (Fin (Module.finrank Complex H)) Complex H) :
    rho.vonNeumannEntropy =
      (((rho.toOperator.toMatrix b.toBasis b.toBasis).charpoly.roots.map Complex.re).map
        entropyTerm).sum := by
  unfold vonNeumannEntropy finiteSpectrum
  rw [LinearMap.charpoly_toMatrix]
end QEC.Semantics.DensityOperator
