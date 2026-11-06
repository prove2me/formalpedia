-- Prove2me | solution 2 for QEC.Semantics.DensityOperator.basisMatrixSpectralEntropy_independent
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T20:00:29.049011+00:00
-- url     : https://prove2.me/submissions/fb580fe6-376f-45bb-9c70-7bde80e1c5e9

import Definitions.Def_QEC_Semantics_Core_Definitions
import Definitions.Def_QEC_Semantics_Entropy_FiniteDimensional
import Theorems.Thm_QEC_Semantics_DensityOperator_vonNeumannEntropy_eq_basisMatrixSpectrum

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
    (b c : OrthonormalBasis (Fin (Module.finrank Complex H)) Complex H) :
    (((rho.toOperator.toMatrix b.toBasis b.toBasis).charpoly.roots.map Complex.re).map
        entropyTerm).sum =
      (((rho.toOperator.toMatrix c.toBasis c.toBasis).charpoly.roots.map Complex.re).map
        entropyTerm).sum := by
  rw [<- rho.vonNeumannEntropy_eq_basisMatrixSpectrum b,
    <- rho.vonNeumannEntropy_eq_basisMatrixSpectrum c]
end QEC.Semantics.DensityOperator
