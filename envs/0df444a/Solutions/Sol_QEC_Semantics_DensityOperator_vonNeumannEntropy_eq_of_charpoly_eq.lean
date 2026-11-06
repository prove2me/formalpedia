-- Prove2me | solution 1 for QEC.Semantics.DensityOperator.vonNeumannEntropy_eq_of_charpoly_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T11:44:28.009483+00:00
-- url     : https://prove2.me/submissions/4fa35256-de95-4687-b11a-b180e8974370

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
theorem _root_.solution {K : Type u}
    [NormedAddCommGroup K] [InnerProductSpace Complex K] [FiniteQuantumSystem K]
    (rho : DensityOperator H) (sigma : DensityOperator K)
    (hcharpoly : rho.toOperator.charpoly = sigma.toOperator.charpoly) :
    rho.vonNeumannEntropy = sigma.vonNeumannEntropy := by
  unfold vonNeumannEntropy finiteSpectrum
  rw [hcharpoly]
end QEC.Semantics.DensityOperator
