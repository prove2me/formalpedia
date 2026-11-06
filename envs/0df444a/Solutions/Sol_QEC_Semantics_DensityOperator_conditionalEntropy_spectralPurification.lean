-- Prove2me | solution 1 for QEC.Semantics.DensityOperator.conditionalEntropy_spectralPurification
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T20:02:43.554111+00:00
-- url     : https://prove2.me/submissions/d0a58f43-1d9d-4ddc-a8b3-5080cb74bad4

import Definitions.Def_QEC_Semantics_Entropy_FiniteDimensional
import Definitions.Def_QEC_Semantics_ErrorCorrection_QuditSubsystem
import Definitions.Def_QEC_Semantics_Entropy_Purification
import Theorems.Thm_QEC_Semantics_DensityOperator_conditionalEntropy_pureDensity
import Theorems.Thm_QEC_Semantics_DensityOperator_rightMarginal_spectralPurification_eq

set_option autoImplicit false
universe u
open QEC
open QEC.Semantics
open scoped BigOperators ComplexOrder TensorProduct
noncomputable section
open QEC.Semantics.DensityOperator
variable {H : Type u}
variable [NormedAddCommGroup H] [InnerProductSpace Complex H] [FiniteQuantumSystem H]
namespace QEC.Semantics.DensityOperator
theorem _root_.solution (rho : DensityOperator H) :
    conditionalEntropy (spectralPurification rho) = -rho.vonNeumannEntropy := by
  calc
    conditionalEntropy (spectralPurification rho) =
      - (rightMarginal (spectralPurification rho)).vonNeumannEntropy := by
        exact conditionalEntropy_pureDensity _ _
    _ = -rho.vonNeumannEntropy := by rw [rightMarginal_spectralPurification_eq]
end QEC.Semantics.DensityOperator
