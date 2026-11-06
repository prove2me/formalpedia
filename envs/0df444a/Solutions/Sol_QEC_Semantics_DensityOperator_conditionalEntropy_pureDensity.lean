-- Prove2me | solution 1 for QEC.Semantics.DensityOperator.conditionalEntropy_pureDensity
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T12:01:09.82598+00:00
-- url     : https://prove2.me/submissions/207bac35-afd0-464e-aa7c-4011fe3bdffe

import Definitions.Def_QEC_Semantics_Entropy_FiniteDimensional
import Definitions.Def_QEC_Semantics_ErrorCorrection_QuditSubsystem
import Definitions.Def_QEC_Semantics_Entropy_Purification
import Theorems.Thm_QEC_Semantics_DensityOperator_vonNeumannEntropy_pureDensity

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
theorem _root_.solution {K : Type u}
    [NormedAddCommGroup K] [InnerProductSpace Complex K] [FiniteQuantumSystem K]
    (psi : CompositeSystem H K) (hpsi : ‖psi‖ ^ 2 = 1) :
    conditionalEntropy (pureDensity psi hpsi) =
      - (rightMarginal (pureDensity psi hpsi)).vonNeumannEntropy := by
  unfold conditionalEntropy
  rw [vonNeumannEntropy_pureDensity]
  ring
end QEC.Semantics.DensityOperator
