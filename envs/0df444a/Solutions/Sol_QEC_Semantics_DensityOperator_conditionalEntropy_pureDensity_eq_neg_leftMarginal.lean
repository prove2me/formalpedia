-- Prove2me | solution 1 for QEC.Semantics.DensityOperator.conditionalEntropy_pureDensity_eq_neg_leftMarginal
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T20:02:39.933873+00:00
-- url     : https://prove2.me/submissions/7591e9d6-6056-472f-a9f8-17d626069617

import Definitions.Def_QEC_Semantics_Entropy_FiniteDimensional
import Definitions.Def_QEC_Semantics_ErrorCorrection_QuditSubsystem
import Definitions.Def_QEC_Semantics_Entropy_Purification
import Theorems.Thm_QEC_Semantics_DensityOperator_vonNeumannEntropy_rightMarginal_eq_leftMarginal_pure
import Theorems.Thm_QEC_Semantics_DensityOperator_conditionalEntropy_pureDensity

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
      - (leftMarginal (pureDensity psi hpsi)).vonNeumannEntropy := by
  rw [conditionalEntropy_pureDensity,
    vonNeumannEntropy_rightMarginal_eq_leftMarginal_pure psi hpsi]
end QEC.Semantics.DensityOperator
