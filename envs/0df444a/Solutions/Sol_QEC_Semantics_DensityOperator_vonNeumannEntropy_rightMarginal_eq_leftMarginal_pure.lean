-- Prove2me | solution 1 for QEC.Semantics.DensityOperator.vonNeumannEntropy_rightMarginal_eq_leftMarginal_pure
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T12:01:21.050171+00:00
-- url     : https://prove2.me/submissions/e801c8ce-62fb-497b-a32d-6d7568465949

import Definitions.Def_QEC_Semantics_Entropy_FiniteDimensional
import Definitions.Def_QEC_Semantics_ErrorCorrection_QuditSubsystem
import Definitions.Def_QEC_Semantics_Entropy_Purification
import Theorems.Thm_QEC_Semantics_DensityOperator_pureMarginals_balanced_charpoly
import Theorems.Thm_QEC_Semantics_DensityOperator_vonNeumannEntropy_eq_of_balanced_charpoly

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
    (rightMarginal (pureDensity psi hpsi)).vonNeumannEntropy =
      (leftMarginal (pureDensity psi hpsi)).vonNeumannEntropy := by
  exact vonNeumannEntropy_eq_of_balanced_charpoly
    (rightMarginal (pureDensity psi hpsi)) (leftMarginal (pureDensity psi hpsi))
    (Module.finrank Complex K) (Module.finrank Complex H)
    (pureMarginals_balanced_charpoly psi hpsi)
end QEC.Semantics.DensityOperator
