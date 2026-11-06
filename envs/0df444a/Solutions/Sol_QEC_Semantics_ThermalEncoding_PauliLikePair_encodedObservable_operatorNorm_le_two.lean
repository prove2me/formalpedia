-- Prove2me | solution 1 for QEC.Semantics.ThermalEncoding.PauliLikePair.encodedObservable_operatorNorm_le_two
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T12:06:03.346249+00:00
-- url     : https://prove2.me/submissions/8b3fd9e2-7234-47a3-bfcd-2f9d3c38ed73

import Definitions.Def_QEC_Semantics_Channels_Core
import Definitions.Def_QEC_Semantics_Entropy_Purification
import Definitions.Def_QEC_Semantics_Channels_Kraus
import Definitions.Def_QEC_Semantics_Core_Qubit
import Mathlib.Analysis.InnerProductSpace.Rayleigh
import Definitions.Def_QEC_Semantics_Dynamics_ThermalEncoding
import Theorems.Thm_QEC_Semantics_ThermalEncoding_conjOperator_operatorNorm_le
import Theorems.Thm_QEC_Semantics_ThermalEncoding_scaledTensorDensity_operatorNorm_le_two

set_option autoImplicit false
noncomputable section
open QEC
open QEC.Semantics
open QEC.Semantics.ThermalEncoding
open Classical
open scoped BigOperators ComplexOrder TensorProduct
variable {H : Type}
variable [NormedAddCommGroup H] [InnerProductSpace Complex H] [FiniteQuantumSystem H]
open QEC.Semantics.ThermalEncoding.PauliLikePair
variable (P : PauliLikePair H)
namespace QEC.Semantics.ThermalEncoding.PauliLikePair
theorem _root_.solution
    (eta : DensityOperator Qubit.QubitSpace) :
    ‖LinearMap.toContinuousLinearMap (P.encodedObservable eta)‖ ≤ 2 := by
  exact
    (conjOperator_operatorNorm_le P.factorization
      (TensorProduct.map ((2 : Complex) • eta.toOperator)
        (1 : Operator P.AuxiliarySpace))).trans
      (scaledTensorDensity_operatorNorm_le_two eta)
end QEC.Semantics.ThermalEncoding.PauliLikePair
