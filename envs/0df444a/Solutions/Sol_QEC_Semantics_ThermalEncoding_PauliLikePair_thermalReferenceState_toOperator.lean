-- Prove2me | solution 1 for QEC.Semantics.ThermalEncoding.PauliLikePair.thermalReferenceState_toOperator
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T11:23:26.482891+00:00
-- url     : https://prove2.me/submissions/978a36ac-a072-45f2-94f4-788f6c8fa599

import Definitions.Def_QEC_Semantics_Channels_Core
import Definitions.Def_QEC_Semantics_Entropy_Purification
import Definitions.Def_QEC_Semantics_Channels_Kraus
import Definitions.Def_QEC_Semantics_Core_Qubit
import Mathlib.Analysis.InnerProductSpace.Rayleigh
import Definitions.Def_QEC_Semantics_Dynamics_ThermalEncoding

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
    (sigma : DensityOperator P.AuxiliarySpace) :
    (P.thermalReferenceState sigma).toOperator =
      P.factorization.conjOperator
        (TensorProduct.map ((2 : Complex)⁻¹ • (1 : Operator Qubit.QubitSpace))
          sigma.toOperator) := by
  rfl
end QEC.Semantics.ThermalEncoding.PauliLikePair
