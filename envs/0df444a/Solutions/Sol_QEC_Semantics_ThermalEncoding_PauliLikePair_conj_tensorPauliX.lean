-- Prove2me | solution 1 for QEC.Semantics.ThermalEncoding.PauliLikePair.conj_tensorPauliX
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T11:59:34.846597+00:00
-- url     : https://prove2.me/submissions/f51bc5a8-905a-455e-acc9-95f3463f9610

import Definitions.Def_QEC_Semantics_Channels_Core
import Definitions.Def_QEC_Semantics_Entropy_Purification
import Definitions.Def_QEC_Semantics_Channels_Kraus
import Definitions.Def_QEC_Semantics_Core_Qubit
import Mathlib.Analysis.InnerProductSpace.Rayleigh
import Definitions.Def_QEC_Semantics_Dynamics_ThermalEncoding
import Theorems.Thm_QEC_Semantics_ThermalEncoding_PauliLikePair_factorization_intertwines_x

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
theorem _root_.solution :
    P.factorization.conjOperator P.tensorPauliX = P.x := by
  apply LinearMap.ext
  intro h
  rw [UnitaryTransport.conjOperator_apply]
  exact (P.factorization_intertwines_x
    (P.factorization.toLinearEquiv.symm h)).trans
      (congrArg P.x (P.factorization.toLinearEquiv.apply_symm_apply h))
end QEC.Semantics.ThermalEncoding.PauliLikePair
