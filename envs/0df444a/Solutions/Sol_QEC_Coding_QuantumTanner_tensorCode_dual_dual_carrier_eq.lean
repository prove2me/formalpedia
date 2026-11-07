-- Prove2me | solution 1 for QEC.Coding.QuantumTanner.tensorCode_dual_dual_carrier_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T13:26:48.606732+00:00
-- url     : https://prove2.me/submissions/e125e790-dc30-4a01-8d3b-7fa0b6067d60

import Definitions.Def_QEC_Coding_QuantumTanner_Core
import Definitions.Def_QEC_Coding_Core_Duality
import Definitions.Def_QEC_Coding_QuantumTanner_TensorDuality
import Theorems.Thm_QEC_Coding_QuantumTanner_tensorCode_dual_carrier_eq
import Theorems.Thm_QEC_Coding_LinearCode_dual_dual_eq


set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.QuantumTanner
open Classical
universe u v
variable {F : Type u} {A B : Type v} [Field F] [Fintype F] [Fintype A] [Fintype B]
namespace QEC.Coding.QuantumTanner
theorem _root_.solution (CA : LinearCode F A) (CB : LinearCode F B) :
    (tensorCode CA.dual CB.dual).dual.carrier = (dualTensorCode CA CB).carrier := by
  rw [tensorCode_dual_carrier_eq, LinearCode.dual_dual_eq, LinearCode.dual_dual_eq]
end QEC.Coding.QuantumTanner
