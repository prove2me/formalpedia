-- Prove2me | solution 1 for QEC.Coding.QuantumTanner.tensorCode_dual_carrier_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T13:24:46.221548+00:00
-- url     : https://prove2.me/submissions/dcf8203a-2b5d-4d29-a126-3577dfab9810

import Definitions.Def_QEC_Coding_QuantumTanner_Core
import Definitions.Def_QEC_Coding_Core_Duality
import Definitions.Def_QEC_Coding_QuantumTanner_TensorDuality
import Theorems.Thm_QEC_Coding_QuantumTanner_columnCode_dual_carrier_eq
import Theorems.Thm_QEC_Coding_QuantumTanner_rowCode_dual_carrier_eq
import Theorems.Thm_QEC_Coding_LinearCode_dual_inf_carrier_eq


set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.QuantumTanner
open Classical
universe u v
variable {F : Type u} {A B : Type v} [Field F] [Fintype F] [Fintype A] [Fintype B]
namespace QEC.Coding.QuantumTanner
theorem _root_.solution (CA : LinearCode F A) (CB : LinearCode F B) :
    (tensorCode CA CB).dual.carrier = (dualTensorCode CA.dual CB.dual).carrier := by
  change ({ carrier := (columnCode CA).carrier ⊓ (rowCode CB).carrier } :
    LinearCode F (A × B)).dual.carrier = _
  rw [LinearCode.dual_inf_carrier_eq, columnCode_dual_carrier_eq, rowCode_dual_carrier_eq]
  rfl
end QEC.Coding.QuantumTanner
