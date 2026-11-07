-- Prove2me | solution 1 for QEC.Coding.QuantumTanner.Data.localRestriction_mem_dualTensorCode_of_mem_firstCoboundaryCheckCode_dual
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T13:29:39.121213+00:00
-- url     : https://prove2.me/submissions/35612dc0-19b3-4c53-a153-f3c8f158df36

import Definitions.Def_QEC_Coding_QuantumTanner_Core
import Definitions.Def_QEC_Coding_CSS_WeightDescent
import Definitions.Def_QEC_Coding_ChainComplex_Duality
import Definitions.Def_QEC_Coding_QuantumTanner_TensorDistance
import Definitions.Def_QEC_Coding_QuantumTanner_Distance
import Theorems.Thm_QEC_Coding_QuantumTanner_Data_localRestriction_mem_tensorCode_dual_of_mem_firstCoboundaryCheckCode_dual
import Theorems.Thm_QEC_Coding_QuantumTanner_tensorCode_dual_dual_carrier_eq


set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.QuantumTanner
open Classical
universe v
open QEC.Coding.QuantumTanner.Data
variable {G A B Square XBasis ZBasis : Type v}
  [Group G] [Fintype G] [Fintype A] [Fintype B] [Fintype Square]
  [Fintype XBasis] [Fintype ZBasis]
namespace QEC.Coding.QuantumTanner.Data
theorem _root_.solution
    (D : Data G A B Square XBasis ZBasis) (x : Word (ZMod 2) Square)
    (hx : x ∈ D.chainComplex.firstCoboundaryCheckCode.dual.carrier) (g : G) :
    D.complex.localRestriction (g, true) x ∈ (dualTensorCode D.codeA D.codeB).carrier := by
  rw [← tensorCode_dual_dual_carrier_eq]
  exact D.localRestriction_mem_tensorCode_dual_of_mem_firstCoboundaryCheckCode_dual x hx g
end QEC.Coding.QuantumTanner.Data
