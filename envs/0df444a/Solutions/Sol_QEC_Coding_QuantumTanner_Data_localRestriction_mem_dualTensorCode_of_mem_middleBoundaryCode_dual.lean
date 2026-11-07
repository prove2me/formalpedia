-- Prove2me | solution 1 for QEC.Coding.QuantumTanner.Data.localRestriction_mem_dualTensorCode_of_mem_middleBoundaryCode_dual
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T13:26:52.781634+00:00
-- url     : https://prove2.me/submissions/cf41686d-a0c0-43fa-b523-8a91fbaa9590

import Definitions.Def_QEC_Coding_QuantumTanner_Core
import Definitions.Def_QEC_Coding_CSS_WeightDescent
import Definitions.Def_QEC_Coding_ChainComplex_Duality
import Definitions.Def_QEC_Coding_QuantumTanner_TensorDistance
import Definitions.Def_QEC_Coding_QuantumTanner_Distance
import Theorems.Thm_QEC_Coding_QuantumTanner_Data_localRestriction_mem_tensorCode_dual_of_mem_middleBoundaryCode_dual
import Theorems.Thm_QEC_Coding_QuantumTanner_tensorCode_dual_carrier_eq


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
    (hx : x ∈ D.chainComplex.middleBoundaryCode.dual.carrier) (g : G) :
    D.complex.localRestriction (g, false) x ∈
      (dualTensorCode D.codeA.dual D.codeB.dual).carrier := by
  rw [← tensorCode_dual_carrier_eq]
  exact D.localRestriction_mem_tensorCode_dual_of_mem_middleBoundaryCode_dual x hx g
end QEC.Coding.QuantumTanner.Data
