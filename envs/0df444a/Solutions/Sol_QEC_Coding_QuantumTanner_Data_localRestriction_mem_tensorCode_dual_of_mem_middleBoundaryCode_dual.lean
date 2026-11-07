-- Prove2me | solution 1 for QEC.Coding.QuantumTanner.Data.localRestriction_mem_tensorCode_dual_of_mem_middleBoundaryCode_dual
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T13:22:32.038205+00:00
-- url     : https://prove2.me/submissions/e0b09ae2-b8f1-4041-b7ff-592406958185

import Definitions.Def_QEC_Coding_QuantumTanner_Core
import Definitions.Def_QEC_Coding_CSS_WeightDescent
import Definitions.Def_QEC_Coding_ChainComplex_Duality
import Definitions.Def_QEC_Coding_QuantumTanner_TensorDistance
import Definitions.Def_QEC_Coding_QuantumTanner_Distance
import Theorems.Thm_QEC_Coding_QuantumTanner_LeftRightCayleySquareComplex_wordPairing_localExtension
import Theorems.Thm_QEC_Coding_QuantumTanner_Data_localExtension_mem_middleBoundaryCode

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
    D.complex.localRestriction (g, false) x ∈ (tensorCode D.codeA D.codeB).dual.carrier := by
  refine (LinearCode.mem_dual _ _).2 ?_
  intro c hc
  rw [← D.complex.wordPairing_localExtension (g, false) x c]
  exact D.chainComplex.middleBoundaryCode.orthogonal_of_mem_dual hx
    (D.localExtension_mem_middleBoundaryCode g c hc)
end QEC.Coding.QuantumTanner.Data
