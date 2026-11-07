-- Prove2me | solution 1 for QEC.Coding.QuantumTanner.Data.localRestriction_mem_tensorCode_dual_of_mem_firstCoboundaryCheckCode_dual
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T13:22:54.708378+00:00
-- url     : https://prove2.me/submissions/c46948d7-b183-4882-981e-b4d2101c8df8

import Definitions.Def_QEC_Coding_QuantumTanner_Core
import Definitions.Def_QEC_Coding_CSS_WeightDescent
import Definitions.Def_QEC_Coding_ChainComplex_Duality
import Definitions.Def_QEC_Coding_QuantumTanner_TensorDistance
import Definitions.Def_QEC_Coding_QuantumTanner_Distance
import Theorems.Thm_QEC_Coding_QuantumTanner_LeftRightCayleySquareComplex_wordPairing_localExtension
import Theorems.Thm_QEC_Coding_QuantumTanner_Data_localExtension_mem_firstCoboundaryCheckCode

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
    D.complex.localRestriction (g, true) x ∈
      (tensorCode D.codeA.dual D.codeB.dual).dual.carrier := by
  refine (LinearCode.mem_dual _ _).2 ?_
  intro c hc
  rw [← D.complex.wordPairing_localExtension (g, true) x c]
  exact D.chainComplex.firstCoboundaryCheckCode.orthogonal_of_mem_dual hx
    (D.localExtension_mem_firstCoboundaryCheckCode g c hc)
end QEC.Coding.QuantumTanner.Data
