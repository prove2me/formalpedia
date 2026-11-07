-- Prove2me | solution 1 for QEC.Coding.QuantumTanner.Data.activeVertices_false_card_mul_le_of_mem_middleBoundaryCode_dual
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T15:08:43.202251+00:00
-- url     : https://prove2.me/submissions/0fc78eef-7080-4633-99da-bcd98b5cefbc

import Definitions.Def_QEC_Coding_QuantumTanner_Core
import Definitions.Def_QEC_Coding_CSS_WeightDescent
import Definitions.Def_QEC_Coding_ChainComplex_Duality
import Definitions.Def_QEC_Coding_QuantumTanner_TensorDistance
import Definitions.Def_QEC_Coding_QuantumTanner_Distance
import Theorems.Thm_QEC_Coding_QuantumTanner_LeftRightCayleySquareComplex_activeVerticesOnSide_card_mul_le
import Theorems.Thm_QEC_Coding_QuantumTanner_Data_localRestriction_mem_dualTensorCode_of_mem_middleBoundaryCode_dual
import Theorems.Thm_QEC_Coding_QuantumTanner_hammingWeight_ge_min_of_mem_dualTensorCode


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
    (D : Data G A B Square XBasis ZBasis) (dA dB : Nat)
    (hA : ∀ a : Word (ZMod 2) A, a ∈ D.codeA.dual.carrier → a ≠ 0 →
      dA ≤ HammingWeight a)
    (hB : ∀ b : Word (ZMod 2) B, b ∈ D.codeB.dual.carrier → b ≠ 0 →
      dB ≤ HammingWeight b)
    (x : Word (ZMod 2) Square) (hx : x ∈ D.chainComplex.middleBoundaryCode.dual.carrier) :
    min dA dB * (D.complex.activeVerticesOnSide false x).card ≤ 2 * HammingWeight x := by
  apply D.complex.activeVerticesOnSide_card_mul_le false x (min dA dB)
  intro g hne
  exact hammingWeight_ge_min_of_mem_dualTensorCode D.codeA.dual D.codeB.dual dA dB hA hB _
    (D.localRestriction_mem_dualTensorCode_of_mem_middleBoundaryCode_dual x hx g) hne
end QEC.Coding.QuantumTanner.Data
