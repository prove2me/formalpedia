-- Prove2me | solution 1 for QEC.Coding.StabilizerCode.BinaryStabilizerPresentation.encodedQubits_eq_blockLength_sub_generatorRank
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T16:44:19.797089+00:00
-- url     : https://prove2.me/submissions/6650521d-c1cf-4569-a5dd-d4be556c2b82

import Definitions.Def_QEC_Coding_Stabilizer_Distance
import Definitions.Def_QEC_Coding_Stabilizer_Parameters
import Theorems.Thm_QEC_Coding_StabilizerCode_BinaryStabilizerPresentation_logicalPauliDimension_eq_two_mul_blockLength_sub_generatorRank

set_option autoImplicit false
noncomputable section
open QEC
open QEC.Coding
open PauliSymplectic
universe u v
open QEC.Coding.StabilizerCode
variable {ι : Type u} [Fintype ι] [DecidableEq ι]
variable {κ : Type v} [Fintype κ]
open QEC.Coding.StabilizerCode.BinaryStabilizerPresentation
namespace QEC.Coding.StabilizerCode.BinaryStabilizerPresentation
theorem _root_.solution
    (P : BinaryStabilizerPresentation (ι := ι) (κ := κ)) :
    P.encodedQubits = P.blockLength - P.generatorRank := by
  rw [encodedQubits,
    P.logicalPauliDimension_eq_two_mul_blockLength_sub_generatorRank]
  exact Nat.div_eq_of_eq_mul_left (by decide : 0 < 2) (Nat.mul_comm _ _)
end QEC.Coding.StabilizerCode.BinaryStabilizerPresentation
