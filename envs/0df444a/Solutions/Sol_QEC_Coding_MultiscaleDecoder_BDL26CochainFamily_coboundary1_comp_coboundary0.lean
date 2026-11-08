-- Prove2me | solution 1 for QEC.Coding.MultiscaleDecoder.BDL26CochainFamily.coboundary1_comp_coboundary0
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T13:50:26.331209+00:00
-- url     : https://prove2.me/submissions/17e57e47-94d4-4259-83ea-6bcbd971d835

import Definitions.Def_QEC_Coding_ChainComplex_Cohomology
import Definitions.Def_QEC_Coding_Stabilizer_LocalHamiltonian
import Definitions.Def_QEC_Locality_Graph_Core
import Definitions.Def_QEC_Coding_FourDimensionalToricCode_Decoder_Multiscale
import Theorems.Thm_QEC_Coding_MultiscaleDecoder_BDL26CochainFamily_wordLinearMapTranspose_zero_local
import Theorems.Thm_QEC_Locality_NoEdgeBetween_symm


set_option autoImplicit false
open QEC
open QEC.Coding
open QEC.Coding.MultiscaleDecoder
open scoped BigOperators
universe u v w x y z a
variable {depth : Nat}
open QEC.Coding.MultiscaleDecoder.BDL26CochainFamily
variable {C0 C1 C2 : LevelIndex depth → Type u}
variable [∀ i, Fintype (C0 i)] [∀ i, Fintype (C1 i)] [∀ i, Fintype (C2 i)]
namespace QEC.Coding.MultiscaleDecoder.BDL26CochainFamily
theorem _root_.solution
    (F : BDL26CochainFamily depth C0 C1 C2)
    (i : LevelIndex depth) :
    (F.coboundary1 i).comp (F.coboundary0 i) =
      (0 : F.Cochain0 i →ₗ[BDL26Field] F.Cochain2 i) := by
  calc
    (F.coboundary1 i).comp (F.coboundary0 i) =
        wordLinearMapTranspose ((F.complex i).boundary1.comp
          (F.complex i).boundary2) := by
      symm
      exact wordLinearMapTranspose_comp
        (g := (F.complex i).boundary1) (f := (F.complex i).boundary2)
    _ = wordLinearMapTranspose
        (0 : Word BDL26Field (C2 i) →ₗ[BDL26Field] Word BDL26Field (C0 i)) := by
      exact congrArg wordLinearMapTranspose (F.complex i).boundary_squared
    _ = 0 := wordLinearMapTranspose_zero_local
end QEC.Coding.MultiscaleDecoder.BDL26CochainFamily
