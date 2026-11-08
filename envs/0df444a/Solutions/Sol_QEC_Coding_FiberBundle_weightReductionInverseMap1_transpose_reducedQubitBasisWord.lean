-- Prove2me | solution 1 for QEC.Coding.FiberBundle.weightReductionInverseMap1_transpose_reducedQubitBasisWord
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T09:15:09.936755+00:00
-- url     : https://prove2.me/submissions/ec44abc6-6faa-4227-b706-d8f7d3014e76

import Definitions.Def_QEC_Coding_FiberBundle_WeightReduction
import Definitions.Def_QEC_Coding_ChainComplex_HomotopyDistance
import Definitions.Def_QEC_Coding_FiberBundle_ExplicitFamily_HomologyDimension
import Definitions.Def_QEC_Coding_FiberBundle_WeightReductionDistance
import Theorems.Thm_QEC_Coding_ClassicalWeightReduction_wordLinearMapTranspose_linearMapOfBasisImages_single


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.FiberBundle
open scoped BigOperators
universe u
variable {baseZero baseOne fiberZero fiberOne : Type u}
variable [Fintype baseZero] [DecidableEq baseZero]
variable [Fintype baseOne] [DecidableEq baseOne]
variable [Fintype fiberZero] [DecidableEq fiberZero]
variable [Fintype fiberOne] [DecidableEq fiberOne]
variable (D : Data baseZero baseOne fiberZero fiberOne)
local notation "R" => baseSupportRelation D
namespace QEC.Coding.FiberBundle
theorem _root_.solution
    (h : ClassicalWeightReduction.HasNoIsolatedVertices R)
    (q : QubitIndex
      (ClassicalWeightReduction.WeightReducedCheck R)
      (ClassicalWeightReduction.WeightReducedBit R)
      fiberZero fiberOne) :
    wordLinearMapTranspose (weightReductionInverseMap1 D h)
        (reducedQubitBasisWord D q) =
      fun source : QubitIndex baseZero baseOne fiberZero fiberOne =>
        match source, q with
        | Sum.inl bi, Sum.inl target' =>
            weightReductionInverseBaseOneBasis D bi.1 bi.2 target'
        | Sum.inr aj, Sum.inr target' =>
            weightReductionInverseBaseZeroOneBasis D h aj.1 aj.2 target'
        | _, _ => 0 := by
  classical
  unfold reducedQubitBasisWord weightReductionInverseMap1
  rw [ClassicalWeightReduction.wordLinearMapTranspose_linearMapOfBasisImages_single]
  rfl
end QEC.Coding.FiberBundle
