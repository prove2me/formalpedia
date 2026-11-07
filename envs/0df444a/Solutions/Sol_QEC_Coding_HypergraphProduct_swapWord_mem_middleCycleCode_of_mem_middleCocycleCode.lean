-- Prove2me | solution 1 for QEC.Coding.HypergraphProduct.swapWord_mem_middleCycleCode_of_mem_middleCocycleCode
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T11:20:43.895035+00:00
-- url     : https://prove2.me/submissions/75af0e6e-c492-46b7-9651-26fa8dcdbe4d

import Definitions.Def_QEC_Coding_HypergraphProduct_Distance_Embedding
import Definitions.Def_QEC_Coding_HypergraphProduct_Distance_Duality
import Theorems.Thm_QEC_Coding_HypergraphProduct_boundary1_transposeData_swapWord
import Theorems.Thm_QEC_Coding_HypergraphProduct_chainComplex_boundary1
attribute [local simp] QEC.Coding.HypergraphProduct.chainComplex_boundary1



set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.HypergraphProduct
universe u v
namespace QEC.Coding.HypergraphProduct
theorem _root_.solution
    {rowOne colOne rowTwo colTwo : Type u}
    [Fintype rowOne] [DecidableEq rowOne]
    [Fintype colOne] [DecidableEq colOne]
    [Fintype rowTwo] [DecidableEq rowTwo]
    [Fintype colTwo] [DecidableEq colTwo]
    (D : Data (ZMod 2) rowOne colOne rowTwo colTwo)
    (z : Word (ZMod 2) (QubitIndex rowOne colOne rowTwo colTwo))
    (hz : z ∈ (chainComplex D).middleCocycleCode.carrier) :
    swapWord z ∈ (chainComplex (transposeData D)).middleCycleCode.carrier := by
  rw [(chainComplex (transposeData D)).mem_middleCycleCode_iff]
  rw [chainComplex_boundary1, boundary1_transposeData_swapWord]
  exact ((chainComplex D).mem_middleCocycleCode_iff z).mp hz
end QEC.Coding.HypergraphProduct
