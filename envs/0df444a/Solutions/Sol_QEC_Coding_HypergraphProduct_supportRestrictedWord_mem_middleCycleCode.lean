-- Prove2me | solution 1 for QEC.Coding.HypergraphProduct.supportRestrictedWord_mem_middleCycleCode
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T11:20:35.887168+00:00
-- url     : https://prove2.me/submissions/fe285353-6263-4f37-8b29-aada4d8f9706

import Definitions.Def_QEC_Coding_HypergraphProduct_Distance_Restriction
import Definitions.Def_QEC_Coding_HypergraphProduct_Distance_Embedding
import Theorems.Thm_QEC_Coding_HypergraphProduct_boundary1_supportRestrictedWord

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
    (hz : z ∈ (chainComplex D).middleCycleCode.carrier) :
    supportRestrictedWord z ∈
      (chainComplex (supportRestrictedData D z)).middleCycleCode.carrier := by
  change boundary1 D z = 0 at hz
  change boundary1 (supportRestrictedData D z) (supportRestrictedWord z) = 0
  rw [boundary1_supportRestrictedWord]
  exact hz
end QEC.Coding.HypergraphProduct
