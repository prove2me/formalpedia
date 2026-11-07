-- Prove2me | solution 1 for QEC.Coding.HypergraphProduct.mem_middleBoundaryCode_of_supportRestrictedWord_mem
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T11:20:41.138144+00:00
-- url     : https://prove2.me/submissions/80ac7259-fdde-4949-afaa-8d5e5a2a6b52

import Definitions.Def_QEC_Coding_HypergraphProduct_Distance_Restriction
import Definitions.Def_QEC_Coding_HypergraphProduct_Distance_Embedding
import Theorems.Thm_QEC_Coding_HypergraphProduct_boundary2_supportExtendedWitness

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
    (hz : supportRestrictedWord z ∈
      (chainComplex (supportRestrictedData D z)).middleBoundaryCode.carrier) :
    z ∈ (chainComplex D).middleBoundaryCode.carrier := by
  change ∃ w, boundary2 (supportRestrictedData D z) w =
    supportRestrictedWord z at hz
  change ∃ w, boundary2 D w = z
  rcases hz with ⟨w, hw⟩
  exact ⟨supportExtendedWitness z w,
    boundary2_supportExtendedWitness D z w hw⟩
end QEC.Coding.HypergraphProduct
