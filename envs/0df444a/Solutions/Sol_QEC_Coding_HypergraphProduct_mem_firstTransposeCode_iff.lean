-- Prove2me | solution 1 for QEC.Coding.HypergraphProduct.mem_firstTransposeCode_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T13:51:50.598209+00:00
-- url     : https://prove2.me/submissions/7c18d364-d005-4824-bfb6-c980a7416715

import Definitions.Def_QEC_Coding_HypergraphProduct_Core
import Definitions.Def_QEC_Coding_CSS_ParityChecks
import Mathlib.LinearAlgebra.Matrix.Rank
import Definitions.Def_QEC_Coding_HypergraphProduct_Parameters

set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.HypergraphProduct
universe u v
namespace QEC.Coding.HypergraphProduct
theorem _root_.solution
    {F : Type v} {rowOne colOne rowTwo colTwo : Type u}
    [Field F] [Fintype F]
    [Fintype rowOne] [DecidableEq rowOne]
    [Fintype colOne] [DecidableEq colOne]
    (D : Data F rowOne colOne rowTwo colTwo) (x : Word F rowOne) :
    x ∈ (firstTransposeCode D).carrier ↔
      Matrix.toLin' D.first.transpose x = 0 := by
  exact mem_parityCheckKernelCode _ _
end QEC.Coding.HypergraphProduct
