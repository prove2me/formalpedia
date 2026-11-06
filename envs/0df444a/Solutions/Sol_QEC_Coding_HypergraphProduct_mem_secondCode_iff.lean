-- Prove2me | solution 1 for QEC.Coding.HypergraphProduct.mem_secondCode_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T13:51:39.957366+00:00
-- url     : https://prove2.me/submissions/efa13764-9dd9-4826-b66f-64ac052c3ecf

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
    [Fintype rowTwo] [DecidableEq rowTwo]
    [Fintype colTwo] [DecidableEq colTwo]
    (D : Data F rowOne colOne rowTwo colTwo) (x : Word F colTwo) :
    x ∈ (secondCode D).carrier ↔ Matrix.toLin' D.second x = 0 := by
  exact mem_parityCheckKernelCode _ _
end QEC.Coding.HypergraphProduct
