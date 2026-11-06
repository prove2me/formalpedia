-- Prove2me | solution 1 for QEC.Coding.HypergraphProduct.mem_secondTransposeCode_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T13:51:51.291213+00:00
-- url     : https://prove2.me/submissions/a720a299-a15e-404a-a724-ed9d36bc0d6d

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
    (D : Data F rowOne colOne rowTwo colTwo) (x : Word F rowTwo) :
    x ∈ (secondTransposeCode D).carrier ↔
      Matrix.toLin' D.second.transpose x = 0 := by
  exact mem_parityCheckKernelCode _ _
end QEC.Coding.HypergraphProduct
