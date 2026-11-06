-- Prove2me | solution 1 for QEC.Coding.FiberBundle.binaryAlgebraicCSSMinimumDistance_of_sector_minima
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T21:50:59.710196+00:00
-- url     : https://prove2.me/submissions/49090aac-8cf1-4419-a560-c20b64fc236d

import Definitions.Def_QEC_Coding_QLDPC_SourceValidity
import Mathlib.LinearAlgebra.Matrix.ToLin
import Definitions.Def_QEC_Coding_FiberBundle_Core
import Theorems.Thm_QEC_Coding_algebraicCSSMinimumDistance_of_sector_minima


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.FiberBundle
universe u
namespace QEC.Coding.FiberBundle
theorem _root_.solution
    {baseZero baseOne fiberZero fiberOne : Type u}
    [Fintype baseZero] [DecidableEq baseZero]
    [Fintype baseOne] [DecidableEq baseOne]
    [Fintype fiberZero] [DecidableEq fiberZero]
    [Fintype fiberOne] [DecidableEq fiberOne]
    (D : Data baseZero baseOne fiberZero fiberOne)
    {dX dZ : Nat}
    (hX : BinaryPureXMinimumDistance D dX)
    (hZ : BinaryPureZMinimumDistance D dZ) :
    BinaryAlgebraicCSSMinimumDistance D (min dX dZ) := by
  exact algebraicCSSMinimumDistance_of_sector_minima hX hZ
end QEC.Coding.FiberBundle
