-- Prove2me | solution 1 for QEC.Coding.FiberBundle.binaryCSSCode_stabilizer_isSourceValidBinary
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T21:50:45.000164+00:00
-- url     : https://prove2.me/submissions/8469340b-c3c5-42da-806c-4734346bcd38

import Definitions.Def_QEC_Coding_QLDPC_SourceValidity
import Mathlib.LinearAlgebra.Matrix.ToLin
import Definitions.Def_QEC_Coding_FiberBundle_Core

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
    (D : Data baseZero baseOne fiberZero fiberOne) :
    (binaryCSSCode D).stabilizer.IsSourceValidBinary := by
  exact (chainComplex D).binaryCSSCode_stabilizer_isSourceValidBinary
end QEC.Coding.FiberBundle
