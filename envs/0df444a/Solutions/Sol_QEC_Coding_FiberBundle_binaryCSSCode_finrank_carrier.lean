-- Prove2me | solution 1 for QEC.Coding.FiberBundle.binaryCSSCode_finrank_carrier
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T21:50:48.452512+00:00
-- url     : https://prove2.me/submissions/3e0625b0-c9c0-44a7-bbf0-6cd33f115d40

import Definitions.Def_QEC_Coding_QLDPC_SourceValidity
import Mathlib.LinearAlgebra.Matrix.ToLin
import Definitions.Def_QEC_Coding_FiberBundle_Core
import Theorems.Thm_QEC_Coding_ChainComplexData_binaryCSSCode_finrank_stabilizer_code_carrier_eq_pow_finrank_middleHomology


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
    Module.finrank Complex (binaryCSSCode D).stabilizer.code.carrier =
      2 ^ Module.finrank (ZMod 2) (chainComplex D).middleHomology := by
  exact
    QEC.Coding.ChainComplexData.binaryCSSCode_finrank_stabilizer_code_carrier_eq_pow_finrank_middleHomology
      (chainComplex D)
end QEC.Coding.FiberBundle
