-- Prove2me | solution 1 for QEC.Coding.FiberBundle.add_bundleCoboundary_not_mem_firstCoboundaryCheckCode_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T07:59:51.184926+00:00
-- url     : https://prove2.me/submissions/2a6739db-5990-43aa-8b07-84599b880af9

import Definitions.Def_QEC_Coding_FiberBundle_Distance
import Definitions.Def_QEC_Coding_FiberBundle_RandomBase_Expansion
import Definitions.Def_QEC_Coding_FiberBundle_RandomTwist
import Definitions.Def_QEC_Coding_FiberBundle_CohomologyDistance
import Theorems.Thm_QEC_Coding_FiberBundle_bundleCoboundary_mem_firstCoboundaryCheckCode

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
    (x : Word (ZMod 2) (QubitIndex baseZero baseOne fiberZero fiberOne))
    (u : Word (ZMod 2) (C0Index baseZero fiberZero)) :
    x + bundleCoboundary D u ∉
        (chainComplex D).firstCoboundaryCheckCode.carrier ↔
      x ∉ (chainComplex D).firstCoboundaryCheckCode.carrier := by
  exact not_congr
    ((chainComplex D).firstCoboundaryCheckCode.carrier.add_mem_iff_left
      (bundleCoboundary_mem_firstCoboundaryCheckCode D u))
end QEC.Coding.FiberBundle
