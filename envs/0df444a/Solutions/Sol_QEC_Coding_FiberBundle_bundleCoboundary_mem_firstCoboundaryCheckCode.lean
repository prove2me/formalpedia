-- Prove2me | solution 1 for QEC.Coding.FiberBundle.bundleCoboundary_mem_firstCoboundaryCheckCode
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T05:55:58.312303+00:00
-- url     : https://prove2.me/submissions/3efdfa3e-0c27-4580-a671-e74b69620144

import Definitions.Def_QEC_Coding_FiberBundle_Distance
import Definitions.Def_QEC_Coding_FiberBundle_RandomBase_Expansion
import Definitions.Def_QEC_Coding_FiberBundle_RandomTwist
import Definitions.Def_QEC_Coding_FiberBundle_CohomologyDistance

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
    (u : Word (ZMod 2) (C0Index baseZero fiberZero)) :
    bundleCoboundary D u ∈
      (chainComplex D).firstCoboundaryCheckCode.carrier := by
  rw [ChainComplexData.mem_firstCoboundaryCheckCode_iff]
  exact ⟨u, rfl⟩
end QEC.Coding.FiberBundle
