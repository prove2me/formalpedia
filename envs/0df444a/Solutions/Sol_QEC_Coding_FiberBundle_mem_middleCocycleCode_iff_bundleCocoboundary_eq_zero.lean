-- Prove2me | solution 1 for QEC.Coding.FiberBundle.mem_middleCocycleCode_iff_bundleCocoboundary_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T06:07:32.275916+00:00
-- url     : https://prove2.me/submissions/32b6dc22-cd53-4058-92ed-84cc905b5a53

import Definitions.Def_QEC_Coding_FiberBundle_CohomologyDistance
import Definitions.Def_QEC_Coding_FiberBundle_CohomologyRepresentatives

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
    (z : Word (ZMod 2)
      (QubitIndex baseZero baseOne fiberZero fiberOne)) :
    z ∈ (chainComplex D).middleCocycleCode.carrier ↔
      bundleCocoboundary D z = 0 := by
  exact (chainComplex D).mem_middleCocycleCode_iff z
end QEC.Coding.FiberBundle
