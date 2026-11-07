-- Prove2me | solution 1 for QEC.Coding.FiberBundle.card_c0Shadow_eraseC0Fiber_lt
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T07:49:13.770934+00:00
-- url     : https://prove2.me/submissions/5686ff86-ea5f-48c9-86a5-4bb2e4747419

import Definitions.Def_QEC_Coding_FiberBundle_Distance
import Definitions.Def_QEC_Coding_FiberBundle_RandomBase_Expansion
import Definitions.Def_QEC_Coding_FiberBundle_RandomTwist
import Definitions.Def_QEC_Coding_FiberBundle_CohomologyDistance
import Theorems.Thm_QEC_Coding_FiberBundle_c0Shadow_eraseC0Fiber

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.FiberBundle
universe u
namespace QEC.Coding.FiberBundle
theorem _root_.solution
    {baseZero fiberZero : Type u}
    [Fintype baseZero] [DecidableEq baseZero] [Fintype fiberZero]
    (u : Word (ZMod 2) (C0Index baseZero fiberZero))
    {a : baseZero} (ha : a ∈ c0Shadow u) :
    (c0Shadow (eraseC0Fiber u a)).card < (c0Shadow u).card := by
  rw [c0Shadow_eraseC0Fiber, Finset.card_erase_of_mem ha]
  have hpos : 0 < (c0Shadow u).card :=
    Finset.card_pos.mpr ⟨a, ha⟩
  omega
end QEC.Coding.FiberBundle
