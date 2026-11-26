-- Prove2me | solution 1 for TunnellMap.RecordDA.genStarted_step
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T16:39:00.778517+00:00
-- url     : https://prove2.me/submissions/a2f689f2-f79b-4c0d-94b7-b138c213baa7

import Definitions.Def_TunnellMap_KernelGenerator
import Definitions.Def_TunnellMap_ComputablePipeline
import Definitions.Def_TunnellMap_KernelPipeline
import Theorems.Thm_TunnellMap_BlockGen_advance_nextBlock_pos

set_option autoImplicit true
open TunnellMap
open TunnellMap.RecordDA
open OrderedGenerator BlockGen
variable {n : ℤ}
namespace TunnellMap.RecordDA
theorem _root_.solution {frames : FrameFamily n} {E E' : DARun n}
    (hE : GenStarted E) (h : step frames E = some E') : GenStarted E' := by
  obtain ⟨s, rest, r, g, hq, hs, hadv, hsrc, hgen⟩ := step_shape h
  intro x
  rw [hgen]
  by_cases hx : x = s
  · subst x
    rw [Function.update_self]
    exact advance_nextBlock_pos (frames s) (hE s) hadv
  · rw [Function.update_of_ne hx]
    exact hE x
end TunnellMap.RecordDA
