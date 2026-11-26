-- Prove2me | solution 1 for TunnellMap.RecordDA.stepTrace_generator_advance
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T17:33:08.120794+00:00
-- url     : https://prove2.me/submissions/aec436cb-916d-455d-a76b-6f04698063c7

import Definitions.Def_TunnellMap_KernelPipeline
import Definitions.Def_TunnellMap_RecordTrace
import Theorems.Thm_TunnellMap_RecordDA_stepTrace_shape

set_option autoImplicit true
open TunnellMap
open TunnellMap.RecordDA
open OrderedGenerator BlockGen
variable {n : ℤ}
namespace TunnellMap.RecordDA
theorem _root_.solution (frames : FrameFamily n) {E : DARun n}
    {ev : DAEvent n} {E' : DARun n} (h : stepTrace frames E = some (ev, E')) :
    ∃ g, BlockGen.advanceK ev.proposer (frames ev.proposer) (E.gen ev.proposer) =
        some (⟨ev.key, ev.target, ev.sign⟩, g) ∧
      E'.gen = Function.update E.gen ev.proposer g := by
  obtain ⟨s, rest, g, -, -, hadv, hprop, hgen, -⟩ := stepTrace_shape frames h
  exact ⟨g, by rw [hprop]; exact hadv, by rw [hprop]; exact hgen⟩
end TunnellMap.RecordDA
