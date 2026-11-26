-- Prove2me | solution 1 for TunnellMap.RecordDA.oneBlockAll_step
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T15:59:46.501594+00:00
-- url     : https://prove2.me/submissions/7ef45772-1789-4904-9d2c-a3dc22b56523

import Definitions.Def_TunnellMap_BlockGeneratorState
import Definitions.Def_TunnellMap_ResidualDeferredAcceptance
import Definitions.Def_TunnellMap_RecordDeferredAcceptance
import Theorems.Thm_TunnellMap_BlockGen_oneBlock_advance


set_option autoImplicit true
open TunnellMap
open TunnellMap.RecordDA
open OrderedGenerator BlockGen
variable {n : ℤ}
variable {frames : FrameFamily n} {E : DARun n} {s old : BResidual n}
  {rest : List (BResidual n)} {r rold : IncidentRecord} {g : GenState}
namespace TunnellMap.RecordDA
theorem _root_.solution (frames : FrameFamily n) {E E' : DARun n}
    (hE : OneBlockAll frames E) (h : step frames E = some E') :
    OneBlockAll frames E' := by
  obtain ⟨s, rest, r, g, hq, hs, hadv, hsrc, hgen⟩ := step_shape h
  intro x
  rw [hgen]
  by_cases hx : x = s
  · subst x
    rw [Function.update_self]
    exact oneBlock_advance (frames s) (hE s) hadv
  · rw [Function.update_of_ne hx]
    exact hE x
end TunnellMap.RecordDA
