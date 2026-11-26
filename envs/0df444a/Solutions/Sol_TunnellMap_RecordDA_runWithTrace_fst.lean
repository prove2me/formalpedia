-- Prove2me | solution 1 for TunnellMap.RecordDA.runWithTrace_fst
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T16:38:11.388858+00:00
-- url     : https://prove2.me/submissions/a6a709b8-1207-4f4a-bcf1-617b50c7cba0

import Definitions.Def_TunnellMap_KernelPipeline
import Definitions.Def_TunnellMap_RecordTrace
import Theorems.Thm_TunnellMap_RecordDA_stepTrace_stepK

set_option autoImplicit true
open TunnellMap
open TunnellMap.RecordDA
open OrderedGenerator BlockGen
variable {n : ℤ}
namespace TunnellMap.RecordDA
theorem _root_.solution (frames : FrameFamily n) :
    ∀ (fuel : ℕ) (E : DARun n), (runWithTrace frames fuel E).1 = runK frames fuel E := by
  intro fuel
  induction fuel with
  | zero => intro E; rfl
  | succ fuel ih =>
      intro E
      have hmap := stepTrace_stepK frames E
      cases hst : stepTrace frames E with
      | none =>
          have : stepK frames E = none := by rw [← hmap, hst]; rfl
          rw [runWithTrace, hst, runK, this]
      | some p =>
          obtain ⟨ev, E'⟩ := p
          have : stepK frames E = some E' := by rw [← hmap, hst]; rfl
          rw [runWithTrace, hst, runK, this]
          exact ih E'
end TunnellMap.RecordDA
