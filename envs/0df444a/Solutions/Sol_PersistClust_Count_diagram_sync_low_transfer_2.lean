-- Prove2me | solution 2 for PersistClust.Count.diagram_sync_low_transfer
-- status  : ACCEPTED   (prove)
-- author  : @fabianroll
-- created : 2026-10-12T18:19:27.189703+00:00
-- url     : https://prove2.me/submissions/98e453c7-5340-4653-befa-10a223b4afd6

import Mathlib
import Definitions.Def_PersistClust_Count_Setting
import Definitions.Def_PersistClust_Count_Diagram
import Definitions.Def_PersistClust_Count_FiltrationLaw
import Definitions.Def_PersistClust_Count_MatchingCensus

open PersistClust.Count
open scoped ENNReal

/-- Sync-low transfer (equal-argument descent of the interleaving square (i')):
two X-cells whose descents co-merge into the SAME component E at level delta
have interleaving images that descend to the SAME Y-cell at level delta - eps.
Reading delta as a merge level: co-merging image threads are already one
class by delta - eps, so an image merge level is at least delta - eps. -/
theorem solution {ιX ιY : Type*}
    {stageX : ℝ → Set ιX} {JX : ℝ → ιX → ιX → Prop}
    {stageY : ℝ → Set ιY} {JY : ℝ → ιY → ιY → Prop}
    (hLawX : FiltrationLaw stageX JX) (hLawY : FiltrationLaw stageY JY)
    {α ε : ℝ}
    (φ : ∀ β : ℝ, α ≤ β → comps stageX JX β → comps stageY JY (β - ε))
    (hSq1 : ∀ (β β' : ℝ) (hβ : α ≤ β) (hβ' : α ≤ β') (hle : β ≤ β')
        (x : comps stageX JX β'),
      φ β hβ (structMap hLawX hle x) =
        structMap hLawY (show β - ε ≤ β' - ε by linarith) (φ β' hβ' x))
    {δ u : ℝ} (hδ : α ≤ δ) (hu : α ≤ u) (hle : δ ≤ u)
    (C : comps stageX JX u) (E : comps stageX JX δ)
    (hmerge : structMap hLawX hle C = E) :
    structMap hLawY (show δ - ε ≤ u - ε by linarith) (φ u hu C) = φ δ hδ E := by
  have h := hSq1 δ u hδ hu hle C
  rw [hmerge] at h
  exact h.symm
