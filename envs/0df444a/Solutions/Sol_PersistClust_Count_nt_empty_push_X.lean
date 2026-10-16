-- Prove2me | solution 1 for PersistClust.Count.nt_empty_push_X
-- status  : ACCEPTED   (prove)
-- author  : @fabianroll
-- created : 2026-10-15T13:29:33.492945+00:00
-- url     : https://prove2.me/submissions/9ffafab1-18a3-484f-b080-c8a67e8f1a7d

import Mathlib
import Definitions.Def_PersistClust_Count_Setting
import Definitions.Def_PersistClust_Count_Diagram
import Definitions.Def_PersistClust_Count_FiltrationLaw
import Definitions.Def_PersistClust_Count_MatchingCensus
import Definitions.Def_PersistClust_Count_MatchingGate

open PersistClust.Count
open scoped ENNReal

/-- Emptyness push (X side, set form): the mirror: if the Y-stage is empty
at level u (with u + eps at least alpha), then the X-stage is empty at
u + eps, via the phi-map. -/
theorem solution {ιX ιY : Type*}
    {stageX : ℝ → Set ιX} {JX : ℝ → ιX → ιX → Prop}
    {stageY : ℝ → Set ιY} {JY : ℝ → ιY → ιY → Prop}
    {α ε : ℝ}
    (φ : ∀ β : ℝ, α ≤ β → comps stageX JX β → comps stageY JY (β - ε))
    {u : ℝ} (hu : α ≤ u + ε) (hY : stageY u = ∅) :
    stageX (u + ε) = ∅ := by
  refine Set.eq_empty_iff_forall_notMem.mpr fun x hx => ?_
  have hC : comps stageX JX (u + ε) := ⟨{z | JX (u + ε) x z}, ⟨x, hx, rfl⟩⟩
  have hD : comps stageY JY ((u + ε) - ε) := φ (u + ε) hu hC
  have hrep : compRep stageY JY ((u + ε) - ε) hD ∈ stageY ((u + ε) - ε) :=
    (compRep_spec stageY JY ((u + ε) - ε) hD).1
  have hstage : stageY ((u + ε) - ε) = ∅ :=
    (congrArg stageY (show (u + ε) - ε = u by ring)).trans hY
  rw [hstage] at hrep
  exact absurd hrep (Set.notMem_empty _)
