-- Prove2me | solution 1 for PersistClust.Count.nt_empty_push_Y
-- status  : ACCEPTED   (prove)
-- author  : @fabianroll
-- created : 2026-10-15T13:27:44.330144+00:00
-- url     : https://prove2.me/submissions/4011af1a-7576-4552-a972-accfec9337f5

import Mathlib
import Definitions.Def_PersistClust_Count_Setting
import Definitions.Def_PersistClust_Count_Diagram
import Definitions.Def_PersistClust_Count_FiltrationLaw
import Definitions.Def_PersistClust_Count_MatchingCensus
import Definitions.Def_PersistClust_Count_MatchingGate

open PersistClust.Count
open scoped ENNReal

/-- Emptyness push (Y side, set form): if the X-stage is empty at level v
(with v + eps at least alpha), then the Y-stage is empty at v + eps. A
point y of the Y-stage at v + eps spans a Y-component, whose
psi-pullback lands in the X-stage at v by the eps-shift arithmetic --
contradicting the emptyness. -/
theorem solution {ιX ιY : Type*}
    {stageX : ℝ → Set ιX} {JX : ℝ → ιX → ιX → Prop}
    {stageY : ℝ → Set ιY} {JY : ℝ → ιY → ιY → Prop}
    {α ε : ℝ}
    (ψ : ∀ β : ℝ, α ≤ β → comps stageY JY β → comps stageX JX (β - ε))
    {v : ℝ} (hv : α ≤ v + ε) (hX : stageX v = ∅) :
    stageY (v + ε) = ∅ := by
  refine Set.eq_empty_iff_forall_notMem.mpr fun y hy => ?_
  have hC : comps stageY JY (v + ε) := ⟨{z | JY (v + ε) y z}, ⟨y, hy, rfl⟩⟩
  have hD : comps stageX JX ((v + ε) - ε) := ψ (v + ε) hv hC
  have hrep : compRep stageX JX ((v + ε) - ε) hD ∈ stageX ((v + ε) - ε) :=
    (compRep_spec stageX JX ((v + ε) - ε) hD).1
  have hstage : stageX ((v + ε) - ε) = ∅ :=
    (congrArg stageX (show (v + ε) - ε = v by ring)).trans hX
  rw [hstage] at hrep
  exact absurd hrep (Set.notMem_empty _)
