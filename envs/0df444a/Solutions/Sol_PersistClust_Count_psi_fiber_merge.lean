-- Prove2me | solution 1 for PersistClust.Count.psi_fiber_merge
-- status  : ACCEPTED   (prove)
-- author  : @fabianroll
-- created : 2026-10-15T13:33:22.162561+00:00
-- url     : https://prove2.me/submissions/4c8cc5e8-161a-4377-9e08-ae40cc84cd92

import Mathlib
import Definitions.Def_PersistClust_Count_Setting
import Definitions.Def_PersistClust_Count_Diagram
import Definitions.Def_PersistClust_Count_FiltrationLaw
import Definitions.Def_PersistClust_Count_MatchingCensus
import Definitions.Def_PersistClust_Count_MatchingGate

open PersistClust.Count
open scoped ENNReal

/-- Psi-fiber merge (interleaving square iii'): the sides-swapped mirror: if
psi identifies two Y-cells y and y' at a common level beta, then their
2eps-descent structure maps agree -- applying phi to the psi-equality
and rewriting both sides through the square law hSq3. -/
theorem solution {ιX ιY : Type*}
    {stageX : ℝ → Set ιX} {JX : ℝ → ιX → ιX → Prop} {stageY : ℝ → Set ιY} {JY : ℝ → ιY → ιY → Prop}
    (hLawX : FiltrationLaw stageX JX) (hLawY : FiltrationLaw stageY JY)
    {α ε : ℝ} (hε : 0 ≤ ε)
    (φ : ∀ β : ℝ, α ≤ β → comps stageX JX β → comps stageY JY (β - ε))
    (ψ : ∀ β : ℝ, α ≤ β → comps stageY JY β → comps stageX JX (β - ε))
    (hSq3 : ∀ (β : ℝ) (hβ : α ≤ β) (hβε : α ≤ β - ε) (y : comps stageY JY β),
      φ (β - ε) hβε (ψ β hβ y) =
        structMap hLawY (show (β - ε) - ε ≤ β by linarith) y)
    {β : ℝ} (hβ : α ≤ β) (hβε : α ≤ β - ε) {y y' : comps stageY JY β}
    (hψ : ψ β hβ y = ψ β hβ y') :
    structMap hLawY (show (β - ε) - ε ≤ β by linarith) y =
      structMap hLawY (show (β - ε) - ε ≤ β by linarith) y' := by
  have h := congrArg (fun z => φ (β - ε) hβε z) hψ
  rwa [hSq3 β hβ hβε y, hSq3 β hβ hβε y'] at h
