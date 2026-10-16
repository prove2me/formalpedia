-- Prove2me | solution 1 for PersistClust.Count.phi_fiber_merge
-- status  : ACCEPTED   (prove)
-- author  : @fabianroll
-- created : 2026-10-15T13:31:34.414026+00:00
-- url     : https://prove2.me/submissions/215aaed7-0294-4337-93fb-762b8fd9de76

import Mathlib
import Definitions.Def_PersistClust_Count_Setting
import Definitions.Def_PersistClust_Count_Diagram
import Definitions.Def_PersistClust_Count_FiltrationLaw
import Definitions.Def_PersistClust_Count_MatchingCensus
import Definitions.Def_PersistClust_Count_MatchingGate

open PersistClust.Count
open scoped ENNReal

/-- Phi-fiber merge (interleaving square iv): if phi identifies two X-cells
x and x' at a common level beta, then their 2eps-descent structure maps
agree -- applying psi to the phi-equality and rewriting both sides
through the square law hSq4 turns the fiber equality into a
descent-merge equality on the source cells. -/
theorem solution {ιX ιY : Type*}
    {stageX : ℝ → Set ιX} {JX : ℝ → ιX → ιX → Prop} {stageY : ℝ → Set ιY} {JY : ℝ → ιY → ιY → Prop}
    (hLawX : FiltrationLaw stageX JX) (hLawY : FiltrationLaw stageY JY)
    {α ε : ℝ} (hε : 0 ≤ ε)
    (φ : ∀ β : ℝ, α ≤ β → comps stageX JX β → comps stageY JY (β - ε))
    (ψ : ∀ β : ℝ, α ≤ β → comps stageY JY β → comps stageX JX (β - ε))
    (hSq4 : ∀ (β : ℝ) (hβ : α ≤ β) (hβε : α ≤ β - ε) (x : comps stageX JX β),
      ψ (β - ε) hβε (φ β hβ x) =
        structMap hLawX (show (β - ε) - ε ≤ β by linarith) x)
    {β : ℝ} (hβ : α ≤ β) (hβε : α ≤ β - ε) {x x' : comps stageX JX β}
    (hφ : φ β hβ x = φ β hβ x') :
    structMap hLawX (show (β - ε) - ε ≤ β by linarith) x =
      structMap hLawX (show (β - ε) - ε ≤ β by linarith) x' := by
  have h := congrArg (fun z => ψ (β - ε) hβε z) hφ
  rwa [hSq4 β hβ hβε x, hSq4 β hβ hβε x'] at h
