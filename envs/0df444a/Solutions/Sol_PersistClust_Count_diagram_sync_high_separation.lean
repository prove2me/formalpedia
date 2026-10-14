-- Prove2me | solution 1 for PersistClust.Count.diagram_sync_high_separation
-- status  : ACCEPTED   (prove)
-- author  : @fabianroll
-- created : 2026-10-12T18:13:33.655974+00:00
-- url     : https://prove2.me/submissions/5f8ad48c-4111-4d13-bb8c-b39aca691017

import Mathlib
import Definitions.Def_PersistClust_Count_Setting
import Definitions.Def_PersistClust_Count_Diagram
import Definitions.Def_PersistClust_Count_FiltrationLaw
import Definitions.Def_PersistClust_Count_MatchingCensus

open PersistClust.Count
open scoped ENNReal

/-- Sync-high separation (contrapositive of the interleaving square (iv')):
X-cells whose 2eps-descents (to level u - eps - eps) are DISTINCT have
distinct images at level u - eps: if the images coincided, square (iv')
applied to each cell would force the two 2eps-descents to coincide.
With an X-merge at level delta this bounds the image merge level by
delta + eps. -/
theorem solution {ιX ιY : Type*}
    {stageX : ℝ → Set ιX} {JX : ℝ → ιX → ιX → Prop}
    {stageY : ℝ → Set ιY} {JY : ℝ → ιY → ιY → Prop}
    (hLawX : FiltrationLaw stageX JX) (hLawY : FiltrationLaw stageY JY)
    {α ε : ℝ} (hε : 0 ≤ ε)
    (φ : ∀ β : ℝ, α ≤ β → comps stageX JX β → comps stageY JY (β - ε))
    (ψ : ∀ β : ℝ, α ≤ β → comps stageY JY β → comps stageX JX (β - ε))
    (hSq4 : ∀ (β : ℝ) (hβ : α ≤ β) (hβε : α ≤ β - ε) (x : comps stageX JX β),
      ψ (β - ε) hβε (φ β hβ x) =
        structMap hLawX (show (β - ε) - ε ≤ β by linarith) x)
    {u : ℝ} (hαu : α ≤ u) (hβε : α ≤ u - ε) (hle : u - ε - ε ≤ u)
    (C₁ C₂ : comps stageX JX u)
    (hne : structMap hLawX hle C₁ ≠ structMap hLawX hle C₂) :
    φ u hαu C₁ ≠ φ u hαu C₂ := by
  intro heq
  apply hne
  have h₁ := hSq4 u hαu hβε C₁
  have h₂ := hSq4 u hαu hβε C₂
  calc structMap hLawX hle C₁
      = ψ (u - ε) hβε (φ u hαu C₁) := h₁.symm
    _ = ψ (u - ε) hβε (φ u hαu C₂) := by rw [heq]
    _ = structMap hLawX hle C₂ := h₂
