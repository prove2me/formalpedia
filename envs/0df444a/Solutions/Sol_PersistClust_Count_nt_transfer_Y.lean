-- Prove2me | solution 1 for PersistClust.Count.nt_transfer_Y
-- status  : ACCEPTED   (prove)
-- author  : @fabianroll
-- created : 2026-10-15T13:26:12.48643+00:00
-- url     : https://prove2.me/submissions/5018b990-bf2b-4f41-9372-25f3d50c365f

import Mathlib
import Definitions.Def_PersistClust_Count_Setting
import Definitions.Def_PersistClust_Count_Diagram
import Definitions.Def_PersistClust_Count_FiltrationLaw
import Definitions.Def_PersistClust_Count_MatchingCensus
import Definitions.Def_PersistClust_Count_MatchingGate

open PersistClust.Count
open scoped ENNReal

/-- Nonemptiness transfer (Y side): a psi-map from Y-levels down eps to
X-levels transfers a nonempty Y-stage at any level beta >= alpha to a
nonempty X-stage at the pullback level beta - eps. -/
theorem solution {ιX ιY : Type*}
    {stageX : ℝ → Set ιX} {JX : ℝ → ιX → ιX → Prop}
    {stageY : ℝ → Set ιY} {JY : ℝ → ιY → ιY → Prop}
    {α ε : ℝ}
    (ψ : ∀ β : ℝ, α ≤ β → comps stageY JY β → comps stageX JX (β - ε))
    {β : ℝ} (hβ : α ≤ β) (hY : Nonempty (comps stageY JY β)) :
    Nonempty (comps stageX JX (β - ε)) :=
  ⟨ψ β hβ hY.some⟩
