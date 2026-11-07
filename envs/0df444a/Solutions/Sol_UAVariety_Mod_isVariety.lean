-- Prove2me | solution 1 for UAVariety.Mod_isVariety
-- status  : ACCEPTED   (prove)
-- author  : @Alien60
-- created : 2026-11-06T17:47:06.868217+00:00
-- url     : https://prove2.me/submissions/fb53067a-eb9c-44fc-b4dd-edccabbb87d2

import Definitions.Def_UAVariety_defs
import Theorems.Thm_UAVariety_same_identities

universe u₁ v₁

set_option linter.unusedSectionVars false

open FirstOrder FirstOrder.Language

namespace UAVariety

variable {L : FirstOrder.Language.{u₁, v₁}} [L.IsAlgebraic]

theorem bh_Mod_isVariety (E : Set (L.Term ℕ × L.Term ℕ)) : IsVariety (Mod E) := by
  have key : ∀ e ∈ E, ∀ A ∈ Mod E, Satisfies A (e.1, e.2) := fun e he A hA => hA e he
  refine ⟨fun B hB e he => ?_, fun B hB e he => ?_, fun B hB e he => ?_⟩
  · exact (same_identities (Mod E) e.1 e.2).1.2 (key e he) B hB
  · exact (same_identities (Mod E) e.1 e.2).2.1.2 (key e he) B hB
  · exact (same_identities (Mod E) e.1 e.2).2.2.1.2 (key e he) B hB

end UAVariety

theorem solution {L : FirstOrder.Language.{u₁, v₁}} [L.IsAlgebraic] (E : Set (L.Term ℕ × L.Term ℕ)) : UAVariety.IsVariety (UAVariety.Mod E) :=
  UAVariety.bh_Mod_isVariety E
