-- Prove2me | solution 1 for UAVariety.S_S_subset_S
-- status  : ACCEPTED   (prove)
-- author  : @Alien60
-- created : 2026-11-06T17:14:47.177493+00:00
-- url     : https://prove2.me/submissions/16083327-40f7-4a9e-b220-35f64a9ac64d

import Definitions.Def_UAVariety_defs

universe u₁ v₁

set_option linter.unusedSectionVars false

open FirstOrder FirstOrder.Language

namespace UAVariety

variable {L : FirstOrder.Language.{u₁, v₁}} [L.IsAlgebraic]

theorem fsp_S_S_subset_S (K : Set (Alg L)) : S (S K) ⊆ S K := by
  rintro C ⟨B, ⟨A, hA, ⟨f⟩⟩, ⟨g⟩⟩
  exact ⟨A, hA, ⟨f.comp g⟩⟩

end UAVariety

theorem solution {L : FirstOrder.Language.{u₁, v₁}} [L.IsAlgebraic] (K : Set (UAVariety.Alg L)) :
    UAVariety.S (UAVariety.S K) ⊆ UAVariety.S K :=
  UAVariety.fsp_S_S_subset_S K
