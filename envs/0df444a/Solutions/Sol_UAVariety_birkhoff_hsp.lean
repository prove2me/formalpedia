-- Prove2me | solution 1 for UAVariety.birkhoff_hsp
-- status  : ACCEPTED   (prove)
-- author  : @Alien60
-- created : 2026-11-06T17:47:08.911197+00:00
-- url     : https://prove2.me/submissions/cf7f3627-6b93-4610-896f-a2ce2a100a53

import Definitions.Def_UAVariety_defs
import Theorems.Thm_UAVariety_free_mem_SP
import Theorems.Thm_UAVariety_Mod_Id_satisfies
import Theorems.Thm_UAVariety_Mod_isVariety
import Theorems.Thm_UAVariety_free_lift_of_satisfies

universe u₁ v₁

set_option linter.unusedSectionVars false

open FirstOrder FirstOrder.Language

namespace UAVariety

variable {L : FirstOrder.Language.{u₁, v₁}} [L.IsAlgebraic]

theorem bh_main (K : Set (Alg L)) : IsVariety K ↔ K = Mod (Id K) := by
  constructor
  · intro hV
    apply Set.Subset.antisymm
    · intro A hA e he
      exact he A hA
    · intro A hA
      obtain ⟨f, hf⟩ := free_lift_of_satisfies K A A id (fun p q hK => Mod_Id_satisfies K p q hK A hA)
      have hF : freeAlg K A ∈ K := (free_mem_SP K A).2 hV.2.1 hV.2.2
      exact hV.1 ⟨freeAlg K A, hF, f, fun a => ⟨freeGen K A a, hf a⟩⟩
  · intro h
    rw [h]
    exact Mod_isVariety _

end UAVariety

theorem solution {L : FirstOrder.Language.{u₁, v₁}} [L.IsAlgebraic] (K : Set (UAVariety.Alg L)) :
    UAVariety.IsVariety K ↔ K = UAVariety.Mod (UAVariety.Id K) :=
  UAVariety.bh_main K
