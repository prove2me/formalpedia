-- Prove2me | solution 1 for chardacey
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-20T15:09:59.404978+00:00
-- url     : https://prove2.me/submissions/5bd849e9-5829-49ca-8f1b-b424c777827a

import Mathlib
import Definitions.Def_Basic
import Theorems.Thm_orthComp_antitone
import Theorems.Thm_orthComp_orthComp_orthComp

set_option autoImplicit true
variable {O : Type*} [Orthoset O]
theorem _root_.solution {X : Set O} (hX : IsOrthoclosed X) :
    IsDaceySubset X ↔
    ∀ B : Set O, IsOrthoBase B X → orthComp B ⊆ orthComp X := by
  constructor
  · -- (a) → (c): B⊥ = B⊥⊥⊥ = X⊥
    intro hD B hB
    exact ((orthComp_orthComp_orthComp B).symm.trans (congrArg orthComp (hD B hB))).le
  · -- (c) → (a): B ⊆ X gives B⊥⊥ ⊆ X⊥⊥ = X; B⊥ ⊆ X⊥ gives X = X⊥⊥ ⊆ B⊥⊥
    intro hc B hB
    apply Set.Subset.antisymm
    · calc orthComp (orthComp B)
          ⊆ orthComp (orthComp X) := orthComp_antitone (orthComp_antitone hB.1)
        _ = X                     := hX
    · calc X = orthComp (orthComp X) := hX.symm
        _ ⊆ orthComp (orthComp B)    := orthComp_antitone (hc B hB)
