-- Prove2me | solution 1 for SandsSauerWoodrow.leSet_antisymm
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-17T11:19:18.486978+00:00
-- url     : https://prove2.me/submissions/da65d7d3-6308-41fd-9014-9f879e6df9b9

import Mathlib
import Definitions.Def_opg1808_colored_tournaments
import Definitions.Def_SandsSauerWoodrow_OrderOnSets

open OPG1808

universe u
open SandsSauerWoodrow

theorem solution{V : Type u} {R : V → V → Prop}
    (hirr : Irreflexive R) (htr : Transitive R) {S T : Set V}
    (hS : RelIndep R S) (hT : RelIndep R T) (hST : leSet R S T) (hTS : leSet R T S) :
    S = T := by
  have key : ∀ {A B : Set V}, RelIndep R A → leSet R A B → leSet R B A → A ⊆ B := by
    intro A B hA hAB hBA x hx
    obtain ⟨y, hy, h1⟩ := hAB x hx
    rcases h1 with h1 | h1
    · rw [h1]
      exact hy
    · exfalso
      obtain ⟨z, hz, h2⟩ := hBA y hy
      have hxz : R x z := by
        rcases h2 with h2 | h2
        · rw [← h2]
          exact h1
        · exact htr h1 h2
      by_cases hne : x = z
      · rw [← hne] at hxz
        exact hirr x hxz
      · exact (hA x hx z hz hne).1 hxz
  exact Set.Subset.antisymm (key hS hST hTS) (key hT hTS hST)
