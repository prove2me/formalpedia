-- Prove2me | solution 2 for SandsSauerWoodrow.leSet_antisymm
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-17T23:23:48.8034+00:00
-- url     : https://prove2.me/submissions/8fbb7dc2-0d24-4c5a-8a01-746927a433f2

import Definitions.Def_opg1808_colored_tournaments
import Definitions.Def_SandsSauerWoodrow_OrderOnSets

open OPG1808
open SandsSauerWoodrow

universe u

/-- Half of antisymmetry: for a strict partial order `R`, an `R`-independent set lying below
another is contained in it. Independence of the second set is not needed. -/
private lemma subset_of_indep {V : Type u} {R : V → V → Prop}
    (hirr : Irreflexive R) (htr : Transitive R) {S T : Set V}
    (hS : RelIndep R S) (hST : leSet R S T) (hTS : leSet R T S) : S ⊆ T := by
  intro x hx
  obtain ⟨y, hy, hxy⟩ := hST x hx
  rcases hxy with hxy | hxy
  · rw [hxy]; exact hy
  · obtain ⟨z, hz, hyz⟩ := hTS y hy
    rcases hyz with hyz | hyz
    · -- here `y = z`, so `y` itself lies in `S`, and independence of `S` forces `x = y`
      subst hyz
      have hxe : x = y := by
        by_contra hne
        exact (hS x hx y hz hne).1 hxy
      rw [hxe]; exact hy
    · -- transitivity puts `x` above `z` inside `S`, contradicting independence of `S`
      have hR : R x z := htr hxy hyz
      by_cases hxz : x = z
      · exact absurd (hxz ▸ hR) (hirr z)
      · exact absurd hR (hS x hx z hz hxz).1

theorem solution {V : Type u} {R : V → V → Prop}
    (hirr : Irreflexive R) (htr : Transitive R) {S T : Set V}
    (hS : RelIndep R S) (hT : RelIndep R T) (hST : leSet R S T) (hTS : leSet R T S) :
    S = T :=
  Set.Subset.antisymm (subset_of_indep hirr htr hS hST hTS)
    (subset_of_indep hirr htr hT hTS hST)
