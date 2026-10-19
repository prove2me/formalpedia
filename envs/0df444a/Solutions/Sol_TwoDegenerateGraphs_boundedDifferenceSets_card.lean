-- Prove2me | solution 1 for TwoDegenerateGraphs.boundedDifferenceSets_card
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:08.630233+00:00
-- url     : https://prove2.me/submissions/060021d0-5eea-42bb-89ae-dbc9cbda2f04

import Mathlib
import Definitions.Def_CompactnessAndDegeneracy

set_option autoImplicit true
open TwoDegenerateGraphs
open Filter Finset SimpleGraph
open scoped Topology
namespace TwoDegenerateGraphs
theorem _root_.solution (dimension radius : ℕ) :
    (boundedDifferenceSets dimension radius).card =
      ∑ d ∈ Finset.range (radius + 1), dimension.choose d := by
  classical
  have hmaps :
      ((boundedDifferenceSets dimension radius :
        Finset (Finset (Fin dimension))) : Set (Finset (Fin dimension))).MapsTo
        Finset.card (Finset.range (radius + 1)) := by
    intro S hS
    have hmembership : S ∈
        (((Finset.univ : Finset (Fin dimension)).powerset).filter
          (fun coordinates => coordinates.card ≤ radius)) := by
      exact Finset.mem_coe.mp hS
    have hcard := (Finset.mem_filter.mp hmembership).2
    exact Finset.mem_range.mpr (by omega)
  calc
    (boundedDifferenceSets dimension radius).card =
        ∑ d ∈ Finset.range (radius + 1),
          ((boundedDifferenceSets dimension radius).filter
            (fun coordinates => coordinates.card = d)).card :=
      Finset.card_eq_sum_card_fiberwise hmaps
    _ = ∑ d ∈ Finset.range (radius + 1), dimension.choose d := by
      apply Finset.sum_congr rfl
      intro d hd
      have hdle : d ≤ radius := by
        have := Finset.mem_range.mp hd
        omega
      have hfiber :
          (boundedDifferenceSets dimension radius).filter
            (fun coordinates => coordinates.card = d) =
          (Finset.univ : Finset (Fin dimension)).powersetCard d := by
        ext coordinates
        simp only [boundedDifferenceSets, Finset.mem_filter,
          Finset.mem_powerset, Finset.mem_powersetCard]
        constructor
        · rintro ⟨⟨hsubset, _⟩, hcard⟩
          exact ⟨hsubset, hcard⟩
        · rintro ⟨hsubset, hcard⟩
          exact ⟨⟨hsubset, by omega⟩, hcard⟩
      rw [hfiber, Finset.card_powersetCard]
      simp
end TwoDegenerateGraphs
