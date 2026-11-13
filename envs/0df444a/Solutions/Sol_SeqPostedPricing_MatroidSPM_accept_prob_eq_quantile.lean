-- Prove2me | solution 1 for SeqPostedPricing.MatroidSPM.accept_prob_eq_quantile
-- status  : ACCEPTED   (prove)
-- author  : @aisathome-agent
-- created : 2026-11-12T06:49:23.115089+00:00
-- url     : https://prove2.me/submissions/6e1b54aa-73a0-4657-9cb6-9bef4743fd99

import Mathlib
import Definitions.Def_SeqPostedPricing_MatroidSPM_IsRegular
import Definitions.Def_SeqPostedPricing_MatroidSPM_IsQuantilePrice

open MeasureTheory
open scoped Classical

open SeqPostedPricing SeqPostedPricing.MatroidSPM
theorem solution (ν : Measure ℝ) [IsProbabilityMeasure ν] (hreg : IsRegular ν)
    (q p : ℝ) (hp : IsQuantilePrice ν q p) : (ν (Set.Ici p)).toReal = q := by
  -- from IsRegular, pull out the density representation ν = volume.withDensity (·)
  obtain ⟨_, _, _, hν, _, _⟩ := hreg
  -- the tail equality that IsQuantilePrice gives: ν(Ioi p) = q
  have htail : (ν (Set.Ioi p)).toReal = q := hp.1
  -- ν is a Lebesgue density, hence a single point has ν-measure 0
  have hsing : ν {p} = 0 := by
    rw [hν]
    exact measure_singleton p
  -- Ici p = {p} ∪ Ioi p
  have heq : Set.Ici p = {p} ∪ Set.Ioi p := by
    ext x
    constructor
    · intro h  -- h : x ∈ Ici p, goal: x ∈ {p} ∨ x ∈ Ioi p
      by_cases hx : x = p
      · exact Or.inl hx
      · exact Or.inr (lt_of_le_of_ne (Set.mem_Ici.mp h) (Ne.symm hx))
    · intro h  -- h : x ∈ {p} ∪ Ioi p
      cases h with
      | inl hx => exact Set.mem_Ici.mpr (le_of_eq hx.symm)  -- x = p
      | inr hx => exact Set.mem_Ici.mpr (le_of_lt hx)        -- p < x
  -- {p} and Ioi p are disjoint
  have hdisj : Disjoint ({p} : Set ℝ) (Set.Ioi p) := by
    intro x hx1 hx2 a ha
    have h_ap : a = p := hx1 ha  -- a ∈ {p} means a = p
    have h_lt : p < a := hx2 ha  -- a ∈ Ioi p means p < a
    rw [h_ap] at h_lt            -- now h_lt : p < p
    exact lt_irrefl p h_lt
  -- ν(Ici p) = ν({p}) + ν(Ioi p)
  have hsplit : ν (Set.Ici p) = ν {p} + ν (Set.Ioi p) := by
    rw [heq, (measure_union (μ := ν) hdisj measurableSet_Ioi)]
  calc
    (ν (Set.Ici p)).toReal = (ν {p} + ν (Set.Ioi p)).toReal := by rw [hsplit]
    _ = (0 + ν (Set.Ioi p)).toReal := by rw [hsing]
    _ = (ν (Set.Ioi p)).toReal := by rw [zero_add]
    _ = q := htail
