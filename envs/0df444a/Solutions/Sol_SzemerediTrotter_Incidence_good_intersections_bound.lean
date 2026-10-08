-- Prove2me | solution 1 for SzemerediTrotter.Incidence.good_intersections_bound
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-04T15:57:05.701089+00:00
-- url     : https://prove2.me/submissions/5794458c-e61c-4756-8931-7bdc3a245186

import Mathlib
import Definitions.Def_SzemerediTrotter_Incidence_incidences

set_option autoImplicit false

open SzemerediTrotter.Incidence in
theorem p2m91071057_line_eq_span {l : AffineSubspace ℝ Plane} (hl : IsLine l) {p q : Plane}
    (hpq : p ≠ q) (hp : p ∈ l) (hq : q ∈ l) : affineSpan ℝ ({p, q} : Set Plane) = l := by
  apply AffineSubspace.eq_of_direction_eq_of_nonempty_of_le
  · apply Submodule.eq_of_le_of_finrank_eq
    · exact AffineSubspace.direction_le (affineSpan_pair_le_of_mem_of_mem hp hq)
    · rw [direction_affineSpan, vectorSpan_pair, finrank_span_singleton (vsub_ne_zero.mpr hpq)]
      exact hl.symm
  · exact (affineSpan_nonempty ℝ).mpr (Set.insert_nonempty _ _)
  · exact affineSpan_pair_le_of_mem_of_mem hp hq

open SzemerediTrotter.Incidence in
theorem p2m91071057_lines_eq {l₁ l₂ : AffineSubspace ℝ Plane} (h₁ : IsLine l₁) (h₂ : IsLine l₂)
    {p q : Plane} (hpq : p ≠ q) (hp₁ : p ∈ l₁) (hq₁ : q ∈ l₁) (hp₂ : p ∈ l₂) (hq₂ : q ∈ l₂) :
    l₁ = l₂ := by
  rw [← p2m91071057_line_eq_span h₁ hpq hp₁ hq₁, p2m91071057_line_eq_span h₂ hpq hp₂ hq₂]

open SzemerediTrotter.Incidence in
theorem p2m91071057_part1 (P : Finset Plane) (L : Finset (AffineSubspace ℝ Plane))
    (hL : ∀ l ∈ L, IsLine l) :
    ∑ p ∈ P, (degree L p).choose 2 ≤ L.card.choose 2 := by
  classical
  have hdeg : ∀ p, (degree L p).choose 2 = ((L.filter (fun l => p ∈ l)).powersetCard 2).card := by
    intro p
    rw [Finset.card_powersetCard]
    unfold degree
    congr 1
  simp_rw [hdeg]
  rw [← Finset.card_biUnion]
  · rw [← Finset.card_powersetCard]
    apply Finset.card_le_card
    intro s hs
    simp only [Finset.mem_biUnion, Finset.mem_powersetCard] at hs ⊢
    obtain ⟨p, _, hsub, hcard⟩ := hs
    exact ⟨hsub.trans (Finset.filter_subset _ _), hcard⟩
  · intro p _ q _ hpq
    rw [Function.onFun, Finset.disjoint_left]
    intro s hsp hsq
    rw [Finset.mem_powersetCard] at hsp hsq
    obtain ⟨a, b, hab, rfl⟩ := Finset.card_eq_two.mp hsp.2
    have ha : a ∈ L.filter (fun l => p ∈ l) := hsp.1 (by simp)
    have hb : b ∈ L.filter (fun l => p ∈ l) := hsp.1 (by simp)
    have ha' : a ∈ L.filter (fun l => q ∈ l) := hsq.1 (by simp)
    have hb' : b ∈ L.filter (fun l => q ∈ l) := hsq.1 (by simp)
    rw [Finset.mem_filter] at ha hb ha' hb'
    exact hab (p2m91071057_lines_eq (hL a ha.1) (hL b hb.1) hpq ha.2 ha'.2 hb.2 hb'.2)

open SzemerediTrotter.Incidence in
theorem p2m91071057_inc (P : Finset Plane) (L : Finset (AffineSubspace ℝ Plane)) :
    incidences P L = ∑ p ∈ P, degree L p := by
  classical
  unfold incidences degree
  rw [Finset.card_filter, Finset.sum_product]
  refine Finset.sum_congr rfl (fun p _ => ?_)
  rw [Finset.card_filter]

open SzemerediTrotter.Incidence in
theorem solution (P : Finset Plane) (L : Finset (AffineSubspace ℝ Plane))
    (hL : ∀ l ∈ L, IsLine l) :
    (∑ p ∈ P, (degree L p).choose 2 ≤ L.card.choose 2) ∧
    ((incidences P L : ℝ) ^ 2 / (2 * (P.card : ℝ)) - (incidences P L : ℝ) / 2
      ≤ (L.card : ℝ) ^ 2 / 2) := by
  have h1 := p2m91071057_part1 P L hL
  refine ⟨h1, ?_⟩
  have h1r : ((∑ p ∈ P, (degree L p).choose 2 : ℕ) : ℝ) ≤ ((L.card.choose 2 : ℕ) : ℝ) := by
    exact_mod_cast h1
  rw [Nat.cast_sum] at h1r
  simp only [Nat.cast_choose_two] at h1r
  have hI : (incidences P L : ℝ) = ∑ p ∈ P, (degree L p : ℝ) := by
    rw [p2m91071057_inc, Nat.cast_sum]
  have hCS : (∑ p ∈ P, (degree L p : ℝ)) ^ 2 ≤ (P.card : ℝ) * ∑ p ∈ P, (degree L p : ℝ) ^ 2 :=
    sq_sum_le_card_mul_sum_sq
  have hsum : ∑ p ∈ P, ((degree L p : ℝ) * ((degree L p : ℝ) - 1) / 2)
      = (∑ p ∈ P, (degree L p : ℝ) ^ 2 - ∑ p ∈ P, (degree L p : ℝ)) / 2 := by
    rw [← Finset.sum_sub_distrib, Finset.sum_div]
    refine Finset.sum_congr rfl (fun p _ => ?_)
    ring
  rw [hsum] at h1r
  rw [hI]
  set S := ∑ p ∈ P, (degree L p : ℝ)
  set Q := ∑ p ∈ P, (degree L p : ℝ) ^ 2
  set t := (L.card : ℝ)
  have hS : 0 ≤ S := Finset.sum_nonneg (fun p _ => Nat.cast_nonneg _)
  have ht : 0 ≤ t := Nat.cast_nonneg _
  rcases Nat.eq_zero_or_pos P.card with hn | hn
  · rw [hn, Nat.cast_zero, mul_zero, div_zero]
    nlinarith
  · have hnr : (0 : ℝ) < P.card := by exact_mod_cast hn
    have hq : S ^ 2 / (2 * (P.card : ℝ)) ≤ Q / 2 := by
      rw [div_le_div_iff₀ (by positivity) (by norm_num)]
      nlinarith
    nlinarith
