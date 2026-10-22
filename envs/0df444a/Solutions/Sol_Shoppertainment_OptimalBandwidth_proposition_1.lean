-- Prove2me | solution 1 for Shoppertainment.OptimalBandwidth.proposition_1
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T06:42:27.818354+00:00
-- url     : https://prove2.me/submissions/50a2178a-81ac-4ac6-a53f-ee1fa0b8d4f5

import Mathlib
import Definitions.Def_Shoppertainment_OptimalBandwidth_Model

set_option autoImplicit false
open Shoppertainment.OptimalBandwidth

lemma sho_psi_eq (ql te : ℝ) (hql1 : ql < 1) (hte0 : 0 ≤ te) (hte1 : te ≤ 1) :
    psi ql te = if teHat ql < te then (qHat te - ql) / (1 - ql) else 0 := by
  unfold psi
  have h2ql : 0 < 2 - ql := by linarith
  split_ifs with hlt
  · congr 1
    have hte : 0 < te := lt_of_le_of_lt (by unfold teHat; positivity) hlt
    unfold teHat at hlt
    rw [div_lt_iff₀ h2ql] at hlt
    have hq1 : ql < qHat te := by
      unfold qHat
      have : 1 / te < 2 - ql := by rw [div_lt_iff₀ hte]; linarith
      linarith
    have hq2 : qHat te ≤ 1 := by
      unfold qHat
      have : 1 ≤ 1 / te := by rw [le_div_iff₀ hte]; linarith
      linarith
    have hset : {q : ℝ | q ∈ Set.Icc ql 1 ∧ 1 / (2 - q) < te} = Set.Ico ql (qHat te) := by
      ext q
      simp only [Set.mem_setOf_eq, Set.mem_Icc, Set.mem_Ico]
      constructor
      · rintro ⟨⟨h1, h2⟩, h3⟩
        refine ⟨h1, ?_⟩
        have hx : 0 < 2 - q := by linarith
        rw [div_lt_iff₀ hx] at h3
        unfold qHat
        have : 1 / te < 2 - q := by rw [div_lt_iff₀ hte]; linarith
        linarith
      · rintro ⟨h1, h2⟩
        refine ⟨⟨h1, by linarith⟩, ?_⟩
        have hx : 0 < 2 - q := by linarith
        rw [div_lt_iff₀ hx]
        have : 1 / te < 2 - q := by unfold qHat at h2; linarith
        rw [div_lt_iff₀ hte] at this
        linarith
    rw [hset, Real.volume_Ico, ENNReal.toReal_ofReal (by linarith)]
  · have hset : {q : ℝ | q ∈ Set.Icc ql 1 ∧ 1 / (2 - q) < te} = ∅ := by
      ext q
      simp only [Set.mem_setOf_eq, Set.mem_Icc, Set.mem_empty_iff_false, iff_false, not_and, not_lt]
      rintro ⟨h1, h2⟩
      have hx : 0 < 2 - q := by linarith
      have : te ≤ 1 / (2 - ql) := by unfold teHat at hlt; exact not_lt.1 hlt
      exact this.trans (one_div_le_one_div_of_le hx (by linarith))
    rw [hset]; simp

theorem solution (ql : ℝ) (hql : 0 ≤ ql) (hql1 : ql < 1) :
    (∀ te ∈ Set.Icc (0:ℝ) 1,
        psi ql te = if teHat ql < te then (qHat te - ql) / (1 - ql) else 0) ∧
    StrictMonoOn (psi ql) (Set.Ioc (teHat ql) 1) ∧
    (∀ te ∈ Set.Icc (0:ℝ) 1,
        AntitoneOn (fun ql' => psi ql' te) {ql' : ℝ | 0 ≤ ql' ∧ ql' < 1 ∧ teHat ql' < te} ∧
        (te < 1 →
          StrictAntiOn (fun ql' => psi ql' te) {ql' : ℝ | 0 ≤ ql' ∧ ql' < 1 ∧ teHat ql' < te})) := by
  have hpos : 0 < teHat ql := by unfold teHat; apply div_pos one_pos; linarith
  have h1ql : 0 < 1 - ql := by linarith
  refine ⟨fun te ⟨h0, h1⟩ => sho_psi_eq ql te hql1 h0 h1, ?_, ?_⟩
  · intro a ha b hb hab
    obtain ⟨ha1, ha2⟩ := ha
    obtain ⟨hb1, hb2⟩ := hb
    have ha0 : 0 < a := lt_trans hpos ha1
    have hb0 : 0 < b := lt_trans hpos hb1
    rw [sho_psi_eq ql a hql1 ha0.le ha2, sho_psi_eq ql b hql1 hb0.le hb2, if_pos ha1, if_pos hb1]
    apply div_lt_div_of_pos_right _ h1ql
    unfold qHat
    have : 1 / b < 1 / a := one_div_lt_one_div_of_lt ha0 hab
    linarith
  · intro te ⟨hte0, hte1⟩
    have key : ∀ a ∈ {ql' : ℝ | 0 ≤ ql' ∧ ql' < 1 ∧ teHat ql' < te},
        psi a te = (qHat te - a) / (1 - a) := by
      intro a ⟨ha0, ha1, ha2⟩
      rw [sho_psi_eq a te ha1 hte0 hte1, if_pos ha2]
    have hc : ∀ a ∈ {ql' : ℝ | 0 ≤ ql' ∧ ql' < 1 ∧ teHat ql' < te}, qHat te ≤ 1 := by
      intro a ⟨ha0, ha1, ha2⟩
      have : 0 < te := lt_of_le_of_lt (by unfold teHat; apply div_nonneg zero_le_one; linarith) ha2
      unfold qHat
      have : 1 ≤ 1 / te := by rw [le_div_iff₀ this]; linarith
      linarith
    constructor
    · intro a ha b hb hab
      simp only
      rw [key a ha, key b hb]
      have h1a : 0 < 1 - a := by linarith [ha.2.1]
      have h1b : 0 < 1 - b := by linarith [hb.2.1]
      rw [div_le_div_iff₀ h1b h1a]
      nlinarith [hc a ha]
    · intro hlt a ha b hb hab
      simp only
      rw [key a ha, key b hb]
      have h1a : 0 < 1 - a := by linarith [ha.2.1]
      have h1b : 0 < 1 - b := by linarith [hb.2.1]
      have hte' : 0 < te := lt_of_le_of_lt (by unfold teHat; apply div_nonneg zero_le_one; linarith [ha.2.1]) ha.2.2
      have hc1 : qHat te < 1 := by
        unfold qHat
        have : 1 < 1 / te := by rw [lt_div_iff₀ hte']; linarith
        linarith
      rw [div_lt_div_iff₀ h1b h1a]
      nlinarith
