-- Prove2me | solution 1 for OpaquePricing.Dominance.Supplement.lemma_9
-- status  : ACCEPTED   (prove)
-- author  : @mikedeng1
-- created : 2026-11-27T06:21:50.742633+00:00
-- url     : https://prove2.me/submissions/49c80a7a-bb49-4e48-924b-38d52a9d856c

import Mathlib
import Definitions.Def_OpaquePricing_Dominance_Setting
import Definitions.Def_OpaquePricing_Dominance_Supplement_OneOpaque
import Definitions.Def_OpaquePricing_Dominance_Supplement_PurchaseRegion

open MeasureTheory

open OpaquePricing
open OpaquePricing.Dominance
open OpaquePricing.Dominance.Supplement

theorem solution {N : ℕ} (hN : 2 ≤ N) (v : Fin N → ℝ)
    (hv : ∀ i, 0 ≤ v i) (p r : ℝ) (hr : 0 ≤ r) (hsmall : r < p / N)
    (hE : v ∈ E2 p r) :
    0 ≤ rnValue v Finset.univ - r ∧
    (∀ i, v i - p < rnValue v Finset.univ - r) ∧
    oneRevenue rnValue p r v = r := by
      classical
      have hmax : ∀ i, v i ≤ maxValue v := by
        intro i
        unfold maxValue orderStat
        set L := (((Finset.univ : Finset (Fin N)).toList.map v).mergeSort (fun a b => decide (b ≤ a))) with hL
        have hpw : L.Pairwise (fun a b => decide (b ≤ a)) := by
          apply List.pairwise_mergeSort
          · intro a b c h1 h2; simp only [decide_eq_true_eq] at *; linarith
          · intro a b; simp only [Bool.or_eq_true, decide_eq_true_eq]; exact le_total _ _
        have hmem : v i ∈ L := by
          rw [hL, List.mem_mergeSort]; simp
        cases hLc : L with
        | nil => rw [hLc] at hmem; simp at hmem
        | cons h t =>
          rw [hLc] at hmem hpw
          simp only [List.getD_cons_zero]
          rcases List.mem_cons.1 hmem with h1 | h1
          · rw [h1]
          · have := List.rel_of_pairwise_cons hpw h1
            simpa using this
      have hatt : ∃ j, v j = maxValue v := by
        unfold maxValue orderStat
        set L := (((Finset.univ : Finset (Fin N)).toList.map v).mergeSort (fun a b => decide (b ≤ a))) with hL
        have hmem : ∀ x, x ∈ L ↔ ∃ j, v j = x := by
          intro x; rw [hL, List.mem_mergeSort]; simp
        cases hLc : L with
        | nil =>
          have := (hmem (v ⟨0, by omega⟩)).2 ⟨_, rfl⟩
          rw [hLc] at this; simp at this
        | cons h t =>
          simp only [List.getD_cons_zero]
          have := (hmem h).1 (by rw [hLc]; simp)
          exact this
      obtain ⟨j, hj⟩ := hatt
      obtain ⟨hE1, hE2⟩ := hE
      have hNpos : (0:ℝ) < N := by exact_mod_cast (show 0 < N by omega)
      have hN1 : (1:ℝ) < N := by exact_mod_cast (show 1 < N by omega)
      have hA : ∀ i, v i / N ≤ rnValue v Finset.univ := by
        intro i
        unfold rnValue
        rw [Finset.card_univ, Fintype.card_fin]
        apply div_le_div_of_nonneg_right _ hNpos.le
        exact Finset.single_le_sum (fun k _ => hv k) (Finset.mem_univ i)
      have hc1 : 0 ≤ rnValue v Finset.univ - r := by
        have h1 := hA j
        rw [hj] at h1
        have h2 : p / N ≤ maxValue v / N := div_le_div_of_nonneg_right hE1 hNpos.le
        linarith
      have hc2 : ∀ i, v i - p < rnValue v Finset.univ - r := by
        intro i
        have h1 := hA i
        have hvi : v i < (N : ℝ) / ((N : ℝ) - 1) * (p - r) := lt_of_le_of_lt (hmax i) hE2
        have hN1' : (0:ℝ) < N - 1 := by linarith
        have : v i * (N - 1) < N * (p - r) := by
          rw [div_mul_eq_mul_div, lt_div_iff₀ hN1'] at hvi; linarith
        have h3 : v i / N * N = v i := by field_simp
        nlinarith
      refine ⟨hc1, hc2, ?_⟩
      have hcardU : (Finset.univ : Finset (Fin N)).card ≠ 1 := by
        rw [Finset.card_univ, Fintype.card_fin]; omega
      have hpU : opqPrice p (fun _ => r) (Finset.univ : Finset (Fin N)) = r := by
        unfold opqPrice; rw [if_neg hcardU]
      have hUmem : (Finset.univ : Finset (Fin N)) ∈ oneOptions N := by
        unfold oneOptions opqOptions
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, or_true, and_true]
        exact ⟨⟨0, by omega⟩, Finset.mem_univ _⟩
      have hsing : ∀ S ∈ oneOptions N, S ≠ Finset.univ →
          rnValue v S - opqPrice p (fun _ => r) S < rnValue v Finset.univ - r := by
        intro S hS hne
        unfold oneOptions at hS
        simp only [Finset.mem_filter] at hS
        rcases hS.2 with h1 | h1
        · obtain ⟨i, rfl⟩ := Finset.card_eq_one.1 h1
          have : rnValue v {i} = v i := by unfold rnValue; simp
          rw [this]
          unfold opqPrice; rw [if_pos h1]
          exact hc2 i
        · exact absurd h1 hne
      have hwin : (oneOptions N).filter (fun S => 0 ≤ rnValue v S - opqPrice p (fun _ => r) S ∧
          ∀ S' ∈ oneOptions N, rnValue v S' - opqPrice p (fun _ => r) S' ≤
            rnValue v S - opqPrice p (fun _ => r) S) = {Finset.univ} := by
        ext S
        simp only [Finset.mem_filter, Finset.mem_singleton]
        constructor
        · rintro ⟨hS, h0, hall⟩
          by_contra hne
          have h1 := hsing S hS hne
          have h2 := hall _ hUmem
          rw [hpU] at h2
          linarith
        · rintro rfl
          refine ⟨hUmem, by rw [hpU]; exact hc1, ?_⟩
          intro S' hS'
          rw [hpU]
          by_cases hne : S' = Finset.univ
          · rw [hne, hpU]
          · exact (hsing S' hS' hne).le
      unfold oneRevenue menuRevenue
      simp only [hwin]
      rw [dif_pos (Finset.singleton_nonempty _), Finset.sup'_singleton, hpU]
