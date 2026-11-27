-- Prove2me | solution 1 for TailOptCaching.ETLRU.Supplement.proof_theorem_1_step_one
-- status  : ACCEPTED   (prove)
-- author  : @mikedeng1
-- created : 2026-11-27T06:49:12.044081+00:00
-- url     : https://prove2.me/submissions/40020175-8797-4023-8cca-b3b546ecbbbb

import Mathlib
import Definitions.Def_TailOptCaching_ETLRU_Supplement_Trace

open TailOptCaching
open TailOptCaching.ETLRU
open TailOptCaching.ETLRU.Supplement

theorem solution {N : ℕ} (tr : Trace N) (C ξ : ℕ) :
    (∀ (x u : Fin N → ℕ → ℕ),
        (∀ i t, t ∈ reqTimes tr i → (need tr i t : ℤ) - x i t - ξ ≤ u i t) →
        tel tr ξ x ≤ ∑ i, ∑ t ∈ reqTimes tr i, u i t) ∧
    (∀ x, Feasible tr C x →
        Feasible tr C (capToBudget tr ξ x) ∧ WithinBudget tr ξ (capToBudget tr ξ x) ∧
          tel tr ξ (capToBudget tr ξ x) = tel tr ξ x) ∧
    (∀ x, WithinBudget tr ξ x →
        tel tr ξ x + hits tr x = ∑ i, ∑ t ∈ reqTimes tr i, budget tr ξ i t) ∧
    (∀ x, Feasible tr C x → WithinBudget tr ξ x →
        ((∀ y, Feasible tr C y → WithinBudget tr ξ y → hits tr y ≤ hits tr x) ↔
          (∀ y, Feasible tr C y → tel tr ξ x ≤ tel tr ξ y))) := by
            have h1 : ∀ (x u : Fin N → ℕ → ℕ),
                  (∀ i t, t ∈ reqTimes tr i → (need tr i t : ℤ) - x i t - ξ ≤ u i t) →
                  tel tr ξ x ≤ ∑ i, ∑ t ∈ reqTimes tr i, u i t := by
              intro x u h
              unfold tel
              refine Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun t ht => ?_
              have := h i t ht
              omega
            have h2 : ∀ x, Feasible tr C x →
                  Feasible tr C (capToBudget tr ξ x) ∧ WithinBudget tr ξ (capToBudget tr ξ x) ∧
                    tel tr ξ (capToBudget tr ξ x) = tel tr ξ x := by
              intro x hx
              obtain ⟨hx0, hxC, hxH, hxN⟩ := hx
              have hle : ∀ i t, capToBudget tr ξ x i t ≤ x i t := by
                intro i t
                unfold capToBudget
                split_ifs
                · exact min_le_left _ _
                · exact le_rfl
              refine ⟨⟨?_, ?_, ?_, ?_⟩, ?_, ?_⟩
              · intro i
                have := hle i 1
                rw [hx0 i] at this
                omega
              · intro t ht1 htT
                exact le_trans (Finset.sum_le_sum fun i _ => hle i t) (hxC t ht1 htT)
              · intro i t ht htT
                exact le_trans (hle i (t + 1)) (hxH i t ht htT)
              · intro i t ht1 htT hnt
                have h3 : capToBudget tr ξ x i t = x i t := by
                  unfold capToBudget
                  rw [if_neg hnt]
                rw [h3]
                exact le_trans (hle i (t + 1)) (hxN i t ht1 htT hnt)
              · intro i t ht
                unfold capToBudget
                rw [if_pos ht]
                exact min_le_right _ _
              · unfold tel
                refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun t ht => ?_
                have h3 : capToBudget tr ξ x i t = min (x i t) (budget tr ξ i t) := by
                  unfold capToBudget
                  rw [if_pos ht]
                rw [h3]
                unfold budget
                omega
            have h3 : ∀ x, WithinBudget tr ξ x →
                  tel tr ξ x + hits tr x = ∑ i, ∑ t ∈ reqTimes tr i, budget tr ξ i t := by
              intro x hx
              unfold tel hits
              rw [← Finset.sum_add_distrib]
              refine Finset.sum_congr rfl fun i _ => ?_
              rw [← Finset.sum_add_distrib]
              refine Finset.sum_congr rfl fun t ht => ?_
              have := hx i t ht
              unfold budget at this ⊢
              omega
            refine ⟨h1, h2, h3, ?_⟩
            intro x hxF hxB
            have ex := h3 x hxB
            constructor
            · intro h y hy
              obtain ⟨hF, hB, hT⟩ := h2 y hy
              have e := h3 _ hB
              have hh := h _ hF hB
              omega
            · intro h y hy hyB
              have e := h3 y hyB
              have hh := h y hy
              omega
