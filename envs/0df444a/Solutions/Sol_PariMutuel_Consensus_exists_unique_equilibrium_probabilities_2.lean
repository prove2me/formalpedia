-- Prove2me | solution 2 for PariMutuel.Consensus.exists_unique_equilibrium_probabilities
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-27T10:04:20.874361+00:00
-- url     : https://prove2.me/submissions/39c4e5b8-912e-45bd-a5db-1275c8ab78bd

import Mathlib
import Definitions.Def_PariMutuel_Consensus_Market
import Definitions.Def_PariMutuel_Consensus_Phi
import Theorems.Thm_PariMutuel_Consensus_existence_theorem
import Theorems.Thm_PariMutuel_Consensus_exists_isPhiMaximizer
import Theorems.Thm_PariMutuel_Consensus_sum_sq_div_le_one

-- carved verbatim out of submission a75568d5-0621-4ccd-9fbe-4e81e09ce0e1, lines 463-466

section
open PariMutuel
open PariMutuel.Consensus
open Finset

theorem pm_prob_pos {m n : ℕ} (M : Market m n) (π : Fin n → ℝ) (β : Fin m → Fin n → ℝ)
    (h : M.IsEquilibrium π β) (j : Fin n) : 0 < π j := by
  obtain ⟨hπ, hβ, hb, hc, hq⟩ := h
  rcases (hπ j).lt_or_eq with h1 | h1
  · exact h1
  exfalso
  obtain ⟨i, hi⟩ := M.P_col_pos j
  have : ∃ s, 0 < β i s := by
    by_contra hne
    push_neg at hne
    have : ∑ s, β i s ≤ 0 := Finset.sum_nonpos (fun s _ => hne s)
    have := M.b_pos i
    linarith [hb i]
  obtain ⟨s, hs⟩ := this
  have h2 := hq i s hs j
  rw [← h1] at h2
  have h3 : β i s ≤ π s := by
    rw [← hc s]
    exact Finset.single_le_sum (f := fun i => β i s) (fun i _ => hβ i s) (Finset.mem_univ i)
  have : 0 < M.P i j * π s := mul_pos hi (by linarith)
  linarith

theorem pm_sum_one {m n : ℕ} (M : Market m n) (π : Fin n → ℝ) (β : Fin m → Fin n → ℝ)
    (h : M.IsEquilibrium π β) : ∑ k, π k = 1 := by
  obtain ⟨hπ, hβ, hb, hc, hq⟩ := h
  simp_rw [← hc]
  rw [Finset.sum_comm]
  simp_rw [hb]
  exact M.b_sum

theorem pm_cs {n : ℕ} (π π' : Fin n → ℝ) (hπ : ∀ k, 0 < π k)
    (hs : ∑ k, π k = 1) (hs' : ∑ k, π' k = 1)
    (h : ∑ k, π' k * π' k / π k ≤ 1) : π' = π := by
  have key : ∑ k, (π' k - π k) ^ 2 / π k = ∑ k, π' k * π' k / π k - 1 := by
    have : ∀ k, (π' k - π k) ^ 2 / π k = π' k * π' k / π k - 2 * π' k + π k := by
      intro k
      have := (hπ k).ne'
      field_simp
      ring
    simp_rw [this, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, hs, hs']
    ring
  have hle : ∑ k, (π' k - π k) ^ 2 / π k ≤ 0 := by linarith
  have hz := (Finset.sum_eq_zero_iff_of_nonneg (fun k _ => div_nonneg (sq_nonneg _) (hπ k).le)).1
    (le_antisymm hle (Finset.sum_nonneg (fun k _ => div_nonneg (sq_nonneg _) (hπ k).le)))
  funext k
  have := hz k (Finset.mem_univ k)
  rw [div_eq_zero_iff] at this
  rcases this with h1 | h1
  · nlinarith [sq_nonneg (π' k - π k)]
  · exact absurd h1 (hπ k).ne'

theorem pm_unique {m n : ℕ} (M : Market m n) (π π' : Fin n → ℝ)
    (β β' : Fin m → Fin n → ℝ) (h : M.IsEquilibrium π β) (h' : M.IsEquilibrium π' β') :
    π = π' :=
  (pm_cs π π' (pm_prob_pos M π β h) (pm_sum_one M π β h) (pm_sum_one M π' β' h')
    (PariMutuel.Consensus.sum_sq_div_le_one M π π' β β' h h')).symm

theorem pm_goal {m n : ℕ} (M : Market m n) :
    ∃! π : Fin n → ℝ, ∃ β : Fin m → Fin n → ℝ, M.IsEquilibrium π β := by
  obtain ⟨ξ, hξ⟩ := PariMutuel.Consensus.exists_isPhiMaximizer M
  refine ⟨M.trackProb ξ, ⟨M.bets ξ, PariMutuel.Consensus.existence_theorem M ξ hξ⟩, ?_⟩
  rintro π' ⟨β', h'⟩
  exact pm_unique M π' (M.trackProb ξ) β' (M.bets ξ) h' (PariMutuel.Consensus.existence_theorem M ξ hξ)

end

section
open PariMutuel.Consensus

theorem solution {m n : ℕ} (M : Market m n) :
    ∃! π : Fin n → ℝ, ∃ β : Fin m → Fin n → ℝ, M.IsEquilibrium π β := by
  exact pm_goal M

end
