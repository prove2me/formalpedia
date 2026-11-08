-- Prove2me | solution 1 for SteinerNav.expected_gap
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-07T19:43:25.085791+00:00
-- url     : https://prove2.me/submissions/ef6f0649-0a36-4c72-b256-2c9e6e20128b

import Mathlib

namespace Aux_Steiner_gap

theorem count (n m : ℕ) :
    ∑ Q ∈ (Finset.range n).powersetCard m,
        ((Finset.range n).filter fun i => ∀ q ∈ Q, i < q).card =
      ((Finset.range n).powersetCard (m + 1)).card := by
  rw [← Finset.card_sigma]
  apply Finset.card_bij (fun (p : Σ _ : Finset ℕ, ℕ) _ => insert p.2 p.1)
  · rintro ⟨Q, i⟩ hp
    simp only [Finset.mem_sigma, Finset.mem_powersetCard, Finset.mem_filter, Finset.mem_range] at hp
    obtain ⟨⟨hQ, hQc⟩, hi, hlt⟩ := hp
    have hiQ : i ∉ Q := fun h => lt_irrefl _ (hlt i h)
    rw [Finset.mem_powersetCard]
    refine ⟨Finset.insert_subset (Finset.mem_range.mpr hi) hQ, ?_⟩
    rw [Finset.card_insert_of_notMem hiQ, hQc]
  · rintro ⟨Q, i⟩ hp ⟨Q', i'⟩ hp' heq
    simp only [Finset.mem_sigma, Finset.mem_powersetCard, Finset.mem_filter, Finset.mem_range] at hp hp'
    simp only at heq
    have hii : i = i' := by
      have h1 : i ∈ insert i' Q' := heq ▸ Finset.mem_insert_self i Q
      have h2 : i' ∈ insert i Q := heq.symm ▸ Finset.mem_insert_self i' Q'
      rcases Finset.mem_insert.mp h1 with h | h
      · exact h
      · rcases Finset.mem_insert.mp h2 with h' | h'
        · exact h'.symm
        · exfalso
          have := hp'.2.2 i h
          have := hp.2.2 i' h'
          omega
    subst hii
    have hiQ : i ∉ Q := fun h => lt_irrefl _ (hp.2.2 i h)
    have hiQ' : i ∉ Q' := fun h => lt_irrefl _ (hp'.2.2 i h)
    have : Q = Q' := by
      rw [← Finset.erase_insert hiQ, heq, Finset.erase_insert hiQ']
    subst this; rfl
  · intro R hR
    rw [Finset.mem_powersetCard] at hR
    have hne : R.Nonempty := by
      rw [← Finset.card_pos, hR.2]; omega
    refine ⟨⟨R.erase (R.min' hne), R.min' hne⟩, ?_, ?_⟩
    · simp only [Finset.mem_sigma, Finset.mem_powersetCard, Finset.mem_filter, Finset.mem_range]
      refine ⟨⟨(Finset.erase_subset _ _).trans hR.1, ?_⟩, ?_, ?_⟩
      · rw [Finset.card_erase_of_mem (Finset.min'_mem _ _), hR.2]; rfl
      · exact Finset.mem_range.mp (hR.1 (Finset.min'_mem _ _))
      · intro q hq
        exact lt_of_le_of_ne (Finset.min'_le _ _ (Finset.mem_of_mem_erase hq))
          (fun h => (Finset.ne_of_mem_erase hq) h.symm)
    · simp only
      exact Finset.insert_erase (Finset.min'_mem _ _)

end Aux_Steiner_gap

open Aux_Steiner_gap in
theorem solution (n m : ℕ) (hm : 1 ≤ m) (hmn : m ≤ n) :
    (∑ Q ∈ (Finset.range n).powersetCard m,
        (((Finset.range n).filter fun i => ∀ q ∈ Q, i < q).card : ℝ)) / (n.choose m : ℝ) =
      ((n : ℝ) - m) / ((m : ℝ) + 1) := by
  rw [← Nat.cast_sum, count, Finset.card_powersetCard, Finset.card_range]
  have hpos : (0 : ℝ) < n.choose m := by exact_mod_cast Nat.choose_pos hmn
  have hkey := Nat.choose_succ_right_eq n m
  rw [div_eq_div_iff hpos.ne' (by positivity)]
  have : ((n.choose (m + 1) * (m + 1) : ℕ) : ℝ) = ((n.choose m * (n - m) : ℕ) : ℝ) := by
    rw [hkey]
  push_cast [Nat.cast_sub hmn] at this
  linarith
