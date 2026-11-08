-- Prove2me | solution 1 for UltrametricFit.claim_8
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-07T15:20:29.350461+00:00
-- url     : https://prove2.me/submissions/e177d3a1-318f-4756-83bc-6b071aebdb68

import Mathlib
import Definitions.Def_UltrametricFit_IsMergeNode

open UltrametricFit in
theorem solution {n : ℕ} (d : Fin n → Fin n → ℝ) (hd : UltrametricFit.IsPseudometric d) (δ : ℝ) (hδ : 0 ≤ δ)
    (A : Finset (Fin n)) (hA : UltrametricFit.IsMergeNode d δ A) :
    UltrametricFit.avgDist d A A ≤ δ := by
  have main : A.Nonempty ∧ ∑ i ∈ A, ∑ j ∈ A, d i j ≤ δ * ((A.card : ℝ) * A.card) := by
    induction hA with
    | singleton i => simp [hd.self, hδ]
    | union A1 A2 h1 h2 hdisj havg ih1 ih2 =>
      obtain ⟨n1, s1⟩ := ih1
      obtain ⟨n2, s2⟩ := ih2
      refine ⟨n1.mono Finset.subset_union_left, ?_⟩
      have hc1 : (0:ℝ) < A1.card := by exact_mod_cast n1.card_pos
      have hc2 : (0:ℝ) < A2.card := by exact_mod_cast n2.card_pos
      have h12 : ∑ i ∈ A1, ∑ j ∈ A2, d i j ≤ δ * ((A1.card : ℝ) * A2.card) := by
        unfold UltrametricFit.avgDist at havg
        rwa [div_le_iff₀ (mul_pos hc1 hc2)] at havg
      have h21 : ∑ i ∈ A2, ∑ j ∈ A1, d i j = ∑ i ∈ A1, ∑ j ∈ A2, d i j := by
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => hd.symm j i))
      rw [Finset.card_union_of_disjoint hdisj]
      simp_rw [Finset.sum_union hdisj, Finset.sum_add_distrib]
      push_cast
      nlinarith [h12, h21, s1, s2]
  obtain ⟨hne, hs⟩ := main
  have hc : (0:ℝ) < A.card := by exact_mod_cast hne.card_pos
  unfold UltrametricFit.avgDist
  rw [div_le_iff₀ (mul_pos hc hc)]
  exact hs
