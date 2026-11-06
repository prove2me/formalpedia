-- Prove2me | solution 1 for ProductFraming.Nest.theorem_2
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-05T06:49:32.643783+00:00
-- url     : https://prove2.me/submissions/8bfe70f6-0658-4afb-96cf-a0988fb98f7e

import Mathlib
import Definitions.Def_ProductFraming_Nest_Model

open Finset ProductFraming.Nest

theorem solution (n m p : ℕ) (hm : 1 ≤ m) (hp : 1 ≤ p) (r : Fin n → ℝ)
    (P : Fin n → Finset (Fin n) → ℝ) (hP : IsChoiceModel P) (lam : ℕ → ℝ) (hlam : IsPageLaw m lam) :
    Vopt n m p r P lam ≤ ∑ x ∈ Icc 1 m, lam x * U p r P x := by
  classical
  unfold Vopt
  apply Finset.sup'_le
  intro f hf
  simp only [feasibleFramings, mem_filter, mem_univ, true_and] at hf
  unfold V
  apply sum_le_sum
  intro x hx
  apply mul_le_mul_of_nonneg_left _ (hlam.1 x hx)
  have hxm := (mem_Icc.mp hx).2
  -- the consideration set has at most `x * p` elements
  have hcard : (consideration (fun i => ((f i : Fin (m + 1)) : ℕ)) x).card ≤ x * p := by
    have hsub : consideration (fun i => ((f i : Fin (m + 1)) : ℕ)) x ⊆
        (Icc 1 x).biUnion (fun j => univ.filter (fun i => ((f i : Fin (m + 1)) : ℕ) = j)) := by
      intro k hk
      simp only [consideration, mem_filter, mem_univ, true_and] at hk
      simp only [mem_biUnion, mem_Icc, mem_filter, mem_univ, true_and]
      exact ⟨_, ⟨hk.1, hk.2⟩, rfl⟩
    refine le_trans (card_le_card hsub) (le_trans card_biUnion_le ?_)
    have : ∑ j ∈ Icc 1 x, (univ.filter (fun i => ((f i : Fin (m + 1)) : ℕ) = j)).card
        ≤ ∑ _j ∈ Icc 1 x, p := by
      apply sum_le_sum
      intro j hj
      rw [mem_Icc] at hj
      exact hf.2 j (mem_Icc.mpr ⟨hj.1, le_trans hj.2 hxm⟩)
    simpa using this
  unfold U G
  apply Finset.le_sup' (R r P)
  simpa using hcard
