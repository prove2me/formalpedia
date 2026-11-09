-- Prove2me | solution 1 for SmallLossGraph.proof_thm_3_4_negative_bias
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-08T16:38:40.721026+00:00
-- url     : https://prove2.me/submissions/c7744b51-ace7-491c-9267-06015c084639

import Mathlib
import Definitions.Def_SmallLossGraph_Protocol
import Definitions.Def_SmallLossGraph_Freezing

open scoped BigOperators

open SmallLossGraph in
theorem solution {d : ℕ} (G : SimpleGraph (Fin d)) (α : ℕ)
    (hα : IndepBound G α) (p : Fin d → ℝ) (hp0 : ∀ i, 0 ≤ p i) (hp1 : ∑ i, p i = 1)
    (ℓ : Fin d → ℝ) (hℓ : ∀ i, ℓ i ∈ Set.Icc (0 : ℝ) 1) (ε' : ℝ) (hε' : 0 < ε') (i : Fin d) :
    ∑ j, sampling G p (gamma ε' α) (gammaPrime ε' α) j *
        estLoss G ℓ p (gamma ε' α) (gammaPrime ε' α) j i ≤ ℓ i := by
  have hmem : ∀ j, i ∈ closedNbhd G j ↔ j ∈ closedNbhd G i := by
    intro j
    unfold closedNbhd
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro (h | h)
      · left; exact h.symm
      · right; exact h.symm
    · rintro (h | h)
      · left; exact h.symm
      · right; exact h.symm
  unfold estLoss
  by_cases hiF : i ∈ frozen G p (gamma ε' α) (gammaPrime ε' α)
  · rw [Finset.sum_eq_zero (fun j _ => by rw [if_neg (fun h => h.2 hiF), mul_zero])]
    exact (hℓ i).1
  · have hterm : ∀ j, sampling G p (gamma ε' α) (gammaPrime ε' α) j *
        (if i ∈ closedNbhd G j ∧ i ∉ frozen G p (gamma ε' α) (gammaPrime ε' α) then
          ℓ i / obsProb G p (gamma ε' α) (gammaPrime ε' α) i else 0) =
        if j ∈ closedNbhd G i then sampling G p (gamma ε' α) (gammaPrime ε' α) j *
          (ℓ i / obsProb G p (gamma ε' α) (gammaPrime ε' α) i) else 0 := by
      intro j
      by_cases hj : j ∈ closedNbhd G i
      · rw [if_pos ⟨(hmem j).2 hj, hiF⟩, if_pos hj]
      · rw [if_neg (fun h => hj ((hmem j).1 h.1)), if_neg hj, mul_zero]
    rw [Finset.sum_congr rfl (fun j _ => hterm j), Finset.sum_ite_mem, Finset.univ_inter,
      ← Finset.sum_mul]
    have hW : ∑ j ∈ closedNbhd G i, sampling G p (gamma ε' α) (gammaPrime ε' α) j =
        obsProb G p (gamma ε' α) (gammaPrime ε' α) i := rfl
    rw [hW]
    by_cases h0 : obsProb G p (gamma ε' α) (gammaPrime ε' α) i = 0
    · rw [h0, div_zero, mul_zero]; exact (hℓ i).1
    · rw [mul_div_cancel₀ _ h0]
