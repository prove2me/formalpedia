-- Prove2me | solution 1 for ThreeSum.TernaryCoverRankFibers.affineFiber_card_le_pow_finrank
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T08:13:18.477476+00:00
-- url     : https://prove2.me/submissions/335e19be-2bed-49b4-8e58-947f2fd2c4b1

import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Finset.Card
import Mathlib.Tactic
import Definitions.Def_Submission_ThreeSum_TernaryCoverRankFibers
import Theorems.Thm_ThreeSum_TernaryCoverRankFibers_affineFiber_card_le_of_proper
import Theorems.Thm_ThreeSum_TernaryCoverRankFibers_affineFiber_card_le_one

set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.TernaryCoverRankFibers
open Finset
variable {K : Type*} [Field K]
variable {E ι : Type*} [Fintype E] [Fintype ι] [DecidableEq K]
namespace ThreeSum.TernaryCoverRankFibers
theorem _root_.solution (left right : E → ι → K) (P : ℕ)
    (hinj : Function.Injective (fun e => (left e, right e)))
    (hE : Fintype.card E ≤ P ^ 2)
    (hprojection : ∀ β γ : K, (β ≠ 0 ∨ γ ≠ 0) → ∀ q : ι → K,
      (projectionFiber left right β γ q).card ≤ P)
    (V : Submodule K (K × K)) (offset : ι → K × K) :
    (affineFiber left right V offset).card ≤ P ^ Module.finrank K V := by
  classical
  have hdim : Module.finrank K V ≤ 2 := by
    simpa using Submodule.finrank_le V
  have hcases : Module.finrank K V = 0 ∨ Module.finrank K V = 1 ∨ Module.finrank K V = 2 := by omega
  rcases hcases with h0 | h1 | h2
  · have hV : V = ⊥ := Submodule.finrank_eq_zero.mp h0
    rw [h0, hV, pow_zero]
    exact affineFiber_card_le_one left right hinj offset
  · have hV : V ≠ ⊤ := by
      intro heq
      have h := h1
      rw [heq] at h
      norm_num at h
    rw [h1, pow_one]
    exact affineFiber_card_le_of_proper left right P hprojection V hV offset
  · rw [h2]
    exact (card_le_card (filter_subset ..)).trans (by simpa using hE)
end ThreeSum.TernaryCoverRankFibers
