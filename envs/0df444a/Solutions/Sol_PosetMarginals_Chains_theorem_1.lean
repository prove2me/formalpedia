-- Prove2me | solution 1 for PosetMarginals.Chains.theorem_1
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-01T23:31:51.960967+00:00
-- url     : https://prove2.me/submissions/f8f97ea5-0ee6-4a5d-b347-ae2c711f756e

import Mathlib
import Definitions.Def_PosetMarginals_Chains_Model
import Theorems.Thm_PosetMarginals_Chains_proposition_1
import Theorems.Thm_PosetMarginals_Chains_theorem_2

open PosetMarginals.Chains

theorem solution {α : Type*} [PartialOrder α] [Fintype α] [Nonempty α]
    (ρ : α → ℝ) (π : Finset α → ℝ) (h : Standing ρ π) :
    ProblemD ρ π := by
  rw [proposition_1 ρ π h, theorem_2 ρ π h]
  unfold maxValue
  apply csSup_le
  · exact ⟨ρ (Classical.arbitrary α), Or.inl ⟨_, rfl⟩⟩
  · rintro v (⟨x, rfl⟩ | ⟨C, hC, rfl⟩)
    · exact (h.1 x).2
    · exact h.2.1 C hC
