-- Prove2me | solution 1 for PI.SqfPrimeFactor.W.ana_pi
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T10:29:00.547193+00:00
-- url     : https://prove2.me/submissions/652cfee2-a928-4ec0-a823-e4d7ac413340

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_PrimesDyadicRS
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SquarefreePrimeFactor_AnaCore
import Theorems.Thm_PI_SqfPrimeFactor_W_ana_three

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.SqfPrimeFactor PI.SqfPrimeFactor.W
open Finset
namespace PI.SqfPrimeFactor.W
theorem _root_.solution (r : ℕ) (hr : 100 ≤ r) (S : Finset ℕ)
    (hS : ∀ p, p ∈ S ↔ p.Prime ∧ r < 2 * p ∧ p + 3 ≤ r) :
    Nat.primeCounting r ≤ Nat.primeCounting (r / 2) + S.card + 2 := by
  simp only [Nat.primeCounting, Nat.primeCounting', Nat.count_eq_card_filter_range]
  have hsub : (range (r + 1)).filter Nat.Prime ⊆
      ((range (r / 2 + 1)).filter Nat.Prime ∪ S) ∪
        ({r - 2, r - 1, r} : Finset ℕ).filter Nat.Prime := by
    intro p hp
    rw [mem_filter, mem_range] at hp
    obtain ⟨hp1, hpp⟩ := hp
    rw [mem_union, mem_union, mem_filter, mem_filter, mem_range, hS]
    by_cases h1 : p < r / 2 + 1
    · exact Or.inl (Or.inl ⟨h1, hpp⟩)
    by_cases h2 : p + 3 ≤ r
    · exact Or.inl (Or.inr ⟨hpp, by omega, h2⟩)
    refine Or.inr ⟨?_, hpp⟩
    simp only [mem_insert, mem_singleton]
    omega
  calc _ ≤ _ := card_le_card hsub
    _ ≤ _ := card_union_le _ _
    _ ≤ _ := Nat.add_le_add (card_union_le _ _) (ana_three r hr)
end PI.SqfPrimeFactor.W
