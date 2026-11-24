-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.AI.length_ne_top_iff_support
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:19:36.395287+00:00
-- url     : https://prove2.me/submissions/7521392d-0360-4a5f-b047-b94f6c523062

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_LengthEqRangeAddRange
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_LengthCokerEqKerAddDimOneOrderSum
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AI_length_quot_prime_ne_top_iff

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.AI
open Module PrimeSpectrum
open scoped Pointwise
universe u v
variable {A : Type u} [CommRing A] [IsNoetherianRing A]
namespace ReciprocityTheory.ChartRestriction.G.AI
theorem _root_.solution (N : Type v) [AddCommGroup N] [Module A N] [Module.Finite A N] :
    length A N ≠ ⊤ ↔ ∀ p ∈ support A N, p.asIdeal.IsMaximal := by
  refine IsNoetherianRing.induction_on_isQuotientEquivQuotientPrime (A := A) ‹_›
    (motive := fun N _ _ _ => length A N ≠ ⊤ ↔ ∀ p ∈ support A N, p.asIdeal.IsMaximal) ?_ ?_ ?_
  · intro N _ _ _ _
    simp [Module.length_eq_zero, Module.support_eq_empty]
  · intro N _ _ _ q e
    rw [e.length_eq, e.support_eq, length_quot_prime_ne_top_iff]
    have hs : support A (A ⧸ q.asIdeal) = zeroLocus (q.asIdeal : Set A) := by
      rw [Module.support_eq_zeroLocus, Ideal.annihilator_quotient]
    rw [hs]
    constructor
    · intro hq p hp
      rw [mem_zeroLocus, SetLike.coe_subset_coe] at hp
      rw [← hq.eq_of_le p.isPrime.ne_top hp]
      exact hq
    · intro h
      exact h q (by simp)
  · intro N₁ _ _ _ N₂ _ _ _ N₃ _ _ _ f g hf hg hex h1 h3
    rw [Module.length_eq_add_of_exact f g hf hg hex, Module.support_of_exact hex hf hg]
    rw [show length A N₁ + length A N₃ ≠ ⊤ ↔ length A N₁ ≠ ⊤ ∧ length A N₃ ≠ ⊤ from
      WithTop.add_ne_top, h1, h3]
    simp only [Set.mem_union]
    constructor
    · rintro ⟨a, b⟩ p (hp | hp)
      exacts [a p hp, b p hp]
    · intro h
      exact ⟨fun p hp => h p (Or.inl hp), fun p hp => h p (Or.inr hp)⟩
end ReciprocityTheory.ChartRestriction.G.AI
