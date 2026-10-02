-- Prove2me | solution 1 for OPG37364.not_hasMatchingCut_of_smallCut_expansion
-- status  : ACCEPTED   (prove)
-- author  : @arexychen
-- created : 2026-09-09T09:06:41.848336+00:00
-- url     : https://prove2.me/submissions/dbf9efd6-bba6-4d64-b7cd-5fc18edba039

import Definitions.Def_opg37364_cut_pairs

set_option autoImplicit false

universe u

namespace OPG37364

variable {V : Type u} {G : SimpleGraph V} {A : Set V}

/-- Taking the complementary shore preserves the original matching-cut predicate. -/
theorem IsMatchingCut.compl (hA : IsMatchingCut G A) : IsMatchingCut G Aᶜ := by
  refine ⟨hA.2.1, ?_, ?_⟩
  · simpa only [compl_compl] using hA.1
  · intro v x y hvx hx hvy hy
    apply hA.2.2 hvx ?_ hvy ?_
    · simpa only [Set.mem_compl_iff, not_not, or_comm, and_comm] using hx
    · simpa only [Set.mem_compl_iff, not_not, or_comm, and_comm] using hy

/-- The first coordinate is injective on the crossing pairs of a matching cut. -/
theorem IsMatchingCut.injOn_fst_cutPairs (hA : IsMatchingCut G A) :
    Set.InjOn Prod.fst (cutPairs G A) := by
  rintro ⟨v, x⟩ ⟨hv, hx, hvx⟩ ⟨w, y⟩ ⟨hw, hy, hwy⟩ hvw
  change v = w at hvw
  subst w
  have hxy : x = y := hA.2.2 hvx (Or.inl ⟨hv, hx⟩) hwy (Or.inl ⟨hv, hy⟩)
  exact Prod.ext rfl hxy

/-- A matching cut has at most one crossing pair per vertex of its chosen shore. -/
theorem IsMatchingCut.cutPairs_encard_le (hA : IsMatchingCut G A) :
    (cutPairs G A).encard ≤ A.encard := by
  apply Set.encard_le_encard_of_injOn (f := Prod.fst)
  · intro e he
    exact he.1
  · exact hA.injOn_fst_cutPairs

end OPG37364

open OPG37364

theorem solution {V : Type u} {G : SimpleGraph V} [Finite V]
    (hExpansion : ∀ S : Set V, S.Nonempty → Sᶜ.Nonempty →
      S.encard ≤ Sᶜ.encard → S.encard < (cutPairs G S).encard) :
    ¬ HasMatchingCut G := by
  rintro ⟨A, hA⟩
  rcases le_total A.encard Aᶜ.encard with hsmall | hsmall
  · exact (not_lt_of_ge hA.cutPairs_encard_le)
      (hExpansion A hA.1 hA.2.1 hsmall)
  · have hAc : IsMatchingCut G Aᶜ := hA.compl
    have hsmall' : Aᶜ.encard ≤ Aᶜᶜ.encard := by
      simpa only [compl_compl] using hsmall
    exact (not_lt_of_ge hAc.cutPairs_encard_le)
      (hExpansion Aᶜ hAc.1 hAc.2.1 hsmall')
