-- Prove2me | solution 1 for Research.radiusSixDirected_card_eq_twice_ordered
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T18:13:45.889781+00:00
-- url     : https://prove2.me/submissions/b2644c6a-aa02-492e-9e0b-c8c503c4d908

module
public import Definitions.Def_Research_TriangularShells
public import Definitions.Def_Research_GlobalShellSix
public import Theorems.Thm_Research_mem_radiusSixDirectedPairs_iff
public import Theorems.Thm_Research_swap_mem_radiusSixDirectedPairs_iff

set_option autoImplicit true
@[expose] public section
public section
open Research
set_option maxRecDepth 100000
attribute [local instance] Research.prodLexLinearOrder
namespace Research
theorem _root_.solution {α : Type*}
    [Fintype α] [DecidableEq α] [LinearOrder α] (p : α → ℝ × ℝ) :
    (radiusSixDirectedPairs p).card =
      2 * (radiusSixOrderedPairs p).card := by
  classical
  let inc := radiusSixDirectedPairs p
  let lower := inc.filter fun q : α × α => q.1 < q.2
  let upper := inc.filter fun q : α × α => q.2 < q.1
  have hlower : lower = radiusSixOrderedPairs p := by
    ext q
    simp only [lower, inc, radiusSixOrderedPairs, radiusSixDirectedPairs,
      Finset.mem_filter]
    aesop
  have hsplit : lower ∪ upper = inc := by
    ext q
    simp only [lower, upper, Finset.mem_union, Finset.mem_filter]
    constructor
    · rintro (h | h) <;> exact h.1
    · intro hq
      have hne : q.1 ≠ q.2 :=
        (mem_radiusSixDirectedPairs_iff p q).mp hq |>.1
      rcases lt_or_gt_of_ne hne with hlt | hgt
      · exact Or.inl ⟨hq, hlt⟩
      · exact Or.inr ⟨hq, hgt⟩
  have hdisj : Disjoint lower upper := by
    rw [Finset.disjoint_left]
    intro q hql hqu
    exact (not_lt_of_ge (le_of_lt (Finset.mem_filter.mp hql).2))
      (Finset.mem_filter.mp hqu).2
  have hcards : lower.card = upper.card := by
    apply Finset.card_bij (fun q _ => q.swap)
    · intro q hq
      apply Finset.mem_filter.mpr
      exact ⟨(swap_mem_radiusSixDirectedPairs_iff p q).mpr
        (Finset.mem_filter.mp hq).1, (Finset.mem_filter.mp hq).2⟩
    · intro a ha b hb hab
      exact Prod.swap_injective hab
    · intro b hb
      refine ⟨b.swap, ?_, Prod.swap_swap b⟩
      apply Finset.mem_filter.mpr
      exact ⟨(swap_mem_radiusSixDirectedPairs_iff p b).mpr
        (Finset.mem_filter.mp hb).1, (Finset.mem_filter.mp hb).2⟩
  have hc := Finset.card_union_of_disjoint hdisj
  calc
    inc.card = lower.card + upper.card := by rw [← hsplit]; exact hc
    _ = lower.card + lower.card := by rw [← hcards]
    _ = 2 * lower.card := by omega
    _ = 2 * (radiusSixOrderedPairs p).card := by rw [hlower]
end Research
