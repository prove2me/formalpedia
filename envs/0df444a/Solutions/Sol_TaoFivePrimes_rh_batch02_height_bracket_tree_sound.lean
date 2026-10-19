-- Prove2me | solution 1 for TaoFivePrimes.rh_batch02_height_bracket_tree_sound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-18T13:55:01.418381+00:00
-- url     : https://prove2.me/submissions/01427771-77d8-4459-9188-4e0615670bbb

import Definitions.Def_TaoFivePrimes_RHBatch02HeightBracketInterface

open RHBatch02HeightBracketData RHBatch02HeightBracketInterface

/-- Every bracket tree has at least one leaf. -/
private lemma leaves_ne {l r n : Nat} (t : Tree l r n) : leaves t ≠ [] := by
  induction t with
  | leaf b => simp [leaves]
  | join u v _ ih1 _ => simp [leaves, ih1]

/-- The leaves of a bracket tree have the advertised count, are ordered by increasing
brackets, and lie inside the span of the tree. -/
theorem solution {l r n : Nat} (t : Tree l r n) :
    (leaves t).length = n ∧
    (leaves t).Pairwise (fun p q => p.r ≤ q.l) ∧
    (∀ p ∈ leaves t, l ≤ p.l ∧ p.r ≤ r) := by
  induction t with
  | leaf b =>
      simp only [leaves]
      refine ⟨rfl, ?_, ?_⟩
      · exact List.pairwise_singleton _ _
      · intro p hp
        simp only [List.mem_singleton] at hp
        subst hp
        exact ⟨le_refl _, le_refl _⟩
  | @join l₁ r₁ n₁ l₂ r₂ n₂ u v hord ihu ihv =>
      obtain ⟨hu1, hu2, hu3⟩ := ihu
      obtain ⟨hv1, hv2, hv3⟩ := ihv
      obtain ⟨q, hq⟩ := List.exists_mem_of_ne_nil _ (leaves_ne u)
      obtain ⟨q', hq'⟩ := List.exists_mem_of_ne_nil _ (leaves_ne v)
      obtain ⟨hql, hqr⟩ := hu3 q hq
      obtain ⟨hq'l, hq'r⟩ := hv3 q' hq'
      have hlq : q.l ≤ q.r := le_of_lt q.bound.1
      have hlq' : q'.l ≤ q'.r := le_of_lt q'.bound.1
      have h12 : l₁ ≤ l₂ := le_trans hql (le_trans hlq (le_trans hqr hord))
      have h2r : l₂ ≤ r₂ := le_trans hq'l (le_trans hlq' hq'r)
      simp only [leaves]
      refine ⟨?_, ?_, ?_⟩
      · rw [List.length_append, hu1, hv1]
      · rw [List.pairwise_append]
        refine ⟨hu2, hv2, ?_⟩
        intro a ha b hb
        have ha' := (hu3 a ha).2
        have hb' := (hv3 b hb).1
        omega
      · intro p hp
        rw [List.mem_append] at hp
        rcases hp with hp | hp
        · obtain ⟨hpl, hpr⟩ := hu3 p hp
          exact ⟨hpl, le_trans hpr (le_trans hord h2r)⟩
        · obtain ⟨hpl, hpr⟩ := hv3 p hp
          exact ⟨le_trans h12 hpl, hpr⟩
