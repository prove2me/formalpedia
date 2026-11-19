-- Prove2me | solution 1 for RobertsonSeymour2010.GM23.Immersion.no_descending_ideals
-- status  : ACCEPTED   (prove)
-- author  : @martelus trismortuus
-- created : 2026-11-18T16:53:21.825205+00:00
-- url     : https://prove2.me/submissions/cba8e5cf-a7f5-4d98-894b-4b84e9d5fbf3

import Definitions.Def_RobertsonSeymour2010_GM23_Immersion_QuasiOrders

open RobertsonSeymour2010.GM23.Immersion in
theorem solution (X : Type) (Ω : ℕ → QO X) (hΩ : (Ω 0).IsWQO) :
    ¬ ∀ i : ℕ, (Ω (i + 1)).IsProperIdeal (Ω i) := by
  intro h
  have anti : ∀ k l, k ≤ l → (Ω l).carrier ⊆ (Ω k).carrier := by
    intro k l hkl
    induction l, hkl using Nat.le_induction with
    | base => exact le_rfl
    | succ l _ ih => exact ((h l).1.1.1).trans ih
  have agree : ∀ k, ∀ x ∈ (Ω k).carrier, ∀ y ∈ (Ω k).carrier,
      ((Ω k).le x y ↔ (Ω 0).le x y) := by
    intro k
    induction k with
    | zero => intro x _ y _; exact Iff.rfl
    | succ k ih =>
      intro x hx y hy
      have hx' := (h k).1.1.1 hx
      have hy' := (h k).1.1.1 hy
      exact ((h k).1.1.2 x hx y hy).trans (ih x hx' y hy')
  have pick : ∀ i, ∃ x, x ∈ (Ω i).carrier ∧ x ∉ (Ω (i + 1)).carrier := by
    intro i
    by_contra hc
    push_neg at hc
    apply (h i).2
    refine ⟨Set.Subset.antisymm (h i).1.1.1 hc, ?_⟩
    exact (h i).1.1.2
  choose x hx using pick
  obtain ⟨i, j, hij, hle⟩ := hΩ x (fun n => anti 0 n (Nat.zero_le n) (hx n).1)
  have hxj : x j ∈ (Ω (i + 1)).carrier := anti (i + 1) j hij (hx j).1
  have hxj' : x j ∈ (Ω i).carrier := anti i (i + 1) (Nat.le_succ i) hxj
  have hle' : (Ω i).le (x i) (x j) := (agree i (x i) (hx i).1 (x j) hxj').2 hle
  exact (h i).1.2 ⟨x i, ⟨(hx i).1, (hx i).2⟩, x j, hxj, hle'⟩
