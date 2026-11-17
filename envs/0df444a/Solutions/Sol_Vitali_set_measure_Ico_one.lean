-- Prove2me | solution 1 for Vitali_set.measure_Ico_one
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-16T23:36:50.789593+00:00
-- url     : https://prove2.me/submissions/5711637c-f07e-4625-8d5d-ef0ee0e9a8a0

import Definitions.Def_ProbabilityTheory_chapter_02_thm_2_9_F000
import Definitions.Def_ProbabilityTheory_chapter_02_thm_2_9_F002
import Mathlib.Tactic
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Set
noncomputable section
namespace Vitali_set
end Vitali_set
section Vitali_set
open Vitali_set
/-- The right endpoint is disjoint from the unit half-open interval. -/
private theorem source_endpoint_disjoint :
    Disjoint (Set.Ico (0 : ℝ) 1) ({1} : Set ℝ) := by
  rw [Set.disjoint_left]
  intro x hx hx1
  have hxlt : x < 1 := hx.2
  have heq : x = 1 := hx1
  rw [heq] at hxlt
  exact (lt_irrefl (1 : ℝ)) hxlt


/-- The two-term support family is pairwise disjoint. -/
private theorem source_two_term_pairwise :
    Pairwise (fun i j : ℕ =>
      Disjoint
        (if i = 0 then Set.Ico (0 : ℝ) 1 else if i = 1 then {1} else ∅)
        (if j = 0 then Set.Ico (0 : ℝ) 1 else if j = 1 then {1} else ∅)) := by
  let f : ℕ → Set ℝ :=
    fun n => if n = 0 then Set.Ico 0 1 else if n = 1 then {1} else ∅
  change Pairwise (fun i j => Disjoint (f i) (f j))
  have h_disj := source_endpoint_disjoint
  intro i j hij
  dsimp [f]
  -- This splits into cases (0 vs 0), (0 vs 1), (1 vs 0), (1 vs 1), etc.
  split_ifs <;> try (simp; done)
  -- We are left with the diagonal cases (0 vs 0, 1 vs 1) which are contradictions,
  -- and the cross cases (0 vs 1, 1 vs 0) which are valid disjointness.
  -- We use a sequence of tactics to handle any of them order-independently.
  all_goals {
    try simp_all           -- Solves the contradictions (i=j vs i≠j)
    try exact h_disj       -- Solves Disjoint (Ico 0 1) {1}
    try exact h_disj.symm  -- Solves Disjoint {1} (Ico 0 1)
  }


/-- The support of the two-term family is exactly the closed unit interval. -/
private theorem source_two_term_union :
    (⋃ n : ℕ, if n = 0 then Set.Ico (0 : ℝ) 1
      else if n = 1 then {1} else ∅) = Set.Icc 0 1 := by
  let f : ℕ → Set ℝ :=
    fun n => if n = 0 then Set.Ico 0 1 else if n = 1 then {1} else ∅
  change (⋃ n, f n) = Set.Icc 0 1
  -- Apply extensionality first to match elements
  ext x
  constructor
  · intro hx
    -- Explicitly rewrite with mem_iUnion to ensure n is treated as ℕ
    rw [mem_iUnion] at hx
    rcases hx with ⟨n, hn⟩
    dsimp [f] at hn
    by_cases h0 : n = 0
    · subst h0; simp at hn; exact Ico_subset_Icc_self hn
    by_cases h1 : n = 1
    · subst h1; simp at hn; rw [hn]; exact right_mem_Icc.2 zero_le_one
    · -- If n is neither 0 nor 1, f n is empty, so x cannot be in it
      simp [h0, h1] at hn
  · -- Backward:  x ∈ Icc 0 1 → x ∈ ⋃ n, f n
    intro hx
    -- Rewrite hx using the decomposition lemma
    rw [mem_Icc] at hx
    -- Split cases on whether x is the endpoint 1 or inside [0, 1)
    by_cases h_eq : x = 1
    · -- Case x = 1: found in index 1
      rw [mem_iUnion]; use 1
      dsimp [f]; simp [h_eq]
    · -- Case x ≠ 1: found in index 0 (since 0 ≤ x ≤ 1 and x ≠ 1 implies x < 1)
      rw [mem_iUnion]; use 0
      dsimp [f]; rw [mem_Ico]
      exact ⟨hx.1, lt_of_le_of_ne hx.2 h_eq⟩


/-- A countable sum supported at indices zero and one. -/
private theorem source_two_term_tsum (m : Set ℝ → ENNReal)
    (h_empty : m ∅ = 0) :
    (∑' n : ℕ, m (if n = 0 then Set.Ico (0 : ℝ) 1
      else if n = 1 then {1} else ∅)) = m (Set.Ico 0 1) + m {1} := by
  let f : ℕ → Set ℝ :=
    fun n => if n = 0 then Set.Ico 0 1 else if n = 1 then {1} else ∅
  change (∑' n, m (f n)) = m (Set.Ico 0 1) + m {1}
  let s : Finset ℕ := {0, 1}
  -- Support condition
  have h_supp : ∀ n, n ∉ s → m (f n) = 0 := by
    intro n hn
    rw [Finset.mem_insert, Finset.mem_singleton] at hn
    push Not at hn
    dsimp [f]
    rw [if_neg hn.1, if_neg hn.2]
    exact h_empty

  rw [tsum_eq_sum h_supp]
  -- Expand finite sum {0, 1}
  rw [Finset.sum_pair (by norm_num : 0 ≠ 1)]
  dsimp [f]


private theorem source_vitali_half_open_additive
    (m : Set ℝ → ENNReal) (h : IsVitaliMeasure m) :
    m (Icc 0 1) = m (Ico 0 1) + m {1} := by
  rcases h with ⟨hd, he, hm, ha, ht, hl⟩
  let f : ℕ → Set ℝ := fun n => if n = 0 then Ico 0 1 else if n = 1 then {1} else ∅
  have hs : ∀ n, f n ⊆ I := by
    intro n
    dsimp [f]
    split_ifs <;> simp [I, Ico_subset_Icc_self]
  have hp : Pairwise (fun i j => Disjoint (f i) (f j)) := source_two_term_pairwise
  have hu : (⋃ n, f n) = Icc 0 1 := source_two_term_union
  have hsum : (∑' n, m (f n)) = m (Ico 0 1) + m {1} := source_two_term_tsum m he
  calc
    m (Icc 0 1) = m (⋃ n, f n) := by rw [hu]
    _ = ∑' n, m (f n) := ha f hs hp
    _ = m (Ico 0 1) + m {1} := hsum

theorem solution (m : Set ℝ → ENNReal) (h : IsVitaliMeasure m) :
    m (Ico 0 1) = 1 := by
  have had := source_vitali_half_open_additive m h
  have hsingle : m {1} = 0 :=
    measure_singleton_zero m h 1 (by simp [I])
  have hclosed : m (Icc 0 1) = 1 := by
    rcases h with ⟨_, _, _, _, _, hlen⟩
    simpa using hlen 0 1 le_rfl zero_le_one le_rfl
  rw [hclosed, hsingle, add_zero] at had
  exact had.symm
end Vitali_set
