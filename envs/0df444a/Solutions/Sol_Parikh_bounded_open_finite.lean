-- Prove2me | solution 1 for Parikh.bounded_open_finite
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T09:48:30.85348+00:00
-- url     : https://prove2.me/submissions/9e5169e0-f5d5-4436-b4dc-c30b083a3c09

module
public import Definitions.Def_LeanPool_Parikh_Counting
public import Mathlib.Computability.ContextFreeGrammar
public import Mathlib.Data.Set.Finite.List
public import Definitions.Def_LeanPool_Parikh_GrammarTrees

set_option autoImplicit true
@[expose] public section
public section
open Parikh
variable {T : Type*}
namespace Parikh
theorem _root_.solution [Finite T] (g : ContextFreeGrammar T) (H : ℕ) :
    {t : ParseTree T g.NT | ActiveOpen g t ∧ t.height ≤ H}.Finite := by
  classical
  have nodeHeight (r : ContextFreeRule T g.NT) (cs : List (ParseTree T g.NT)) :
      (ParseTree.node r cs).height = 1 + (cs.map ParseTree.height).foldl max 0 := by
    exact ParseTree.height.eq_3 r cs
  -- Fixed-length lists over a finite subtype cover every possible child list.
  have finiteLists {s : Set (ParseTree T g.NT)} (hs : s.Finite) (n : ℕ) :
      {cs : List (ParseTree T g.NT) | cs.length = n ∧ ∀ c ∈ cs, c ∈ s}.Finite := by
    let : Finite s := hs
    apply ((List.finite_length_eq s n).image (List.map Subtype.val)).subset
    intro cs hcs
    refine ⟨cs.attachWith (· ∈ s) hcs.2, ?_, ?_⟩
    · simpa using hcs.1
    · exact List.attachWith_map_subtype_val hcs.2
  -- At height zero, only finite terminals and active holes are available.
  have leaves :
      (Set.range (ParseTree.terminal (N := g.NT)) ∪
        ParseTree.hole '' (activeNonterminals g : Set g.NT)).Finite :=
    (Set.finite_range (ParseTree.terminal (T := T) (N := g.NT))).union
      ((activeNonterminals g).finite_toSet.image _)
  induction H with
  | zero =>
    apply leaves.subset
    rintro t ⟨⟨hv, ha⟩, hh⟩
    cases hv with
    | terminal a => exact Or.inl ⟨a, rfl⟩
    | hole A =>
      apply Or.inr
      refine ⟨A, ?_, rfl⟩
      apply ha A
      simp [ParseTree.holes]
    | node r cs hr hv roots =>
      rw [nodeHeight] at hh
      omega
  | succ H ih =>
    let family : Set (ParseTree T g.NT) :=
      {t | ActiveOpen g t ∧ t.height ≤ H}
    -- Each finite production fixes its arity; validity filters this finite superset.
    have nodes : (⋃ r ∈ (g.rules : Set (ContextFreeRule T g.NT)),
        ParseTree.node r '' {cs : List (ParseTree T g.NT) |
          cs.length = r.output.length ∧ ∀ c ∈ cs, c ∈ family}).Finite :=
      g.rules.finite_toSet.biUnion fun r _ => (finiteLists ih r.output.length).image _
    apply (leaves.union nodes).subset
    rintro t ⟨⟨hv, ha⟩, hh⟩
    cases hv with
    | terminal a => exact Or.inl (Or.inl ⟨a, rfl⟩)
    | hole A =>
      apply Or.inl ∘ Or.inr
      refine ⟨A, ?_, rfl⟩
      apply ha A
      simp [ParseTree.holes]
    | node r cs hr hv roots =>
      apply Or.inr
      apply Set.mem_iUnion₂.mpr
      refine ⟨r, hr, cs, ⟨?_, ?_⟩, rfl⟩
      · simpa using congrArg List.length roots
      · intro c hc
        refine ⟨⟨hv c hc, ?_⟩, ?_⟩
        · intro A hA
          apply ha A
          simp only [ParseTree.holes, ← List.flatMap_def, List.mem_flatMap]
          exact ⟨c, hc, hA⟩
        · have hm : c.height ∈ cs.map ParseTree.height := List.mem_map_of_mem hc
          have hmax := List.le_max_of_mem hm
          have hne := List.ne_nil_of_mem hm
          rw [nodeHeight, List.foldl_max_eq_max hne, Nat.zero_max] at hh
          omega
end Parikh
