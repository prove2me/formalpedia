-- Prove2me | solution 1 for SeymourMFMC.Binary.parity_decomposition
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-10-28T08:46:48.551352+00:00
-- url     : https://prove2.me/submissions/caeeff76-5743-4fbb-a740-42059edcc65d

import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Sym
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Sym.Sym2
import Mathlib.Data.List.Chain
import Mathlib.Data.List.Perm.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Ring.Parity
import Mathlib.Order.RelClasses
import Mathlib.Tactic.Linarith
import Definitions.Def_SeymourMFMC_Binary_ground
import Definitions.Def_SeymourMFMC_Binary_blocker
import Definitions.Def_SeymourMFMC_Binary_IsClutter
import Definitions.Def_SeymourMFMC_Binary_IsBinary
import Definitions.Def_SeymourMFMC_Binary_IsCircuit

open SeymourMFMC.Binary

private lemma exists_minimal_subset {α : Type*} [DecidableEq α] (P : Finset α → Prop) :
    ∀ (n : ℕ) (W : Finset α), W.card = n → P W →
      ∃ B ⊆ W, P B ∧ ∀ B' ∈ B.ssubsets, ¬ P B' := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro W hcard hPW
    by_cases hmin : ∀ B' ∈ W.ssubsets, ¬ P B'
    · exact ⟨W, Finset.Subset.rfl, hPW, hmin⟩
    · push Not at hmin
      rcases hmin with ⟨B', hB'ss, hPB'⟩
      rw [Finset.mem_ssubsets] at hB'ss
      have hlt : B'.card < n := hcard ▸ Finset.card_lt_card hB'ss
      rcases ih B'.card hlt B' rfl hPB' with ⟨B, hBB', hPB, hBmin⟩
      exact ⟨B, hBB'.trans hB'ss.subset, hPB, hBmin⟩

private lemma card_sdiff_inter_add {α : Type*} [DecidableEq α]
    {Z C : Finset α} (hCZ : C ⊆ Z) (B : Finset α) :
    ((Z \ C) ∩ B).card + (C ∩ B).card = (Z ∩ B).card := by
  rw [← Finset.card_union_of_disjoint]
  · congr 1
    rw [← Finset.union_inter_distrib_right, Finset.sdiff_union_of_subset hCZ]
  · rw [Finset.disjoint_left]
    intro x hx1 hx2
    rw [Finset.mem_inter, Finset.mem_sdiff] at hx1
    rw [Finset.mem_inter] at hx2
    exact hx1.1.2 hx2.1

private lemma part_a {α : Type*} [DecidableEq α] (L : Finset (Finset α)) :
    ∀ (n : ℕ) (Z : Finset α), Z.card = n → Z ⊆ ground L →
      (∀ B ∈ blocker L, Even (Z ∩ B).card) →
      ∃ Cs : Finset (Finset α), (∀ C ∈ Cs, IsCircuit L C) ∧
        (Cs : Set (Finset α)).PairwiseDisjoint id ∧ Cs.sup id = Z := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro Z hcard hZ heven
    rcases Z.eq_empty_or_nonempty with rfl | hZne
    · refine ⟨∅, ?_, ?_, Finset.sup_empty⟩
      · intro C hC
        exact False.elim (Finset.notMem_empty C hC)
      · simp
    · obtain ⟨C, hCZ, ⟨hCne, hCcyc⟩, hCmin⟩ :=
        exists_minimal_subset (fun C => C.Nonempty ∧ IsCycle L C) n Z hcard ⟨hZne, hZ, heven⟩
      have hCcirc : IsCircuit L C :=
        ⟨hCne, hCcyc, fun C' hC' hC'ne hC'cyc => hCmin C' hC' ⟨hC'ne, hC'cyc⟩⟩
      have hZ'ss : Z \ C ⊂ Z := Finset.sdiff_ssubset hCZ hCne
      have hZ'lt : (Z \ C).card < n := hcard ▸ Finset.card_lt_card hZ'ss
      have hZ'ground : Z \ C ⊆ ground L := Finset.sdiff_subset.trans hZ
      have hZ'even : ∀ B ∈ blocker L, Even ((Z \ C) ∩ B).card := by
        intro B hB
        have hsum := card_sdiff_inter_add hCZ B
        rcases heven B hB with ⟨k, hk⟩
        rcases hCcyc.2 B hB with ⟨m, hm⟩
        refine ⟨k - m, ?_⟩
        omega
      obtain ⟨Cs', hCs'1, hCs'2, hCs'3⟩ := ih (Z \ C).card hZ'lt (Z \ C) rfl hZ'ground hZ'even
      have hdisj : ∀ C' ∈ Cs', Disjoint C C' := by
        intro C' hC'
        have hC'sub : C' ⊆ Z \ C := by
          rw [← hCs'3]
          exact Finset.le_sup (f := id) hC'
        rw [Finset.disjoint_left]
        intro x hxC hxC'
        exact (Finset.mem_sdiff.mp (hC'sub hxC')).2 hxC
      refine ⟨insert C Cs', ?_, ?_, ?_⟩
      · intro C' hC'
        rcases Finset.mem_insert.mp hC' with rfl | hC'
        · exact hCcirc
        · exact hCs'1 C' hC'
      · rw [Finset.coe_insert, Set.pairwiseDisjoint_insert]
        exact ⟨hCs'2, fun C' hC' _ => hdisj C' hC'⟩
      · rw [Finset.sup_insert, id_eq, hCs'3]
        exact Finset.union_sdiff_of_subset hCZ

theorem solution {α : Type*} [DecidableEq α] (L : Finset (Finset α))
    (hL : IsClutter L) (hbin : IsBinary L) (Z : Finset α) (hZ : Z ⊆ ground L) :
    ((∀ B ∈ blocker L, Even (Z ∩ B).card) →
      ∃ Cs : Finset (Finset α), (∀ C ∈ Cs, IsCircuit L C) ∧
        (Cs : Set (Finset α)).PairwiseDisjoint id ∧ Cs.sup id = Z) ∧
    ((∀ B ∈ blocker L, Odd (Z ∩ B).card) →
      ∃ A ∈ L, ∃ Cs : Finset (Finset α), (∀ C ∈ Cs, IsCircuit L C) ∧
        (Cs : Set (Finset α)).PairwiseDisjoint id ∧ (∀ C ∈ Cs, Disjoint C A) ∧
        A ∪ Cs.sup id = Z) := by
  have _ := hL
  refine ⟨fun heven => part_a L Z.card Z rfl hZ heven, fun hodd => ?_⟩
  have hexA : ∃ A ∈ L, A ⊆ Z := by
    by_contra hno
    push Not at hno
    have hMW : Meets L (ground L \ Z) := by
      intro A hA
      obtain ⟨x, hxA, hxZ⟩ := Finset.not_subset.mp (hno A hA)
      have hxG : x ∈ ground L := Finset.le_sup (f := id) hA hxA
      exact ⟨x, Finset.mem_inter.mpr ⟨hxA, Finset.mem_sdiff.mpr ⟨hxG, hxZ⟩⟩⟩
    obtain ⟨B, hBW, hMB, hBmin⟩ :=
      exists_minimal_subset (Meets L) (ground L \ Z).card (ground L \ Z) rfl hMW
    have hB : B ∈ blocker L := by
      rw [blocker, Finset.mem_filter, Finset.mem_powerset]
      exact ⟨hBW.trans Finset.sdiff_subset, hMB, hBmin⟩
    have hZB : Z ∩ B = ∅ := by
      rw [Finset.eq_empty_iff_forall_notMem]
      intro x hx
      rw [Finset.mem_inter] at hx
      exact (Finset.mem_sdiff.mp (hBW hx.2)).2 hx.1
    rcases hodd B hB with ⟨k, hk⟩
    rw [hZB, Finset.card_empty] at hk
    omega
  rcases hexA with ⟨A, hA, hAZ⟩
  have hZ'even : ∀ B ∈ blocker L, Even ((Z \ A) ∩ B).card := by
    intro B hB
    have hsum := card_sdiff_inter_add hAZ B
    rcases hodd B hB with ⟨k, hk⟩
    rcases hbin A hA B hB with ⟨m, hm⟩
    refine ⟨k - m, ?_⟩
    omega
  obtain ⟨Cs, hCs1, hCs2, hCs3⟩ :=
    part_a L (Z \ A).card (Z \ A) rfl (Finset.sdiff_subset.trans hZ) hZ'even
  refine ⟨A, hA, Cs, hCs1, hCs2, ?_, ?_⟩
  · intro C hC
    have hCsub : C ⊆ Z \ A := by
      rw [← hCs3]
      exact Finset.le_sup (f := id) hC
    rw [Finset.disjoint_left]
    intro x hxC hxA
    exact (Finset.mem_sdiff.mp (hCsub hxC)).2 hxA
  · rw [hCs3, Finset.union_sdiff_of_subset hAZ]
