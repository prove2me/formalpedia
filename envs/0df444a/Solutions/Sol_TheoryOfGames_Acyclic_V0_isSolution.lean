-- Prove2me | solution 1 for TheoryOfGames.Acyclic.V0_isSolution
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-03T00:58:59.561982+00:00
-- url     : https://prove2.me/submissions/be37c509-199d-4435-8bf1-741c398309e1

import Mathlib
import Definitions.Def_TheoryOfGames_Acyclic_Solution
import Definitions.Def_TheoryOfGames_Acyclic_Acyclicity
import Definitions.Def_TheoryOfGames_Acyclic_Construction

set_option autoImplicit false

namespace P2M96d6b2bf

open TheoryOfGames.Acyclic

theorem mem_succ {α : Type*} (D : Set α) (S : α → α → Prop) (k : ℕ) (y : α) :
    y ∈ stageA D S (k+1) ↔ y ∈ stageA D S k ∧ y ∉ maxima (stageA D S k) S ∧
      ¬ ∃ x ∈ maxima (stageA D S k) S, S x y := by
  simp only [stageA, Set.mem_diff, Set.mem_setOf_eq]
  constructor
  · rintro ⟨⟨h1, h2⟩, h3⟩
    exact ⟨h1, h2, fun h => h3 ⟨h1, h⟩⟩
  · rintro ⟨h1, h2, h3⟩
    exact ⟨⟨h1, h2⟩, fun h => h3 h.2⟩

theorem succ_sub {α : Type*} (D : Set α) (S : α → α → Prop) (k : ℕ) :
    stageA D S (k+1) ⊆ stageA D S k := fun y hy => ((mem_succ D S k y).1 hy).1

theorem anti {α : Type*} (D : Set α) (S : α → α → Prop) : Antitone (stageA D S) :=
  antitone_nat_of_succ_le (succ_sub D S)

theorem sub_D {α : Type*} (D : Set α) (S : α → α → Prop) (k : ℕ) : stageA D S k ⊆ D :=
  anti D S (Nat.zero_le k)

theorem maxima_nonempty {α : Type*} (D : Set α) (S : α → α → Prop) (hS : IsAcyclic D S)
    (E : Set α) (hE : E ⊆ D) (hfin : E.Finite) (hne : E.Nonempty) : (maxima E S).Nonempty := by
  by_contra hno
  have h : ∀ x : E, ∃ y : E, S y.1 x.1 := by
    intro x
    by_contra hx
    push_neg at hx
    exact hno ⟨x.1, x.2, fun y hy => hx ⟨y, hy⟩⟩
  choose f hf using h
  haveI : Finite E := hfin.to_subtype
  obtain ⟨x0, hx0⟩ := hne
  obtain ⟨i, j, hij, heq⟩ :=
    Finite.exists_ne_map_eq_of_infinite (fun n : ℕ => f^[n] ⟨x0, hx0⟩)
  have key : ∀ i j : ℕ, i < j → f^[i] ⟨x0, hx0⟩ = f^[j] ⟨x0, hx0⟩ → False := by
    intro i j hlt he
    refine hS (j - i) (by omega) (fun n => (f^[i+n] ⟨x0, hx0⟩).1) ?_ ?_ ?_
    · intro n _
      exact hE (f^[i+n] ⟨x0, hx0⟩).2
    · show (f^[i + (j - i)] ⟨x0, hx0⟩).1 = (f^[i + 0] ⟨x0, hx0⟩).1
      rw [show i + (j - i) = j by omega, Nat.add_zero, ← he]
    · intro n _
      show S (f^[i + (n+1)] ⟨x0, hx0⟩).1 (f^[i+n] ⟨x0, hx0⟩).1
      rw [show i + (n+1) = (i+n) + 1 by omega, Function.iterate_succ_apply']
      exact hf _
  rcases lt_or_gt_of_ne hij with h | h
  · exact key i j h heq
  · exact key j i h heq.symm

theorem ncard_lt {α : Type*} (D : Set α) (S : α → α → Prop) (hS : IsAcyclic D S)
    (hD : D.Finite) (k : ℕ) (hne : (stageA D S k).Nonempty) :
    (stageA D S (k+1)).ncard < (stageA D S k).ncard := by
  obtain ⟨b, hb⟩ :=
    maxima_nonempty D S hS (stageA D S k) (sub_D D S k) (hD.subset (sub_D D S k)) hne
  have hb' : b ∈ stageA D S k ∧ ∀ z ∈ stageA D S k, ¬ S z b := hb
  apply Set.ncard_lt_ncard _ (hD.subset (sub_D D S k))
  refine (Set.ssubset_iff_of_subset (succ_sub D S k)).2 ⟨b, hb'.1, fun h => ?_⟩
  exact ((mem_succ D S k b).1 h).2.1 hb

theorem eventually_empty {α : Type*} (D : Set α) (S : α → α → Prop) (hD : D.Finite)
    (hS : IsAcyclic D S) : stageA D S (D.ncard + 1) = ∅ := by
  have h : ∀ k, stageA D S k = ∅ ∨ (stageA D S k).ncard + k ≤ D.ncard := by
    intro k
    induction k with
    | zero =>
      right
      show D.ncard + 0 ≤ D.ncard
      omega
    | succ k ih =>
      rcases (stageA D S k).eq_empty_or_nonempty with he | hne
      · left
        exact Set.subset_eq_empty (succ_sub D S k) he
      · rcases ih with h0 | h1
        · exact absurd h0 hne.ne_empty
        · right
          have := ncard_lt D S hS hD k hne
          omega
  rcases h (D.ncard + 1) with h | h
  · exact h
  · omega

theorem main {α : Type*} (D : Set α) (S : α → α → Prop)
    (hD : D.Finite) (hS : IsAcyclic D S) :
    IsSolution D S (V0 D S) := by
  unfold IsSolution
  ext y
  simp only [Set.mem_setOf_eq]
  constructor
  · intro hy
    obtain ⟨k, hk⟩ := Set.mem_iUnion.1 hy
    have hk' : y ∈ stageA D S k ∧ ∀ z ∈ stageA D S k, ¬ S z y := hk
    refine ⟨sub_D D S k hk'.1, ?_⟩
    intro x hx hxy
    obtain ⟨j, hj⟩ := Set.mem_iUnion.1 hx
    have hj' : x ∈ stageA D S j ∧ ∀ z ∈ stageA D S j, ¬ S z x := hj
    rcases lt_or_ge j k with hjk | hjk
    · have hyA : y ∈ stageA D S (j+1) := anti D S (show j+1 ≤ k by omega) hk'.1
      exact ((mem_succ D S j y).1 hyA).2.2 ⟨x, hj, hxy⟩
    · exact hk'.2 x (anti D S hjk hj'.1) hxy
  · rintro ⟨hyD, hno⟩
    have h : ∀ k, y ∈ stageA D S k ∨ y ∈ V0 D S := by
      intro k
      induction k with
      | zero => left; exact hyD
      | succ k ih =>
        rcases ih with h | h
        · by_cases hb : y ∈ maxima (stageA D S k) S
          · right; exact Set.mem_iUnion.2 ⟨k, hb⟩
          · by_cases hc : ∃ x ∈ maxima (stageA D S k) S, S x y
            · obtain ⟨x, hx, hxy⟩ := hc
              exact absurd hxy (hno x (Set.mem_iUnion.2 ⟨k, hx⟩))
            · left; exact (mem_succ D S k y).2 ⟨h, hb, hc⟩
        · right; exact h
    rcases h (D.ncard + 1) with h | h
    · rw [eventually_empty D S hD hS] at h
      exact absurd h (Set.notMem_empty y)
    · exact h

end P2M96d6b2bf

open TheoryOfGames.Acyclic in
theorem solution {α : Type*} (D : Set α) (S : α → α → Prop)
    (hD : D.Finite) (hS : IsAcyclic D S) :
    IsSolution D S (V0 D S) := by
  exact P2M96d6b2bf.main D S hD hS
