-- Prove2me | solution 1 for PancakeHard.property_8
-- status  : ACCEPTED   (prove)
-- author  : @Ethan Cheung Wang
-- created : 2026-11-09T07:53:28.344993+00:00
-- url     : https://prove2.me/submissions/af3cf49b-37f3-4f0c-8543-2c8501e54fb7

import Mathlib
import Definitions.Def_PancakeHard_Literals
import Theorems.Thm_PancakeHard_property_5

set_option autoImplicit false

namespace PancakeHard

private def litBlock (p : ℕ) (O I : Finset ℕ) (j : ℕ) : List ℕ :=
  if j + 1 ∈ O then lockOpen (p + 12 * j)
  else if j + 1 ∈ I then interval (p + 12 * j + 1) (p + 12 * j + 12)
  else lockSeq (p + 12 * j)

private lemma literals_eq_flatMap (p m : ℕ) (O I : Finset ℕ) :
    literals p m O I = (List.range m).flatMap (litBlock p O I) := by
  rfl

private lemma range_split (a b : ℕ) :
    List.range (a + 1 + b) =
      List.range a ++ [a] ++ (List.range b).map (fun k => a + 1 + k) := by
  have hs : List.range (a + 1) = List.range a ++ [a] := by
    rw [List.range_add]; simp [List.range_one]
  calc
    List.range (a + 1 + b)
        = List.range ((a + 1) + b) := rfl
    _ = List.range (a + 1) ++ (List.range b).map (fun k => (a + 1) + k) := by
        rw [List.range_add]
    _ = (List.range a ++ [a]) ++ (List.range b).map (fun k => (a + 1) + k) := by
        rw [hs]
    _ = List.range a ++ [a] ++ (List.range b).map (fun k => a + 1 + k) := by
        simp [List.append_assoc]

private lemma litBlock_prefix (p : ℕ) (O I : Finset ℕ) (i j : ℕ)
    (hj : j < i - 1) (hi1 : 1 ≤ i) :
    litBlock p (insert i O) I j = litBlock p O I j := by
  have : j + 1 ≠ i := by omega
  simp [litBlock, Finset.mem_insert, this]

private lemma litBlock_suffix (p : ℕ) (O I : Finset ℕ) (i k : ℕ)
    (hi1 : 1 ≤ i) :
    litBlock p (insert i O) I (i - 1 + 1 + k) = litBlock p O I (i - 1 + 1 + k) := by
  have : i - 1 + 1 + k + 1 ≠ i := by omega
  simp [litBlock, Finset.mem_insert, this]

private lemma litBlock_prefix_erase (p : ℕ) (O I : Finset ℕ) (i j : ℕ)
    (hj : j < i - 1) (hi1 : 1 ≤ i) :
    litBlock p (O.erase i) (insert i I) j = litBlock p O I j := by
  have hne : j + 1 ≠ i := by omega
  have hneO : j + 1 ∈ O.erase i ↔ j + 1 ∈ O := by
    simp [Finset.mem_erase, hne]
  have hneI : j + 1 ∈ insert i I ↔ j + 1 ∈ I := by
    simp [Finset.mem_insert, hne]
  simp [litBlock, hneO, hneI]

private lemma litBlock_suffix_erase (p : ℕ) (O I : Finset ℕ) (i k : ℕ)
    (hi1 : 1 ≤ i) :
    litBlock p (O.erase i) (insert i I) (i - 1 + 1 + k) =
      litBlock p O I (i - 1 + 1 + k) := by
  have hne : i - 1 + 1 + k + 1 ≠ i := by omega
  have hneO : i - 1 + 1 + k + 1 ∈ O.erase i ↔ i - 1 + 1 + k + 1 ∈ O := by
    simp [Finset.mem_erase, hne]
  have hneI : i - 1 + 1 + k + 1 ∈ insert i I ↔ i - 1 + 1 + k + 1 ∈ I := by
    simp [Finset.mem_insert, hne]
  simp [litBlock, hneO, hneI]

private lemma flatMap_congr_range {α : Type*} (n : ℕ) (f g : ℕ → List α)
    (h : ∀ j < n, f j = g j) :
    (List.range n).flatMap f = (List.range n).flatMap g := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.range_succ, List.flatMap_append, List.flatMap_append, List.flatMap_singleton,
      List.flatMap_singleton, ih (fun j hj => h j (Nat.lt_succ_of_lt hj)), h n (Nat.lt_succ_self _)]

/-- `Λ^O_I = A ++ L_i ++ B` and `Λ^{O∪{i}}_I = A ++ L_i^o ++ B` when `i ∉ O ∪ I`. -/
lemma literals_split_closed (p m : ℕ) (O I : Finset ℕ) (i : ℕ)
    (hi : i ∈ Finset.Icc 1 m) (hO : i ∉ O) (hI : i ∉ I) :
    ∃ A B : List ℕ,
      literals p m O I = A ++ lockSeq (p + 12 * (i - 1)) ++ B ∧
      literals p m (insert i O) I = A ++ lockOpen (p + 12 * (i - 1)) ++ B := by
  obtain ⟨hi1, him⟩ := Finset.mem_Icc.mp hi
  let A := (List.range (i - 1)).flatMap (litBlock p O I)
  let B := (List.range (m - i)).flatMap (fun k => litBlock p O I (i - 1 + 1 + k))
  refine ⟨A, B, ?_, ?_⟩
  · rw [literals_eq_flatMap, show m = (i - 1) + 1 + (m - i) by omega, range_split]
    simp only [List.flatMap_append, List.flatMap_cons, List.flatMap_map]
    have hblk : litBlock p O I (i - 1) = lockSeq (p + 12 * (i - 1)) := by
      have : i - 1 + 1 = i := by omega
      simp [litBlock, this, hO, hI]
    simp [A, B, hblk, List.append_assoc]
  · rw [literals_eq_flatMap (O := insert i O), show m = (i - 1) + 1 + (m - i) by omega,
      range_split]
    simp only [List.flatMap_append, List.flatMap_cons, List.flatMap_map]
    have hA : (List.range (i - 1)).flatMap (litBlock p (insert i O) I) = A := by
      refine flatMap_congr_range _ _ _ fun j hj => ?_
      exact litBlock_prefix p O I i j hj hi1
    have hB : (List.range (m - i)).flatMap (fun k => litBlock p (insert i O) I (i - 1 + 1 + k)) =
        B := by
      refine flatMap_congr_range _ _ _ fun k hk => ?_
      exact litBlock_suffix p O I i k hi1
    have hblk : litBlock p (insert i O) I (i - 1) = lockOpen (p + 12 * (i - 1)) := by
      have : i - 1 + 1 = i := by omega
      simp [litBlock, this, Finset.mem_insert_self]
    simp [A, B, hA, hB, hblk, List.append_assoc]

/-- `Λ^O_I = A ++ L_i^o ++ B` and `Λ^{O-{i}}_{I∪{i}} = A ++ 𝓘 ++ B` when `i ∈ O`. -/
lemma literals_split_open (p m : ℕ) (O I : Finset ℕ) (i : ℕ)
    (hi : i ∈ O) (hO : O ⊆ Finset.Icc 1 m) (hOI : Disjoint O I) :
    ∃ A B : List ℕ,
      literals p m O I = A ++ lockOpen (p + 12 * (i - 1)) ++ B ∧
      literals p m (O.erase i) (insert i I) =
        A ++ interval (p + 12 * (i - 1) + 1) (p + 12 * (i - 1) + 12) ++ B := by
  have him : i ∈ Finset.Icc 1 m := hO hi
  obtain ⟨hi1, him'⟩ := Finset.mem_Icc.mp him
  have hI : i ∉ I := Finset.disjoint_left.mp hOI hi
  let A := (List.range (i - 1)).flatMap (litBlock p O I)
  let B := (List.range (m - i)).flatMap (fun k => litBlock p O I (i - 1 + 1 + k))
  refine ⟨A, B, ?_, ?_⟩
  · rw [literals_eq_flatMap, show m = (i - 1) + 1 + (m - i) by omega, range_split]
    simp only [List.flatMap_append, List.flatMap_cons, List.flatMap_map]
    have hblk : litBlock p O I (i - 1) = lockOpen (p + 12 * (i - 1)) := by
      have : i - 1 + 1 = i := by omega
      simp [litBlock, this, hi]
    simp [A, B, hblk, List.append_assoc]
  · rw [literals_eq_flatMap (O := O.erase i) (I := insert i I),
      show m = (i - 1) + 1 + (m - i) by omega, range_split]
    simp only [List.flatMap_append, List.flatMap_cons, List.flatMap_map]
    have hA : (List.range (i - 1)).flatMap (litBlock p (O.erase i) (insert i I)) = A := by
      refine flatMap_congr_range _ _ _ fun j hj => ?_
      exact litBlock_prefix_erase p O I i j hj hi1
    have hB :
        (List.range (m - i)).flatMap
          (fun k => litBlock p (O.erase i) (insert i I) (i - 1 + 1 + k)) = B := by
      refine flatMap_congr_range _ _ _ fun k hk => ?_
      exact litBlock_suffix_erase p O I i k hi1
    have hblk : litBlock p (O.erase i) (insert i I) (i - 1) =
        interval (p + 12 * (i - 1) + 1) (p + 12 * (i - 1) + 12) := by
      have : i - 1 + 1 = i := by omega
      simp [litBlock, this, Finset.mem_erase]
    simp [A, B, hA, hB, hblk, List.append_assoc]

/-- Closed-lock split used for deadlocks: `i ∉ O ∪ I`. -/
lemma literals_split_closed_only (p m : ℕ) (O I : Finset ℕ) (i : ℕ)
    (hi : i ∈ Finset.Icc 1 m) (hO : i ∉ O) (hI : i ∉ I) :
    ∃ A B : List ℕ, literals p m O I = A ++ lockSeq (p + 12 * (i - 1)) ++ B := by
  obtain ⟨A, B, h, _⟩ := literals_split_closed p m O I i hi hO hI
  exact ⟨A, B, h⟩

theorem property_8_proof (p m : ℕ) (O I : Finset ℕ) (X : List ℕ)
    (hO : O ⊆ Finset.Icc 1 m) (hI : I ⊆ Finset.Icc 1 m) (hOI : Disjoint O I) :
    (∀ i ∈ Finset.Icc 1 m, i ∉ O → i ∉ I →
      IsStack (litKey p i :: X ++ literals p m O I) →
      LeadsTo (litKey p i :: X ++ literals p m O I) {X ++ literals p m (insert i O) I}) ∧
    (∀ i ∈ O,
      IsStack (litTest p i :: X ++ literals p m O I) →
      LeadsTo (litTest p i :: X ++ literals p m O I)
        {X ++ literals p m (O.erase i) (insert i I)}) ∧
    (∀ i ∈ Finset.Icc 1 m, i ∉ O →
      IsStack (litTest p i :: X ++ literals p m O I) →
      IsDeadlock (litTest p i :: X ++ literals p m O I)) := by
  refine ⟨?a, ?b, ?c⟩
  · -- (a) key opens closed lock i
    intro i hi hO' hI' hStack
    obtain ⟨A, B, hΛ, hΛ'⟩ := literals_split_closed p m O I i hi hO' hI'
    have hp : litKey p i = lockKey (p + 12 * (i - 1)) := rfl
    have hS : IsStack (lockKey (p + 12 * (i - 1)) :: (X ++ A) ++ lockSeq (p + 12 * (i - 1)) ++ B) := by
      convert hStack using 1
      simp [hp, hΛ, List.append_assoc]
    have h := (property_5 (p + 12 * (i - 1)) (X ++ A) B).1 hS
    convert h using 1
    · simp [hp, hΛ, List.append_assoc]
    · simp [hΛ', List.append_assoc]
  · -- (b) test on open lock i
    intro i hi hStack
    obtain ⟨A, B, hΛ, hΛ'⟩ := literals_split_open p m O I i hi hO hOI
    have hp : litTest p i = lockTest (p + 12 * (i - 1)) := rfl
    have hS : IsStack (lockTest (p + 12 * (i - 1)) :: (X ++ A) ++ lockOpen (p + 12 * (i - 1)) ++ B) := by
      convert hStack using 1
      simp [hp, hΛ, List.append_assoc]
    have h := (property_5 (p + 12 * (i - 1)) (X ++ A) B).2.1 hS
    convert h using 1
    · simp [hp, hΛ, List.append_assoc]
    · simp [hΛ', List.append_assoc]
  · -- (c) test when i ∉ O
    intro i hi hO' hStack
    by_cases hI' : i ∈ I
    · -- duplicate: litTest appears in head and in the I-block
      obtain ⟨hi1, him⟩ := Finset.mem_Icc.mp hi
      have hdup : litTest p i ∈ literals p m O I := by
        rw [literals_eq_flatMap]
        have hi0 : i - 1 < m := by omega
        refine List.mem_flatMap.mpr ⟨i - 1, List.mem_range.mpr hi0, ?_⟩
        have : i - 1 + 1 = i := by omega
        have hblk : litBlock p O I (i - 1) =
            interval (p + 12 * (i - 1) + 1) (p + 12 * (i - 1) + 12) := by
          simp [litBlock, this, hO', hI']
        rw [hblk, litTest, lockTest, interval]
        refine (List.mem_range').2 ⟨6, by omega, ?_⟩
        ring_nf
      have hnd : ¬ (litTest p i :: X ++ literals p m O I).Nodup :=
        List.not_nodup_cons_of_mem (List.mem_append.mpr (Or.inr hdup))
      have : ¬ IsStack (litTest p i :: X ++ literals p m O I) := by
        intro hs
        have hperm : (litTest p i :: X ++ literals p m O I).Perm
            (identity (litTest p i :: X ++ literals p m O I).length) := hs
        have hid : (identity (litTest p i :: X ++ literals p m O I).length).Nodup := by
          simp [identity, interval]; exact List.nodup_range' 1
        exact hnd ((hperm.nodup_iff).2 hid)
      exact (this hStack).elim
    · -- i ∉ O ∪ I: closed lock deadlock via property_5.c
      obtain ⟨A, B, hΛ⟩ := literals_split_closed_only p m O I i hi hO' hI'
      have hp : litTest p i = lockTest (p + 12 * (i - 1)) := rfl
      have hS : IsStack (lockTest (p + 12 * (i - 1)) :: (X ++ A) ++ lockSeq (p + 12 * (i - 1)) ++ B) := by
        convert hStack using 1
        simp [hp, hΛ, List.append_assoc]
      have hD := (property_5 (p + 12 * (i - 1)) (X ++ A) B).2.2 hS
      convert hD using 1
      simp [hp, hΛ, List.append_assoc]

end PancakeHard

theorem solution (p m : ℕ) (O I : Finset ℕ) (X : List ℕ) (hO : O ⊆ Finset.Icc 1 m)
    (hI : I ⊆ Finset.Icc 1 m) (hOI : Disjoint O I) :
    (∀ i ∈ Finset.Icc 1 m, i ∉ O → i ∉ I →
      PancakeHard.IsStack (PancakeHard.litKey p i :: X ++ PancakeHard.literals p m O I) →
      PancakeHard.LeadsTo (PancakeHard.litKey p i :: X ++ PancakeHard.literals p m O I)
        {X ++ PancakeHard.literals p m (insert i O) I}) ∧
    (∀ i ∈ O,
      PancakeHard.IsStack (PancakeHard.litTest p i :: X ++ PancakeHard.literals p m O I) →
      PancakeHard.LeadsTo (PancakeHard.litTest p i :: X ++ PancakeHard.literals p m O I)
        {X ++ PancakeHard.literals p m (O.erase i) (insert i I)}) ∧
    (∀ i ∈ Finset.Icc 1 m, i ∉ O →
      PancakeHard.IsStack (PancakeHard.litTest p i :: X ++ PancakeHard.literals p m O I) →
      PancakeHard.IsDeadlock (PancakeHard.litTest p i :: X ++ PancakeHard.literals p m O I)) :=
  PancakeHard.property_8_proof p m O I X hO hI hOI
