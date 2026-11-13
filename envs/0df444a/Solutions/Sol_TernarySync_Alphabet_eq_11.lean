-- Prove2me | solution 1 for TernarySync.Alphabet.eq_11
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T07:20:51.754196+00:00
-- url     : https://prove2.me/submissions/40205698-4c7e-4fca-8155-002d15b34190

import Mathlib
import Definitions.Def_TernarySync_Alphabet_RandomSource

section
set_option autoImplicit false

namespace TernarySync.Dev.Eq11
open TernarySync.Alphabet

/-- words of length `k` having `z` as a subsequence -/
def supSet {β : Type*} (z : List β) (k : ℕ) : Set (List β) :=
  {x | x.length = k ∧ z.Sublist x}

theorem supSet_bound {β : Type*} [Fintype β] : ∀ (k n m : ℕ) (z : List β), n + m = k →
    z.length = n →
    (supSet z k).Finite ∧
      ((supSet z k).ncard : ℝ) ≤ (Nat.choose k m : ℝ) * (Fintype.card β : ℝ) ^ m := by
  intro k
  induction k with
  | zero =>
    intro n m z h1 h2
    have hn : n = 0 := by omega
    have hm : m = 0 := by omega
    subst hn hm
    have hsub : supSet z 0 ⊆ {([] : List β)} := by
      intro x hx
      have := hx.1
      simp [List.length_eq_zero_iff.mp this]
    refine ⟨(Set.finite_singleton _).subset hsub, ?_⟩
    have := Set.ncard_le_ncard hsub (Set.finite_singleton _)
    simp at this
    simpa using this
  | succ k ih =>
    intro n m z h1 h2
    cases m with
    | zero =>
      have hsub : supSet z (k + 1) ⊆ {z} := by
        intro x hx
        have := hx.2.eq_of_length (by rw [h2, hx.1]; omega)
        simp [this]
      refine ⟨(Set.finite_singleton _).subset hsub, ?_⟩
      have := Set.ncard_le_ncard hsub (Set.finite_singleton _)
      simp at this
      simpa using this
    | succ m' =>
      have hA := ih n m' z (by omega) h2
      have hAfin : (Set.image (fun p : β × List β => p.1 :: p.2)
          (Set.univ ×ˢ supSet z k)).Finite :=
        (Set.finite_univ.prod hA.1).image _
      have hAcard : ((Set.image (fun p : β × List β => p.1 :: p.2)
          (Set.univ ×ˢ supSet z k)).ncard : ℝ) ≤
          (Fintype.card β : ℝ) * ((Nat.choose k m' : ℝ) * (Fintype.card β : ℝ) ^ m') := by
        have h1 := Set.ncard_image_le (f := fun p : β × List β => p.1 :: p.2)
          (Set.finite_univ.prod hA.1)
        rw [Set.ncard_prod, Set.ncard_univ, Nat.card_eq_fintype_card] at h1
        have h1' : ((Set.image (fun p : β × List β => p.1 :: p.2)
          (Set.univ ×ˢ supSet z k)).ncard : ℝ) ≤ (Fintype.card β : ℝ) * (supSet z k).ncard := by
          exact_mod_cast h1
        calc _ ≤ _ := h1'
          _ ≤ _ := by gcongr; exact hA.2
      cases z with
      | nil =>
        have hsub : supSet ([] : List β) (k + 1) ⊆ Set.image (fun p : β × List β => p.1 :: p.2)
            (Set.univ ×ˢ supSet [] k) := by
          rintro x ⟨hx1, -⟩
          cases x with
          | nil => simp at hx1
          | cons a x' =>
            refine ⟨(a, x'), ⟨trivial, ?_, List.nil_sublist _⟩, rfl⟩
            simpa using hx1
        refine ⟨hAfin.subset hsub, ?_⟩
        have := Set.ncard_le_ncard hsub hAfin
        have h3 : ((supSet ([] : List β) (k + 1)).ncard : ℝ) ≤ _ :=
          le_trans (by exact_mod_cast this) hAcard
        refine le_trans h3 ?_
        have hpas : (Nat.choose k m' : ℝ) ≤ (Nat.choose (k + 1) (m' + 1) : ℝ) := by
          rw [Nat.choose_succ_succ]; push_cast; linarith [(Nat.cast_nonneg (Nat.choose k (m'+1)) : (0:ℝ) ≤ _)]
        calc _ = (Nat.choose k m' : ℝ) * (Fintype.card β : ℝ) ^ (m' + 1) := by ring
          _ ≤ _ := by gcongr
      | cons b z' =>
        have hB := ih (n - 1) (m' + 1) z' (by simp at h2; omega) (by simp at h2; omega)
        have hBfin : (Set.image (List.cons b) (supSet z' k)).Finite := hB.1.image _
        have hBcard : ((Set.image (List.cons b) (supSet z' k)).ncard : ℝ) ≤
            (Nat.choose k (m' + 1) : ℝ) * (Fintype.card β : ℝ) ^ (m' + 1) := by
          have h1 := Set.ncard_image_le (f := List.cons b) hB.1
          calc _ ≤ ((supSet z' k).ncard : ℝ) := by exact_mod_cast h1
            _ ≤ _ := hB.2
        have hsub : supSet (b :: z') (k + 1) ⊆
            Set.image (fun p : β × List β => p.1 :: p.2) (Set.univ ×ˢ supSet (b :: z') k) ∪
              Set.image (List.cons b) (supSet z' k) := by
          rintro x ⟨hx1, hx2⟩
          cases x with
          | nil => simp at hx1
          | cons a x' =>
            rw [List.sublist_cons_iff] at hx2
            rcases hx2 with h | ⟨r, hr, h⟩
            · left
              exact ⟨(a, x'), ⟨trivial, by simpa using hx1, h⟩, rfl⟩
            · right
              obtain ⟨rfl, rfl⟩ : b = a ∧ z' = r := by simpa using hr
              exact ⟨x', ⟨by simpa using hx1, h⟩, rfl⟩
        refine ⟨(hAfin.union hBfin).subset hsub, ?_⟩
        have h4 := Set.ncard_le_ncard hsub (hAfin.union hBfin)
        have h5 := Set.ncard_union_le (Set.image (fun p : β × List β => p.1 :: p.2)
          (Set.univ ×ˢ supSet (b :: z') k)) (Set.image (List.cons b) (supSet z' k))
        have h6 : ((supSet (b :: z') (k + 1)).ncard : ℝ) ≤
            ((Set.image (fun p : β × List β => p.1 :: p.2)
              (Set.univ ×ˢ supSet (b :: z') k)).ncard : ℝ) +
              ((Set.image (List.cons b) (supSet z' k)).ncard : ℝ) := by
          exact_mod_cast h4.trans h5
        refine h6.trans ?_
        refine (add_le_add hAcard hBcard).trans (le_of_eq ?_)
        rw [Nat.choose_succ_succ]; push_cast; ring

theorem ncard_biUnion_le {ι α : Type*} (s : Finset ι) (f : ι → Set α) (c : ι → ℝ)
    (hf : ∀ i ∈ s, (f i).Finite ∧ ((f i).ncard : ℝ) ≤ c i) :
    (⋃ i ∈ s, f i).Finite ∧ (((⋃ i ∈ s, f i).ncard : ℕ) : ℝ) ≤ ∑ i ∈ s, c i := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    have h1 := hf a (Finset.mem_insert_self _ _)
    have h2 := ih (fun i hi => hf i (Finset.mem_insert_of_mem hi))
    rw [Finset.set_biUnion_insert, Finset.sum_insert ha]
    refine ⟨h1.1.union h2.1, ?_⟩
    have := Set.ncard_union_le (f a) (⋃ i ∈ s, f i)
    have h3 : (((f a ∪ ⋃ i ∈ s, f i).ncard : ℕ) : ℝ) ≤
        ((f a).ncard : ℝ) + ((⋃ i ∈ s, f i).ncard : ℝ) := by exact_mod_cast this
    linarith [h1.2, h2.2]

end TernarySync.Dev.Eq11

namespace TernarySync.Alphabet
open TernarySync.Dev.Eq11 in
theorem chk_eq_11 {β : Type*} [Fintype β] (ℓ : ℕ) (hℓ : 1000 < ℓ) (y : List β) (hy : y.length = ℓ) :
    ((delBall ((1 : ℝ) / 1000) ℓ y).ncard : ℝ) ≤
      ∑ d ∈ (Finset.range (ℓ + 1)).filter (fun d : ℕ => (d : ℝ) < (1 : ℝ) / 1000 * (ℓ : ℝ)),
        ((ℓ.choose d : ℝ) ^ 2 * (Fintype.card β : ℝ) ^ d) := by
  classical
  set D := (Finset.range (ℓ + 1)).filter (fun d : ℕ => (d : ℝ) < (1 : ℝ) / 1000 * (ℓ : ℝ)) with hD
  let U : ℕ → Set (List β) := fun d => ⋃ z ∈ (List.sublistsLen (ℓ - d) y).toFinset, supSet z ℓ
  have hU : ∀ d ∈ D, (U d).Finite ∧ ((U d).ncard : ℝ) ≤
      (ℓ.choose d : ℝ) ^ 2 * (Fintype.card β : ℝ) ^ d := by
    intro d hd
    have hdl : d ≤ ℓ := by
      have := (Finset.mem_filter.mp hd).1
      simp at this; omega
    have h := ncard_biUnion_le (List.sublistsLen (ℓ - d) y).toFinset (fun z => supSet z ℓ)
      (fun _ => (ℓ.choose d : ℝ) * (Fintype.card β : ℝ) ^ d) (by
        intro z hz
        have hz' := (List.mem_sublistsLen.mp (List.mem_toFinset.mp hz))
        have := supSet_bound ℓ (ℓ - d) d z (by omega) hz'.2
        rw [show ℓ = ℓ from rfl] at this
        exact this)
    refine ⟨h.1, h.2.trans ?_⟩
    rw [Finset.sum_const, nsmul_eq_mul]
    have hc : ((List.sublistsLen (ℓ - d) y).toFinset.card : ℝ) ≤ (ℓ.choose d : ℝ) := by
      have h1 := List.toFinset_card_le (List.sublistsLen (ℓ - d) y)
      rw [List.length_sublistsLen, hy, Nat.choose_symm hdl] at h1
      exact_mod_cast h1
    calc _ ≤ (ℓ.choose d : ℝ) * ((ℓ.choose d : ℝ) * (Fintype.card β : ℝ) ^ d) := by
          gcongr
      _ = _ := by ring
  have hb := ncard_biUnion_le D U _ hU
  have hsub : delBall ((1 : ℝ) / 1000) ℓ y ⊆ ⋃ d ∈ D, U d := by
    rintro x ⟨hx1, hx2⟩
    have hne : {k : ℕ | ∃ z : List β, z.Sublist x ∧ z.Sublist y ∧ z.length = k}.Nonempty :=
      ⟨0, [], List.nil_sublist _, List.nil_sublist _, rfl⟩
    have hbd : BddAbove {k : ℕ | ∃ z : List β, z.Sublist x ∧ z.Sublist y ∧ z.length = k} := by
      refine ⟨x.length, ?_⟩
      rintro k ⟨z, hz1, -, rfl⟩
      exact hz1.length_le
    obtain ⟨z, hz1, hz2, hz3⟩ := Nat.sSup_mem hne hbd
    have hK : lcs x y = z.length := hz3.symm
    have hzl : z.length ≤ ℓ := hx1 ▸ hz1.length_le
    simp only [U, Set.mem_iUnion]
    refine ⟨ℓ - z.length, ?_, z, ?_, hx1, hz1⟩
    · rw [hD, Finset.mem_filter, Finset.mem_range]
      refine ⟨by omega, ?_⟩
      rw [hK] at hx2
      rw [Nat.cast_sub hzl]
      linarith
    · rw [List.mem_toFinset, List.mem_sublistsLen]
      refine ⟨hz2, ?_⟩
      omega
  have h1 := Set.ncard_le_ncard hsub hb.1
  exact (by exact_mod_cast h1 : ((delBall ((1 : ℝ) / 1000) ℓ y).ncard : ℝ) ≤ _).trans hb.2
end TernarySync.Alphabet
end

theorem solution : type_of% @TernarySync.Alphabet.chk_eq_11 := @TernarySync.Alphabet.chk_eq_11
