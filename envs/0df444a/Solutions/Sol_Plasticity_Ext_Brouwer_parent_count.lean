-- Prove2me | solution 1 for Plasticity.Ext.Brouwer.parent_count
-- status  : ACCEPTED   (prove)
-- author  : @scanstone
-- created : 2026-10-14T09:31:56.159387+00:00
-- url     : https://prove2.me/submissions/f4b5b56f-590d-4498-bdd2-aa50067867a1

import Definitions.Def_Plasticity_CubicalSperner
import Theorems.Thm_Plasticity_Ext_Brouwer_facets
import Theorems.Thm_Plasticity_Ext_Brouwer_interior
import Mathlib.Data.Fintype.Card
import Mathlib.Order.Fin.Basic
import Mathlib.Tactic.ByContra
import Mathlib.Tactic.Contrapose
import Mathlib.Tactic.Use
import Mathlib.Tactic.Convert
import Mathlib.Tactic.NthRewrite
import Mathlib.Tactic.Cases
import Mathlib.Tactic.CongrExclamation
import Mathlib.Tactic.Push
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Algebra.Order.Group.Nat

/-!
# Parent counts of codimension-one grid simplices

Ported from harfe, *fixed-point-theorems-lean4*,
https://github.com/harfe/fixed-point-theorems-lean4
(file `FixedPointTheorems/cubical_sperner_prep.lean`), MIT licence; the copyright and permission notice is reproduced below.
Adapted to Lean v4.33.1 / Mathlib 0df444a (tactic blocks restyled, a few proof steps repaired).

Copyright (c) 2026 harfe

Permission is hereby granted, free of charge, to any person obtaining a copy of this software
and associated documentation files (the "Software"), to deal in the Software without
restriction, including without limitation the rights to use, copy, modify, merge, publish,
distribute, sublicense, and/or sell copies of the Software, and to permit persons to whom the
Software is furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in all copies or
substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR IMPLIED, INCLUDING
BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND
NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM,
DAMAGES OR OTHER LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.
-/

open Plasticity Plasticity.CubicalSperner

namespace Sol_Plasticity_Ext_Brouwer_parent_count

open Classical

variable (SC : SpernerCube)
variable {n1 : ℕ}
variable {hn1 : n1 + 1 = SC.n}

/-- Some coordinate is constantly `0` along `I`. -/
def case_A (I : Fin (n1 +1) → SC.G) := ∃ j, ∀ k, I k j = 0

/-- Some coordinate is constantly `p` along `I`. -/
def case_B (I : Fin (n1 +1) → SC.G) := ∃ j, ∀ k, I k j = Fin.last SC.p

/-- Some coordinate is constant along `I`, with a value strictly between `0` and `p`. -/
def case_C (I : Fin (n1 +1) → SC.G) :=
    ∃ j, ∃ (q : Fin (SC.p + 1)), (q ≠ 0 ∧ q ≠ Fin.last SC.p ) ∧ ∀ k, I k j = q

/-- No coordinate is constant along `I`. -/
def case_D (I : Fin (n1 +1) → SC.G) := ∀ j, ∀ q, ∃ k,I k j ≠ q

/-- Facets of a full simplex are its vertex deletions (child card `Plasticity.Ext.Brouwer.facets`). -/
lemma child_simplex_char (I : Fin (n1 +1) → SC.G) J {hs : simplex SC SC.n J}
    : is_face SC I J ↔ ∃ i, I = @delete_vertex SC n1 hn1 i J :=
  Plasticity.Ext.Brouwer.facets SC hn1 I J hs

/-- Interior simplices have two parents (child card `Plasticity.Ext.Brouwer.interior`). -/
lemma case_D_parent_count {hn1 : n1 + 1 = SC.n} I (hs : simplex SC n1 I) (h1 : case_D SC I)
    : Finset.card { J : Fin (SC.n + 1) → SC.G | is_face SC I J} = 2 := by
  have h := Plasticity.Ext.Brouwer.interior SC hn1 I hs h1
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype] at h
  convert h

lemma one_of_ABCD (I : Fin (n1 +1) → SC.G) :
    case_A SC I ∨ case_B SC I ∨ case_C SC I ∨ case_D SC I := by
  by_cases h1 : case_D SC I
  exact Or.inr (Or.inr (Or.inr h1))
  unfold case_D at h1
  push Not at h1
  obtain ⟨j , ⟨ q, h2 ⟩⟩ := h1
  by_cases q0 : q = 0
  · apply Or.inl
    use j
    rwa [← q0]
  by_cases qp : q = Fin.last SC.p
  · apply Or.inr (Or.inl _)
    use j
    intro k
    rwa [h2 k]
  suffices h3 : case_C SC I by
    simp only [h3, true_or, or_true]
  use j, q

section simplex_properties

lemma monotone_1_of_simplex {m:ℕ } (I : Fin (m+1)→ SC.G) (hs : simplex SC m I) (i1 i2 : Fin (m+1))
    (h1 : i1 ≤ i2) : ∀ j, I i1 j ≤ I i2 j := by
  intro j
  let f := fun i ↦ I i j
  have h2 := @Fin.monotone_iff_le_succ m _ _ f
  suffices h3 : Monotone f by exact (h3 h1)
  rw [h2]
  clear i1 i2 h1
  intro i1
  have h3 := (hs.2 i1.1 i1.2 j).1
  simp only [Fin.val_fin_le] at h3
  convert h3 <;> ext <;> simp [Fin.ofNat_eq_cast, Nat.mod_eq_of_lt]

lemma last_of_simplex {m: ℕ} I (hs : simplex SC m I) j :
    (I (Fin.last m) j).1 ≤ (I 0 j).1 + 1 := by
  cases m
  simp only [Fin.last_zero, Fin.isValue, le_add_iff_nonneg_right, zero_le]
  rename_i m
  have h3 : 0 < m + 1 := by omega
  exact (hs.2 0 h3 j).2

lemma le_add_one_of_simplex {m: ℕ} I (hs : simplex SC m I) (i1 i2 : Fin (m+1)) j :
    (I i1 j).1 ≤ (I i2 j).1 + 1 := by
  have h1 := last_of_simplex SC I hs j
  apply le_trans _ (le_trans h1 _)
  apply monotone_1_of_simplex SC I hs _ _ (Fin.le_last i1)
  apply Nat.add_le_add_right
  apply monotone_1_of_simplex SC I hs _ _ (Fin.zero_le i2)

end simplex_properties

lemma p_ne_zero_of_cube {hn1 : n1 + 1 = SC.n}: Fin.last SC.p ≠ 0 := by
  simp only [ne_eq, Fin.last_eq_zero_iff]
  intro h1
  let v : Fin SC.n → Fin (SC.p + 1) := fun _ ↦ 0
  have h3 : NeZero SC.n := by
    rw [←hn1]
    exact instNeZeroNatHAdd_1
  have h4 : v 0 = 0 := by {rfl}
  have h2 := (SC.rl_proper v).2 0
  simp only [Fin.val_zero, ne_eq, h1, Fin.val_eq_zero_iff, nonpos_iff_eq_zero] at h2
  exact h2.1 h4 (h2.2 h4)

lemma insert_index_ne j a : @insert_index SC n1 hn1 j a ≠ j := by
  apply Fin.ne_of_val_ne
  unfold insert_index
  by_cases hlt : a.val < j.val
  · simp only [hlt, ↓reduceIte]
    omega
  · simp only [hlt, ↓reduceIte, ne_eq]
    omega

lemma almost_surjective_of_insert_index (j : Fin (SC.n+1)) (a : Fin (SC.n+1)) (h : a ≠ j)
    : ∃ k : Fin (n1 + 1) , a = @insert_index SC n1 hn1 j k := by
  unfold insert_index
  by_cases hlt : a.1 < j.1
  · use (Fin.ofNat _ a.1)
    have h2 : a.1 = (Fin.ofNat (n1 + 1) a.1) := by
      rw [Fin.ofNat_eq_cast, Fin.val_cast_of_lt]
      rw [hn1]
      apply lt_of_lt_of_le hlt
      exact Fin.is_le j
    simp only [← h2, hlt]
    rfl
  · have h2 : j.1 < a.1 := by
      have := Fin.val_ne_of_ne (id (Ne.symm h))
      omega
    let a1 := a.1 - 1
    have h3 : a1 + 1 = a.1 := by
      show a.1 - 1 + 1 = a.1
      omega
    let a1f := Fin.ofNat (n1 + 1) a1
    use a1f
    ext
    have h4 : a1 < n1 +1 := by
      have h5 := a.2
      show a.1 - 1 < n1 + 1
      omega
    have h6 : a1f.1 = a1 := by
      unfold a1f
      simp only [Fin.ofNat_eq_cast, Fin.val_natCast, Nat.mod_succ_eq_iff_lt, Nat.succ_eq_add_one]
      exact h4
    have h5 : ¬ (a1f < j.1) := by
      simp only [not_lt, h6]
      show j.1 ≤ a.1 - 1
      omega
    simp only [h5, ↓reduceIte]
    rw [← h3, h6]

lemma insert_index_strict_mono j : StrictMono (@insert_index SC n1 hn1 j) := by
  intro a b h1
  have h2 : a.1 < b.1 := by {exact h1}
  have h21 : a.1 < b.1 + 1 := by omega
  unfold insert_index
  by_cases h3 : a.1 < j.1
  · by_cases h4 : b.1 < j.1
    repeat {
      simp only [h3, ↓reduceIte, h4, Fin.mk_lt_mk, Fin.val_fin_lt, gt_iff_lt]
      assumption
    }
  · by_cases h4 : b.1 < j.1
    · simp only [h3, ↓reduceIte, h4, Fin.mk_lt_mk, gt_iff_lt]
      omega
    · simp only [h3, ↓reduceIte, h4, Fin.mk_lt_mk, gt_iff_lt]
      omega

lemma insert_index_inj j : Function.Injective (@insert_index SC n1 hn1 j) := by
  apply StrictMono.injective
  apply insert_index_strict_mono

lemma delete_vertex_inj J {hs : simplex SC SC.n J} i1 i2
    (h1 : @delete_vertex SC n1 hn1 i1 J = @delete_vertex SC n1 hn1 i2 J ) : i1 = i2 := by
  by_contra h2
  obtain ⟨k, h3 ⟩ := @almost_surjective_of_insert_index SC n1 hn1 i2 i1 h2
  apply @insert_index_ne SC n1 hn1 i1 k
  apply hs.1
  nth_rewrite 2 [h3]
  exact (congrFun h1) k

lemma is_id_of_strict_mono (m: ℕ ) (f : Fin m → Fin m) (hsm : StrictMono f)
    : ∀ k, f k = k := by
  suffices h1 : ∀ (a : ℕ), ∀ k, k.1 < a → f k = k by
    intro k
    exact h1 m k k.2
  intro a
  induction' a with a ha
  · intro k h1
    omega
  · have h1 : Function.Injective f := by {exact StrictMono.injective hsm}
    have h2 : Function.Surjective f := Finite.surjective_of_injective h1
    intro k hk
    have h3 j : j < k → f j = j := by
      intro hj
      apply ha
      omega
    by_cases h4 : f k < k
    apply h1 (h3 (f k) h4)
    simp only [not_lt] at h4
    apply le_antisymm _ h4
    obtain ⟨l, h9⟩ := h2 k
    suffices h8 : k ≤ l by {rwa [← hsm.le_iff_le, h9] at h8}
    by_contra! h6
    have h7 := h3 l h6
    rw [h9] at h7
    rw [h7] at h6
    exact (lt_self_iff_false l).mp h6

lemma is_insert_index_of_strict_mono f (hsm : StrictMono f)
    : ∃ j, f = @insert_index SC n1 hn1 j := by
  have h31 : Function.Injective f := by {exact hsm.injective}
  have hns : ∃ j, ∀ i, f i ≠ j := by
    by_contra! h1
    have h2 : Function.Surjective f := by {exact h1 }
    have h5 : Function.Bijective f :=  And.intro h31 h2
    have h4 := Nat.card_eq_of_bijective f h5
    simp only [Nat.card_eq_fintype_card, Fintype.card_fin, Nat.add_right_cancel_iff] at h4
    rw [h4] at hn1
    simp only [Nat.add_eq_left, one_ne_zero] at hn1
  obtain ⟨ j, hj⟩ := hns
  use j
  have h1 : ∀ k1, ∃ k2, f k1 = @insert_index SC n1 hn1 j k2 := by
    intro k1
    apply almost_surjective_of_insert_index
    exact hj k1
  obtain ⟨g, hg⟩ := Classical.skolem.mp h1
  have h2 : StrictMono g := by
    intro k1 k2
    contrapose!
    intro h4
    rw [←hsm.le_iff_le, hg k1, hg k2]
    have h5 := @insert_index_strict_mono SC n1 hn1 j
    rw [h5.le_iff_le]
    exact h4
  have h3 := is_id_of_strict_mono _ g h2
  ext1 k
  rw [hg k, h3 k]

lemma insert_vertex I (v : SC.G) j :
    ∃ J, I = @delete_vertex SC n1 hn1 j J ∧ J j = v := by
  have h1 : ∀ j2, ∃ w, (j2 = j → w = v)
      ∧ ∀ i, @insert_index SC n1 hn1 j i = j2 → I i = w := by
    intro j2
    by_cases h1 : j2 = j
    · use v
      simp only [implies_true, true_and]
      intro i
      have h3 : @insert_index SC n1 hn1 j i ≠ j := by {apply insert_index_ne}
      simp only [h1, h3, IsEmpty.forall_iff]
    · have h3 : ∃ i, j2 = @insert_index SC n1 hn1 j i := by
        apply almost_surjective_of_insert_index
        exact h1
      obtain ⟨ i, hi⟩ := h3
      use (I i)
      simp only [h1, IsEmpty.forall_iff, true_and]
      intro i2 h2
      congr!
      apply insert_index_inj SC j
      rw [h2, hi]
  obtain ⟨J, h2⟩ := Classical.skolem.mp h1
  use J
  apply And.intro
  · ext i
    exact (h2 (@insert_index SC n1 hn1 j i)).2 i rfl
  exact (h2 j).1 rfl

lemma parent_injective I (hs : simplex SC n1 I) J j
    (h1 : I = @delete_vertex SC n1 hn1 j J) (h2 : J j ∉ Set.range I)
    : Function.Injective J := by
  have h5 j3 : j3 ≠ j → ∃ i3, j3 = @insert_index SC n1 hn1 j i3
    := by {apply almost_surjective_of_insert_index}
  intro j1 j2 h4
  have h7 j3 : J j3 = J j → j3 = j := by
      intro h7
      by_contra h51
      apply h2
      obtain ⟨i3, hi3⟩ := h5 j3 h51
      use i3
      rw [←h7,h1,hi3]
      rfl
  by_cases h8 : j1 = j
  · rw [h8, h7 j2]
    rw [←h8,h4]
  by_cases h9 : j2 = j
  · rw [h9, h7 j1]
    rw [←h9,h4]
  obtain ⟨i1, hi1⟩ := h5 j1 h8
  obtain ⟨i2, hi2⟩ := h5 j2 h9
  suffices h11 : i1 = i2 by {rw [hi1,hi2,h11] }
  apply hs.1
  rw [h1]
  unfold delete_vertex
  rw [← hi1,← hi2, h4]

lemma parent_simplex_case_BC I (hs : simplex SC n1 I) J
    (h1 : I = @delete_vertex SC n1 hn1 0 J) (h2 : J 0 ≠ I 0)
    (h3 : ∀ k, J 0 k ≤ I 0 k ∧ (I (Fin.last n1) k).1 ≤ (J 0 k).1 + 1) : is_face SC I J := by
  suffices h4 : simplex SC SC.n J by
    rw [child_simplex_char]
    use 0
    exact h4
  have h4 : J 0 ∉ Set.range I := by
    intro h5
    obtain ⟨i1, hi1⟩ := h5
    apply h2
    apply funext
    intro k
    apply le_antisymm (h3 k).1
    rw [←hi1]
    apply monotone_1_of_simplex SC I hs _ _ (Fin.zero_le i1)
  apply And.intro ( parent_injective SC I hs J 0 h1 h4)
  have h5 j2 : j2 < n1 + 1 →  J (Fin.ofNat _ (j2+1)) = I (Fin.ofNat _ j2) := by
    rw [h1]
    unfold delete_vertex insert_index
    congr! with h7
    simp only [Fin.ofNat_eq_cast, Fin.val_zero, not_lt_zero, ↓reduceIte]
    rw [Fin.val_cast_of_lt, Fin.val_cast_of_lt h7]
    omega
  intro j1 hj1 k1
  apply And.intro
  · rw [←hn1] at hj1
    rw [h5 j1 hj1]
    cases j1
    · simp only [Fin.ofNat_eq_cast, Fin.val_fin_le]
      exact (h3 k1).1
    rename_i j2
    rw [h5 j2]
    apply monotone_1_of_simplex SC I hs
    simp only [Fin.ofNat_eq_cast]
    apply Fin.natCast_mono
    exact Nat.le_of_lt_succ hj1
    exact Nat.le_add_right j2 1
    exact Nat.lt_of_succ_lt hj1
  · have h6 := h5 n1 (lt_add_one n1)
    have e1 : (Fin.ofNat (SC.n + 1) (n1 + 1) : Fin (SC.n + 1)) = Fin.last SC.n := by
      rw [← hn1]; simp [Fin.ofNat_eq_cast, Fin.natCast_eq_last]
    have e2 : (Fin.ofNat (n1 + 1) n1 : Fin (n1 + 1)) = Fin.last n1 := by
      simp [Fin.ofNat_eq_cast, Fin.natCast_eq_last]
    rw [e1, e2] at h6
    rw [congrFun h6 k1]
    exact (h3 k1).2

lemma parent_simplex_case_AC I (hs : simplex SC n1 I) J j (hj : j = Fin.last SC.n)
    (h1 : I = @delete_vertex SC n1 hn1 j J) (h2 : J j ≠ I (Fin.last n1))
    (h3 : ∀ k, I (Fin.last n1) k ≤ J j k ∧ (J j k).1 ≤ (I 0 k).1 + 1) : is_face SC I J := by
  suffices h4 : simplex SC SC.n J by
    rw [child_simplex_char]
    use j
    exact h4
  have h4 : J j ∉ Set.range I := by
    intro h5
    obtain ⟨i1, hi1⟩ := h5
    apply h2
    apply funext
    intro k
    apply le_antisymm _ (h3 k).1
    rw [←hi1]
    apply monotone_1_of_simplex SC I hs _ _ (Fin.le_last i1)
  have h5 j2 : j2 < SC.n → J (Fin.ofNat _ j2) = I (Fin.ofNat _ j2) := by
    intro h6
    rw [h1,hj]
    unfold delete_vertex insert_index
    congr!
    have h7 : (Fin.ofNat (n1+1) j2).1 < (Fin.last SC.n).1 := by
      simp only [Fin.ofNat_eq_cast, Fin.val_last]
      rw [Fin.val_cast_of_lt]
      exact h6
      rwa [←hn1] at h6
    simp only [h7,↓reduceIte]
    simp only [Fin.ofNat_eq_cast]
    rw [Fin.val_cast_of_lt, Fin.val_cast_of_lt]
    rwa [←hn1] at h6
    exact Nat.lt_add_right 1 h6
  apply And.intro ( parent_injective SC I hs J j h1 h4)
  intro j1 hj1 k1
  apply And.intro
  · rw [h5 _ hj1]
    by_cases h12 : j1 + 1 < SC.n
    · rw [h5 _ h12]
      apply monotone_1_of_simplex SC I hs
      simp only [Fin.ofNat_eq_cast]
      apply Fin.natCast_mono
      apply Nat.le_of_lt_add_one
      rwa [hn1]
      exact Nat.le_add_right j1 1
    have h16 : j1+1 = SC.n := by omega
    have h13 : Fin.ofNat _ j1 = Fin.last n1 := by
      suffices h15 : j1 = n1 by
        simp only [h15, Fin.ofNat_eq_cast, Fin.natCast_eq_last]
      omega
    have h14 : Fin.ofNat _ (j1+1) = j := by
      rw [hj]
      simp only [h16, Fin.ofNat_eq_cast, Fin.natCast_eq_last]
    rw [h13,h14]
    exact (h3 k1).1
  · have h7 : J 0 = I 0 := by
      have h6 := h5 0 (Nat.zero_lt_of_lt hj1)
      simp only [Fin.ofNat_eq_cast] at h6
      exact h6
    rw [h7,←hj]
    exact (h3 k1).2

noncomputable def coord_change_count (v1 v2 : SC.G) := Finset.card {i | v1 i ≠ v2 i}

lemma ccc_add {m} I (hs : simplex SC m I) (i1 i2 i3) (h1 : i1 ≤ i2 ∧ i2 ≤ i3) :
    coord_change_count SC (I i1) (I i3) =
    coord_change_count SC (I i1) (I i2) + coord_change_count SC (I i2) (I i3) := by
  unfold coord_change_count
  rw [←Finset.card_union_of_disjoint]
  congr
  apply Finset.ext_iff.mpr
  intro k2
  simp only [ne_eq, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union]
  rw [←Decidable.not_and_iff_not_or_not]
  apply Iff.intro
  · intro h3 h4
    apply h3
    rw [h4.1, h4.2]
  · intro h2 h3
    apply h2
    have h4 := monotone_1_of_simplex SC I hs i1 i2 h1.1 k2
    have h5 := monotone_1_of_simplex SC I hs i2 i3 h1.2 k2
    rw [h3] at h4 ⊢
    suffices h1 : I i3 k2 = I i2 k2 by exact ⟨h1, Eq.symm h1⟩
    exact Fin.le_antisymm h4 h5
  · apply Finset.disjoint_filter.mpr
    intro k1 hk1 h2 h3
    apply h3
    have h4 : ∀ k, I i1 k ≤ I i2 k :=  monotone_1_of_simplex SC I hs i1 i2 h1.1
    have h5 : I i1 k1 < I i2 k1 := lt_of_le_of_ne (h4 k1) h2
    have h6 : (I i3 k1).1 ≤ (I i1 k1).1 + 1 := by
      apply le_add_one_of_simplex _ _ hs
    apply le_antisymm ( monotone_1_of_simplex SC I hs i2 i3 h1.2 k1)
    apply le_trans h6 h5

lemma ccc_pos {m} I (hs : simplex SC m I) i1 i2 (h1 : i1 ≠ i2)
    : 0 < coord_change_count SC (I i1) (I i2) := by
  unfold coord_change_count
  by_contra! h2
  apply h1
  apply hs.1
  simp only [ne_eq, nonpos_iff_eq_zero, Finset.card_eq_zero] at h2
  apply funext
  intro k
  rw [Finset.filter_eq_empty_iff] at h2
  simp only [Finset.mem_univ, Decidable.not_not, forall_const] at h2
  apply h2

noncomputable def ccc_fun {m} (I : Fin (m+1)→ SC.G) (i : Fin (m+1)) : Fin (SC.n + 1 )
    := ⟨ coord_change_count SC (I 0) (I i), by {
      refine Nat.lt_succ_of_le ?_
      exact card_finset_fin_le {i_1 | I 0 i_1 ≠ I i i_1}
    } ⟩

lemma ccc_fun_strict_mono {m} I (hs : simplex SC m I) :
    StrictMono (ccc_fun SC I) := by
  intro i1 i2 h1
  unfold ccc_fun
  simp only [Fin.mk_lt_mk]
  have h3 : 0 ≤ i1 ∧ i1 ≤ i2 := ⟨ (Fin.zero_le i1), (Fin.le_of_lt h1) ⟩
  rw [ccc_add SC I hs 0 i1 i2 h3]
  simp only [lt_add_iff_pos_right, gt_iff_lt]
  apply ccc_pos SC I hs _ _ $ Fin.ne_of_lt h1

lemma ccc_fun_is_insert_index I (hs : simplex SC n1 I) :
    ∃ j, ccc_fun SC I = @insert_index SC n1 hn1 j := by
  apply is_insert_index_of_strict_mono
  apply ccc_fun_strict_mono SC I hs

lemma ccc_fun_case_D_iff {m} I (hs : simplex SC m I) :
    case_D SC I ↔ ccc_fun SC I (Fin.last m) = Fin.last SC.n := by
  have h1 : (ccc_fun SC I (Fin.last m) = Fin.last SC.n) ↔ ∀ k, I 0 k ≠ I (Fin.last m) k  := by
    have key : ∀ s : Finset (Fin SC.n), s.card = SC.n ↔ s = Finset.univ := fun s => by
      rw [← Finset.card_eq_iff_eq_univ, Fintype.card_fin]
    unfold ccc_fun coord_change_count
    rw [Fin.ext_iff]
    simp only [Fin.val_last]
    rw [key, Finset.eq_univ_iff_forall]
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  apply Iff.trans _ h1.symm
  unfold case_D
  apply Iff.intro
  · intro h2 k1
    obtain ⟨i2, hi2⟩ := h2 k1 (I 0 k1)
    intro h3
    apply hi2
    apply le_antisymm
    · rw [h3]
      apply monotone_1_of_simplex SC I hs _ _ (Fin.le_last i2)
    exact monotone_1_of_simplex SC I hs _ _ (Fin.zero_le i2) k1
  · contrapose!
    intro h2
    obtain ⟨k2, ⟨q, hq⟩ ⟩ := h2
    use k2
    rw [hq, hq]

lemma last_eq_first_add_one J (hs : simplex SC SC.n J)
    : ∀ k, (J (Fin.last SC.n) k).1 = (J 0 k).1 + 1 := by
  have h3 : ∀ j3, ccc_fun SC J j3 = j3 := by
    apply is_id_of_strict_mono
    apply ccc_fun_strict_mono SC J hs
  have h2 := (ccc_fun_case_D_iff SC J hs).mpr (h3 _)
  unfold case_D at h2
  intro k
  apply le_antisymm  (last_of_simplex SC J hs k)
  apply Nat.add_one_le_of_lt
  obtain ⟨j1, hj1⟩ := h2 k (J 0 k)
  have h4 := monotone_1_of_simplex SC J hs _ _ (Fin.le_last j1) k
  apply lt_of_lt_of_le _ h4
  apply lt_of_le_of_ne (monotone_1_of_simplex SC J hs _ _ (Fin.zero_le j1) k) hj1.symm

lemma delete_vertex_ccc_fun_match J (hs : simplex SC SC.n J) j1 j2
    ( h1 : ccc_fun SC (@delete_vertex SC n1 hn1 j1 J) = @insert_index SC n1 hn1 j2)
    : (j1 = 0 → j2 = Fin.last SC.n) ∧ (j1 ≠ 0 → j1 = j2) := by
  let I := @delete_vertex SC n1 hn1 j1 J
  have hsI : simplex SC n1 I := by
    suffices h2 : is_face SC I J by { exact h2.1}
    rw [@child_simplex_char SC n1 hn1 I J hs]
    use j1
  have scnpos : 0 < SC.n := by omega
  by_cases h4 : j1 = 0
  · simp only [h4, forall_const, ne_eq, not_true_eq_false, IsEmpty.forall_iff, and_true]
    have h5 : I 0 = J 1 := by
      unfold I delete_vertex insert_index
      congr!
      rw [h4]
      simp only [Fin.val_zero, lt_self_iff_false, ↓reduceIte, zero_add]
      simp only [Fin.val_one']
      refine Eq.symm (Nat.mod_eq_of_lt ?_)
      exact Nat.lt_add_of_pos_left scnpos
    symm
    by_contra h6
    obtain ⟨i1, hi1⟩ := @almost_surjective_of_insert_index SC n1 hn1 _ _ h6
    have h8 : (ccc_fun SC I i1).1 = SC.n := by
      unfold I
      rw [h1, ← hi1]
      simp only [Fin.val_last]
    unfold ccc_fun at h8
    simp only [h5] at h8
    unfold I delete_vertex at h8
    let c2 := coord_change_count SC (J 0) (J 1)
    have c2pos : 0 < c2 := by
      apply ccc_pos _ _ hs
      simp only [ne_eq, Fin.zero_eq_one_iff, Nat.add_eq_right]
      omega
    let j3 := @insert_index SC n1 hn1 j1 i1
    have h9 : (ccc_fun SC J j3).1 = c2 + SC.n:= by
      simp only [← h8]
      apply ccc_add SC J hs
      simp only [Fin.zero_le, true_and]
      suffices h9 : j3 ≠ j1 by
        rw [h4] at h9
        exact Fin.one_le_of_ne_zero h9
      apply insert_index_ne
    have h10 : c2 + SC.n ≤ SC.n := by
      rw [←h9]
      exact Fin.is_le (ccc_fun SC J j3)
    simp only [add_le_iff_nonpos_left, nonpos_iff_eq_zero] at h10
    omega
  simp only [h4, IsEmpty.forall_iff, ne_eq, not_false_eq_true, forall_const, true_and]
  have h2 : I 0 = J 0 := by
    unfold I delete_vertex
    congr!
    unfold insert_index
    simpa only [Fin.val_zero, Fin.val_pos_iff, zero_add, Fin.mk_eq_zero,
        ite_eq_left_iff, not_lt,Fin.le_zero_iff, one_ne_zero, imp_false]
  have h3 : ∀ j3, ccc_fun SC J j3 = j3 := by
    apply is_id_of_strict_mono
    apply ccc_fun_strict_mono SC J hs
  symm
  by_contra h5
  obtain ⟨i1, hi1⟩ := @almost_surjective_of_insert_index SC n1 hn1 _ _ h5
  have h6 : ccc_fun SC I i1 = ccc_fun SC J j2 := by
    unfold ccc_fun
    simp [h2]
    congr
    rw [hi1]
    rfl
  rw [h1, h3 j2] at h6
  contrapose h6
  apply insert_index_ne

lemma case_D_iff_not_end_1 I (hs : simplex SC n1 I) j
    (h1 : ccc_fun SC I = @insert_index SC n1 hn1 j) :
    case_D SC I ↔ j ≠ 0 ∧ j ≠ Fin.last SC.n := by
  rw [ccc_fun_case_D_iff SC I hs, h1]
  have h2 : j ≠ 0 := by
    intro h3
    apply @insert_index_ne SC n1 hn1 j 0
    rw [←h1, h3]
    unfold ccc_fun coord_change_count
    simp only [ne_eq, not_true_eq_false, Finset.filter_false, Finset.card_empty, Fin.zero_eta]
  simp only [ne_eq, h2, not_false_eq_true, true_and]
  apply Iff.intro
  · intro h3 h4
    apply @insert_index_ne SC n1 hn1 j (Fin.last n1)
    rw [h3,h4]
  · intro h3
    have h32 : Fin.last SC.n ≠ j := fun a ↦ h3 (Eq.symm a)
    obtain ⟨i2, hi2⟩  := @almost_surjective_of_insert_index SC n1 hn1 j (Fin.last SC.n) h32
    apply le_antisymm
    exact Fin.le_last (insert_index SC j (Fin.last n1))
    rw [hi2]
    have h4 := @insert_index_strict_mono SC n1 hn1 j
    rw [h4.le_iff_le]
    exact Fin.le_last i2

lemma case_D_iff_not_end_2 J (hs : simplex SC SC.n J) j :
    case_D SC (@delete_vertex SC n1 hn1 j J) ↔ j ≠ 0 ∧ j ≠ Fin.last SC.n := by
  let I := @delete_vertex SC n1 hn1 j J
  have hsI : simplex SC n1 I := by
    suffices h2 : is_face SC I J by exact h2.1
    rw [@child_simplex_char SC n1 hn1 I J hs]
    use j
  obtain ⟨j2, hj2⟩ := @ccc_fun_is_insert_index SC n1 hn1 I hsI
  have h1 := @delete_vertex_ccc_fun_match SC n1 hn1 J hs j j2 hj2
  by_cases h2 : j = 0
  · rw [ccc_fun_case_D_iff SC I hsI]
    simp only [h2, ne_eq, not_true_eq_false, Fin.zero_eq_last_iff, false_and, iff_false]
    rw [←h1.1 h2, hj2]
    apply insert_index_ne
  rw [@case_D_iff_not_end_1 SC n1 hn1 I hsI]
  rw [hj2, ← h1.2 h2]

lemma same_delete_index_eq_iff J1 J2 j
    (h1 : @delete_vertex SC n1 hn1 j J1 = @delete_vertex SC n1 hn1 j J2)
    : J1 = J2 ↔ J1 j = J2 j := by
  apply Iff.intro (fun a ↦ congrFun a j)
  intro h2
  ext j2
  by_cases h3 : j2 = j
  rw [h3,h2]
  obtain ⟨i1, hi1⟩ := @almost_surjective_of_insert_index SC n1 hn1 j j2 h3
  rw [hi1]
  exact congrFun h1 i1

lemma unique_const_ABC {hn1 : n1 + 1 = SC.n} I (hs : simplex SC n1 I) k1 q1
    (h1 : ∀ i, I i k1 = q1): ∀ k2, k1 ≠ k2 → I 0 k2 ≠ I (Fin.last n1) k2 := by
  intro k2 h3 h2
  let s : Finset (Fin SC.n) := {i | I 0 i ≠ I (Fin.last n1) i}
  have h4 : n1 ≤ s.card := by
    obtain ⟨j, hj⟩ := @ccc_fun_is_insert_index SC n1 hn1 I hs
    show n1 ≤ (ccc_fun SC I (Fin.last n1)).1
    rw [hj]
    unfold insert_index
    simp only [Fin.val_last]
    by_cases h11 : n1 < j.1
    simp only [h11, ↓reduceIte, le_refl]
    simp only [h11, ↓reduceIte, le_add_iff_nonneg_right, zero_le]
  have h6 : 2 ≤ sᶜ.card := by
    show 1 < sᶜ.card
    rw [Finset.one_lt_card]
    use k2
    unfold s
    simp only [ne_eq, Finset.compl_filter, Decidable.not_not, Finset.mem_filter,
        Finset.mem_univ,h2, and_self, true_and]
    use k1
    apply And.intro _ h3.symm
    rw [h1,h1]
  have h7 := add_le_add h4 h6
  simp only [Finset.card_add_card_compl, Fintype.card_fin] at h7
  rw [←hn1,add_le_add_iff_left] at h7
  simp only [Nat.not_ofNat_le_one] at h7

lemma case_AC_ex_unique I (hs : simplex SC n1 I) k1 q
    (hABC : ∀ i, I i k1 = q) (hAC : q ≠ Fin.last SC.p)
    : ∃! J, I = @delete_vertex SC n1 hn1 (Fin.last SC.n) J ∧ is_face SC I J := by
  have h1 k2 : I 0 k2 ≠ Fin.last SC.p := by
    intro h11
    have h12 : k1 ≠ k2 := by
      intro h13
      apply hAC
      rw [←hABC 0,h13,h11]
    apply @unique_const_ABC SC n1 hn1 I hs k1 q hABC k2 h12
    apply le_antisymm
    apply monotone_1_of_simplex SC I hs
    exact Fin.zero_le (Fin.last n1)
    rw [h11]
    exact Fin.le_last (I (Fin.last n1) k2)
  let ins2 : SC.G := fun k ↦ (I 0 k) + 1
  have h2 k : (ins2 k).1 = (I 0 k).1 + 1 := by
    apply Fin.val_add_one_of_lt
    rw [Fin.lt_last_iff_ne_last]
    exact h1 k
  obtain ⟨J1, hJ1⟩ := @insert_vertex SC n1 hn1 I ins2 (Fin.last SC.n)
  have h3 : J1 (Fin.last SC.n) ≠ I (Fin.last n1) := by
    intro h12
    have h11 : I 0 k1 = I 0 k1 + 1 := by
      show I 0 k1 = ins2 k1
      rw [←hJ1.2, h12,hABC,hABC]
    simp only [left_eq_add, Fin.one_eq_zero_iff, Nat.add_eq_right] at h11
    apply @p_ne_zero_of_cube SC n1 hn1
    simp only [Fin.last_eq_zero_iff, h11]
  have h4 : is_face SC I J1 := by
    apply parent_simplex_case_AC SC I hs J1 (Fin.last SC.n) rfl hJ1.1 h3
    intro k2
    rw [hJ1.2]
    apply And.intro
    · rw [Fin.le_def, h2 k2]
      apply le_add_one_of_simplex SC I hs
    rw [h2 k2]
  use J1
  simp only
  apply And.intro (And.intro hJ1.1 h4)
  intro J2 hJ2
  rw [@same_delete_index_eq_iff SC n1 hn1 _ _ _ (hJ2.1.symm.trans hJ1.1)]
  rw [hJ1.2]
  apply funext
  intro k1
  ext
  have h5 := last_eq_first_add_one SC J2 hJ2.2.2.1 k1
  rw [h5, h2 k1]
  suffices h6 : I 0 = J2 0 by {rw [h6]}
  rw [hJ2.1]
  unfold delete_vertex insert_index
  congr!
  simp only [Fin.val_zero, Fin.val_last, zero_add, ite_eq_left_iff,
    not_lt, nonpos_iff_eq_zero,one_ne_zero, imp_false]
  rw [←hn1]
  omega

lemma case_B_not_last I (h1 : case_B SC I) J
    (h2 : I = @delete_vertex SC n1 hn1 (Fin.last SC.n) J ∧ is_face SC I J) : False := by
  have h3 := last_eq_first_add_one SC J h2.2.2.1
  obtain ⟨k1, hk1⟩ := h1
  have h4 : I 0 = J 0 := by
    rw [h2.1]
    unfold delete_vertex insert_index
    congr!
    simp only [Fin.val_zero, Fin.val_last, zero_add, ite_eq_left_iff,
        not_lt, nonpos_iff_eq_zero,one_ne_zero, imp_false]
    rw [←hn1]
    omega
  have h5 := (J (Fin.last SC.n) k1).is_le
  rw [h3 k1,←h4,hk1 0] at h5
  contrapose! h5
  exact lt_add_one SC.p

lemma case_BC_ex_unique I (hs : simplex SC n1 I) k1 q
    (hABC : ∀ i, I i k1 = q) (hBC : q ≠ 0)
    : ∃! J, I = @delete_vertex SC n1 hn1 0 J ∧ is_face SC I J := by
  have h1 k2 : I (Fin.last n1) k2 ≠ 0 := by
    intro h11
    have h12 : k1 ≠ k2 := by
      intro h13
      apply hBC
      rw [←hABC (Fin.last n1),h13,h11]
    apply @unique_const_ABC SC n1 hn1 I hs k1 q hABC k2 h12
    apply le_antisymm
    apply monotone_1_of_simplex SC I hs
    exact Fin.zero_le (Fin.last n1)
    rw [h11]
    exact Fin.zero_le (I 0 k2)
  let ins2 : SC.G := fun k ↦ (I (Fin.last n1) k) - 1
  have h22 k := Fin.val_sub_one_of_ne_zero (h1 k)
  have h21 k : (ins2 k).1 + 1 = (I (Fin.last n1) k).1  := by
    rw [h22]
    apply Nat.sub_one_add_one ( Fin.val_ne_zero_iff.mpr (h1 k))
  obtain ⟨J1, hJ1⟩ := @insert_vertex SC n1 hn1 I ins2 0
  have h3 : J1 0 ≠ I 0 := by
    intro h12
    have h11 : (ins2 k1).1 + 1 = ins2 k1 := by
      rw [h21 k1, hABC, ←hJ1.2,h12,hABC]
    simp only [Nat.add_eq_left, one_ne_zero] at h11
  have h4 : is_face SC I J1 := by
    apply parent_simplex_case_BC SC I hs J1 hJ1.1 h3
    intro k2
    rw [hJ1.2]
    apply And.intro
    rw [Fin.le_def, ←add_le_add_iff_right 1, h21 k2]
    exact le_add_one_of_simplex SC I hs (Fin.last n1) 0 k2
    rw [h21 k2]
  use J1
  simp only
  apply And.intro (And.intro hJ1.1 h4)
  intro J2 hJ2
  rw [@same_delete_index_eq_iff SC n1 hn1 _ _ _ (hJ2.1.symm.trans hJ1.1), hJ1.2]
  apply funext
  intro k1
  ext
  have h5 := last_eq_first_add_one SC J2 hJ2.2.2.1 k1
  have h6 : I (Fin.last n1) = J2 (Fin.last SC.n) := by
    rw [hJ2.1]
    unfold delete_vertex insert_index
    simp only [Fin.val_last, Fin.val_zero, not_lt_zero, ↓reduceIte]
    congr!
  rw [←h6, ←h21 k1] at h5
  omega

lemma zero_ne_last {hn1 : n1 + 1 = SC.n} : 0 ≠ Fin.last SC.n := by
  simp only [ne_eq, Fin.zero_eq_last_iff]
  rw [←hn1]
  omega

lemma case_A_not_zero I (h1 : case_A SC I) J
    (h2 : I = @delete_vertex SC n1 hn1 0 J ∧ is_face SC I J) : False := by
  have h3 := last_eq_first_add_one SC J h2.2.2.1
  obtain ⟨k1, hk1⟩ := h1
  have h4 : I (Fin.last n1) = J (Fin.last SC.n) := by
    rw [h2.1]
    unfold delete_vertex insert_index
    simp only [Fin.val_last, Fin.val_zero, not_lt_zero, ↓reduceIte]
    congr!
  apply Nat.zero_ne_add_one (J 0 k1).1
  rw [←h3 k1,← h4,hk1]
  rfl

lemma case_ABC_count_disj {hn1 : n1 + 1 = SC.n} I k1 q
    (hABC : ∀ i, I i k1 = q) : Finset.card { J | is_face SC I J}
    = Finset.card {J | I = @delete_vertex SC n1 hn1 0 J ∧ is_face SC I J}
    + Finset.card {J | I = @delete_vertex SC n1 hn1 (Fin.last SC.n) J ∧ is_face SC I J} := by
  have hnd : ¬ case_D SC I := by
    contrapose! hABC
    exact hABC k1 q
  rw [←Finset.card_union_of_disjoint]
  congr
  ext J
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union]
  apply Iff.intro
  · intro h1
    simp only [h1, and_true]
    rw [child_simplex_char] at h1
    obtain ⟨j1, hj1⟩ := h1
    have h2 := @case_D_iff_not_end_2 SC n1 hn1 J h1.2.1 j1
    rw [hj1,h2] at hnd
    have h3 := Decidable.or_iff_not_not_and_not.mpr hnd
    cases' h3 with h3 h3
    rw [hj1,h3]
    exact Or.inl rfl
    rw [hj1,h3]
    exact Or.inr rfl
    · exact hn1
    · exact h1.2.1
  · intro h1
    rw [←or_and_right] at h1
    exact h1.2
  apply Finset.disjoint_filter.mpr
  intro J h1 h2 h3
  apply @zero_ne_last SC n1 hn1
  apply @delete_vertex_inj SC n1 hn1 J h2.2.2.1
  rw [←h2.1,←h3.1]

lemma case_C_parent_count {hn1 : n1 + 1 = SC.n} I (hs : simplex SC n1 I) (h1 : case_C SC I )
    : Finset.card { J : Fin (SC.n + 1) → SC.G | is_face SC I J} = 2 := by
  obtain ⟨k1,q, h1⟩  := h1
  have h2 := @case_AC_ex_unique SC n1 hn1 I hs k1 q h1.2 h1.1.2
  have h3 := @case_BC_ex_unique SC n1 hn1 I hs k1 q h1.2 h1.1.1
  rw [Fintype.existsUnique_iff_card_one] at h2 h3
  rw [case_ABC_count_disj SC I k1 q h1.2,h2,h3]
  exact hn1

lemma case_B_parent_count {hn1 : n1 + 1 = SC.n} I (hs : simplex SC n1 I) (h2 : case_B SC I )
    : Finset.card { J : Fin (SC.n + 1) → SC.G | is_face SC I J} = 1 := by
  obtain ⟨k1, h1⟩  := id h2
  have h4 : Fin.last SC.p ≠ 0 := @p_ne_zero_of_cube SC n1 hn1
  have h3 := @case_BC_ex_unique SC n1 hn1 I hs k1 _ h1 h4
  rw [Fintype.existsUnique_iff_card_one] at h3
  rw [case_ABC_count_disj SC I k1 (Fin.last SC.p) h1, h3]
  simp only [Nat.add_eq_left]
  apply Finset.card_filter_eq_zero_iff.mpr
  intro J h5
  apply case_B_not_last SC I h2
  exact hn1

lemma case_A_parent_count {hn1 : n1 + 1 = SC.n} I (hs : simplex SC n1 I) (h2 : case_A SC I )
    : Finset.card { J : Fin (SC.n + 1) → SC.G | is_face SC I J} = 1 := by
  obtain ⟨k1, h1⟩  := id h2
  have h4 : Fin.last SC.p ≠ 0 := @p_ne_zero_of_cube SC n1 hn1
  have h3 := @case_AC_ex_unique SC n1 hn1 I hs k1 _ h1 h4.symm
  rw [Fintype.existsUnique_iff_card_one] at h3
  rw [case_ABC_count_disj SC I k1 0 h1, h3]
  simp only [Nat.add_eq_right]
  apply Finset.card_filter_eq_zero_iff.mpr
  intro J h5
  apply case_A_not_zero SC I h2
  exact hn1

end Sol_Plasticity_Ext_Brouwer_parent_count

theorem solution (SC : CubicalSperner.SpernerCube) {n1 : ℕ} (hn1 : n1 + 1 = SC.n)
    (I : Fin (n1 + 1) → SC.G) (hI : CubicalSperner.simplex SC n1 I) :
    (((∃ j, ∀ k, I k j = 0) ∨ (∃ j, ∀ k, I k j = Fin.last SC.p)) →
      Nat.card {J : Fin (SC.n + 1) → SC.G // CubicalSperner.is_face SC I J} = 1) ∧
    (¬((∃ j, ∀ k, I k j = 0) ∨ (∃ j, ∀ k, I k j = Fin.last SC.p)) →
      Nat.card {J : Fin (SC.n + 1) → SC.G // CubicalSperner.is_face SC I J} = 2) := by
  classical
  simp only [Nat.card_eq_fintype_card, Fintype.card_subtype]
  refine ⟨fun h => ?_, fun h => ?_⟩
  · rcases h with h | h
    · convert Sol_Plasticity_Ext_Brouwer_parent_count.case_A_parent_count SC (hn1 := hn1) I hI h
    · convert Sol_Plasticity_Ext_Brouwer_parent_count.case_B_parent_count SC (hn1 := hn1) I hI h
  · rcases Sol_Plasticity_Ext_Brouwer_parent_count.one_of_ABCD SC I with h1 | h1 | h1 | h1
    · exact absurd (Or.inl h1) h
    · exact absurd (Or.inr h1) h
    · convert Sol_Plasticity_Ext_Brouwer_parent_count.case_C_parent_count SC (hn1 := hn1) I hI h1
    · convert Sol_Plasticity_Ext_Brouwer_parent_count.case_D_parent_count SC (hn1 := hn1) I hI h1
