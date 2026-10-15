-- Prove2me | solution 1 for Plasticity.Ext.Brouwer.interior
-- status  : ACCEPTED   (prove)
-- author  : @scanstone
-- created : 2026-10-14T09:31:24.631102+00:00
-- url     : https://prove2.me/submissions/9463590d-882d-411b-9ab0-665dacf4210b

import Definitions.Def_Plasticity_CubicalSperner
import Theorems.Thm_Plasticity_Ext_Brouwer_facets
import Mathlib.Data.Fintype.Card
import Mathlib.Order.Fin.Basic
import Mathlib.Tactic.ByContra
import Mathlib.Tactic.Contrapose
import Mathlib.Tactic.Use
import Mathlib.Tactic.Convert
import Mathlib.Tactic.NthRewrite
import Mathlib.Tactic.Cases
import Mathlib.Tactic.CongrExclamation
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Algebra.Order.Group.Nat

/-!
# Interior grid simplices have exactly two parents

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

namespace Sol_Plasticity_Ext_Brouwer_interior

open Classical

variable (SC : SpernerCube)
variable {n1 : ℕ}
variable {hn1 : n1 + 1 = SC.n}

/-- No coordinate is constant along `I`. -/
def case_D (I : Fin (n1 +1) → SC.G) := ∀ j, ∀ q, ∃ k,I k j ≠ q

/-- Facets of a full simplex are its vertex deletions (child card `Plasticity.Ext.Brouwer.facets`). -/
lemma child_simplex_char (I : Fin (n1 +1) → SC.G) J {hs : simplex SC SC.n J}
    : is_face SC I J ↔ ∃ i, I = @delete_vertex SC n1 hn1 i J :=
  Plasticity.Ext.Brouwer.facets SC hn1 I J hs

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

lemma monotone_2_of_simplex {m:ℕ } (I : Fin (m+1)→ SC.G) (hs : simplex SC m I) (i1 i2 : Fin (m+1)) :
    i1 ≤ i2 ↔ ∀ j, I i1 j ≤ I i2 j := by
  apply Iff.intro
  · intro h1 j
    apply monotone_1_of_simplex _ I hs i1 i2 h1
  · intro h1
    by_contra h2
    have h3 : i1 ≠ i2 := ne_of_not_le h2
    apply h3
    apply hs.1
    apply funext
    intro j
    apply le_antisymm (h1 j)
    apply monotone_1_of_simplex _ _ hs i2 i1 (le_of_not_ge h2)

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

lemma surround_index (j : Fin (SC.n + 1)) (i : Fin (n1 + 1)) (hij : i.1 + 1 = j.1 )
    (hj1 : j ≠ Fin.last SC.n): ((@insert_index SC n1 hn1 j i).1 + 1 = j.1
    ∧ j.1 + 1 = @insert_index SC n1 hn1 j (i+1)) := by
  unfold insert_index
  have h2 : i.1 < j.1 := by omega
  have h3 : (i+1).1 = i.1 + 1 := by
    refine Fin.val_add_one_of_lt ?_
    simp only [Nat.succ_eq_add_one]
    show i.1 < n1
    have h6 := Fin.val_lt_last hj1
    omega
  apply And.intro
  · simp only [h2, ↓reduceIte]
    exact hij
  simp only [h3, hij, lt_self_iff_false, ↓reduceIte]

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

lemma parent_simplex_case_D I (hs : simplex SC n1 I) J j i
    (hij : i.1 + 1 = j.1 ) (h1 : I = @delete_vertex SC n1 hn1 j J) (h2 : J j ∉ Set.range I)
    (h3 : ∀ k, I i k ≤ J j k ∧ J j k ≤ I (i+1) k) : is_face SC I J := by
  suffices h4 : simplex SC SC.n J by
    rw [child_simplex_char]
    use j
    exact h4
  have h5 j3 : j3 ≠ j → ∃ i3, j3 = @insert_index SC n1 hn1 j i3 := by
    apply almost_surjective_of_insert_index
  have h6 j3 : j3 ≠ j → ∃ i3, I i3 = J j3 := by
    intro h7
    obtain ⟨i3, hi3⟩ := h5 j3 h7
    use i3
    rw [h1, hi3]
    rfl
  apply And.intro (parent_injective SC I hs J j h1 h2)
  intro i2 h4 k2
  have h5 := h3 k2
  apply And.intro
  · simp only [Fin.ofNat_eq_cast, Fin.val_fin_le]
    rw [h1] at h5
    unfold delete_vertex at h5
    have h6 : (@insert_index SC n1 hn1 j i).1 + 1 = j := by
      unfold insert_index
      have h7 : i.1 < j.1 := by omega
      simp only [h7, ↓reduceIte]
      exact hij
    by_cases h8 : i2 = j.1
    · convert h5.2
      simp only [h8, Fin.cast_val_eq_self]
      have h11 : j ≠ Fin.last SC.n := by
        suffices h12 : j.1 ≠ SC.n by exact Ne.symm (Fin.ne_of_val_ne (Ne.symm h12))
        rw [←h8]
        exact Nat.ne_of_lt h4
      have h9 := @surround_index SC n1 hn1 j i hij h11
      rw [h8, h9.2]
      exact Fin.cast_val_eq_self (insert_index SC j (i + 1))
    by_cases h9 : i2 + 1 = j.1
    · rw [←h9] at h6
      simp only [Nat.add_right_cancel_iff] at h6
      convert h5.1
      rw [←h6]
      simp only [Fin.cast_val_eq_self]
      rw [h9]
      simp only [Fin.cast_val_eq_self]
    have h11 : ∃ i3, (Fin.ofNat _ i2) = @insert_index SC n1 hn1 j i3 := by
      apply almost_surjective_of_insert_index
      intro h12
      apply h8
      rw [← h12]
      simp only [Fin.ofNat_eq_cast]
      rw [Fin.val_cast_of_lt]
      apply lt_trans h4 (lt_add_one SC.n)
    have h12 : ∃ i3, (Fin.ofNat _ (i2+1)) = @insert_index SC n1 hn1 j i3 := by
      apply almost_surjective_of_insert_index
      intro h12
      apply h9
      rw [← h12]
      simp only [Fin.ofNat_eq_cast]
      rw [Fin.val_cast_of_lt]
      omega
    simp only [Fin.ofNat_eq_cast] at h11 h12
    obtain ⟨i3, hi3⟩ := h11
    obtain ⟨i4, hi4⟩ := h12
    rw [hi3, hi4]
    suffices h21 : I i3 k2 ≤ I i4 k2 by {rwa [h1] at h21}
    apply monotone_1_of_simplex SC I hs
    have h21 : StrictMono (@insert_index SC n1 hn1 j) := by
      apply insert_index_strict_mono
    rw [←h21.le_iff_le]
    rw [←hi3, ← hi4]
    refine (Fin.natCast_le_natCast ?_ h4).mpr ?_
    exact Nat.le_of_succ_le h4
    exact Nat.le_succ i2
  · have h11 : (J (Fin.last SC.n) k2).1 ≤ (I (Fin.last n1) k2).1 := by
      simp only [Fin.val_fin_le]
      by_cases h12 : Fin.last SC.n = j
      · rw [h12]
        apply le_trans h5.2
        apply monotone_1_of_simplex SC I hs _ _ (Fin.le_last _)
      obtain ⟨ i3, hi3⟩ := h6 _ h12
      rw [←hi3]
      apply monotone_1_of_simplex SC I hs _ _ (Fin.le_last _)
    have h13 := last_of_simplex SC I hs k2
    apply le_trans h11 (le_trans h13 _)
    simp only [add_le_add_iff_right, Fin.val_fin_le]
    by_cases h14 : 0 = j
    · rw [h14]
      apply le_trans _ h5.1
      apply monotone_1_of_simplex SC I hs _ _ (Fin.zero_le _)
    · obtain ⟨i3, hi3⟩ := h6 _ h14
      rw [← hi3]
      apply monotone_1_of_simplex SC I hs _ _ (Fin.zero_le _)

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

lemma case_D_parent_count {hn1 : n1 + 1 = SC.n} I (hs : simplex SC n1 I) (h1 : case_D SC I )
    : Finset.card { J : Fin (SC.n + 1) → SC.G | is_face SC I J} = 2 := by
  obtain ⟨ j1, hj1 ⟩ := @ccc_fun_is_insert_index SC n1 hn1 I hs
  have h2 : j1 ≠ 0 ∧ j1 ≠ Fin.last SC.n := by
    rw [←case_D_iff_not_end_1 SC I hs j1 hj1]
    exact h1
  have h3 : ∃ (i1: Fin (n1 + 1)), i1.1 + 1 = j1.1 := by
    obtain ⟨a, ha⟩ := Fin.exists_succ_eq_of_ne_zero h2.1
    rw [← ha]
    simp only [Fin.val_succ, Nat.add_right_cancel_iff]
    use ⟨ a.1, by {rw [hn1]; exact a.2}⟩
  obtain ⟨ i1, hi1⟩ := h3
  have h32 : i1 ≤ i1 + 1 := by
    refine Fin.le_of_lt ?_
    refine Fin.lt_add_one_iff.mpr ?_
    show i1.1 < n1
    have h3 := Fin.val_lt_last h2.2
    omega
  have h11 := @surround_index SC n1 hn1 j1 i1 hi1 h2.2
  have h12 : @insert_index SC n1 hn1 j1 i1 ≤ j1 ∧ j1 ≤ @insert_index SC n1 hn1 j1 (i1+1) := by
    rw [Fin.le_def, Fin.le_def, ←h11.2]
    apply And.intro
    rw [←h11.1]
    apply Nat.le_add_right
    apply Nat.le_add_right
  have h3 : coord_change_count SC (I i1) (I (i1+1)) = 2 := by
    have h3 : (@insert_index SC n1 hn1 j1 i1).1 + 2
        = (@insert_index SC n1 hn1 j1 (i1 +1)).1 := by
      rw [← h11.2, ←h11.1]
    have h4 : (ccc_fun SC I (i1+1)).1 = (ccc_fun SC I i1).1
        + coord_change_count SC (I i1) (I (i1 + 1)) := by
      apply ccc_add SC I hs
      simp only [Fin.zero_le, true_and, h32]
    rw [← hj1, h4 ] at h3
    simp only [Nat.add_left_cancel_iff] at h3
    exact h3.symm
  have h4 : ∃ k1, ∃ k2, k1 ≠ k2 ∧ {k | I i1 k ≠ I (i1 +1) k} = {k1, k2} := by
    unfold coord_change_count at h3
    rw [Finset.card_eq_two] at h3
    convert h3
    simp only [ne_eq]
    rw [←Finset.coe_eq_pair]
    simp only [Finset.coe_filter, Finset.mem_univ, true_and]
  obtain ⟨k1, ⟨k2, h4⟩ ⟩ := h4
  have hk1 : I i1 k1 ≠ I (i1+1) k1 := by
    have h5 := Set.mem_insert k1 {k2}
    rwa [←h4.2] at h5
  have hk2 : I i1 k2 ≠ I (i1+1) k2 := by
    have h5 : k2 ∈ ({k1, k2} : Set _) := Set.mem_insert_of_mem k1 rfl
    rwa [←h4.2] at h5
  have h5 k3 : I i1 k3 ≠ I (i1+1) k3 → ∃ J3,
      I = @delete_vertex SC n1 hn1 j1 J3 ∧ is_face SC I J3 ∧ J3 j1 k3 ≠ I i1 k3 := by
    intro h21
    let ins : SC.G := fun k ↦ if k = k3 then I (i1 + 1) k else I i1 k
    obtain ⟨J3, hJ3⟩ := @insert_vertex SC n1 hn1 I ins j1
    have h6 : ∀ k, I i1 k ≤ ins k ∧ ins k ≤ I (i1+1) k := by
      intro k
      unfold ins
      have h13 : I i1 k3 ≤ I (i1+1) k3 := monotone_1_of_simplex SC I hs _ _ h32 k3
      by_cases h12 : k = k3
      simp only [h12, ↓reduceIte, le_refl, and_true, ge_iff_le]
      exact monotone_1_of_simplex SC I hs _ _ h32 k3
      simp only [h12, ↓reduceIte, le_refl, true_and, ge_iff_le]
      exact monotone_1_of_simplex SC I hs _ _ h32 k
    have h22 : J3 j1 k3 ≠ I i1 k3 := by
      rw [hJ3.2]
      unfold ins
      simp only [↓reduceIte, ne_eq]
      exact h21.symm
    have h23 : ∃ k4, k3 ≠ k4 ∧ I i1 k4 ≠ I (i1+1) k4 := by
      by_cases h24 : k3 = k1
      use k2
      rw [h24]
      apply And.intro h4.1 hk2
      use k1
    have h7 : ins ∉ Set.range I := by
      intro h9
      obtain ⟨i2,hi2⟩ := h9
      rw [forall_and, ← hi2] at h6
      rw [← monotone_2_of_simplex _ _ hs,← monotone_2_of_simplex _ _ hs] at h6
      have h13 : i2 = i1 ∨ i2 = i1 + 1 := by
        refine (WCovBy.le_and_le_iff ?_).mp h6
        apply And.intro h32
        intro i3 h33
        simp only [not_lt]
        exact Fin.add_one_le_of_lt h33
      cases' h13 with h13 h13
      apply h22
      rw [hJ3.2, ←hi2, h13]
      obtain ⟨k4, hk4⟩ := h23
      apply hk4.2
      rw [←h13, hi2]
      unfold ins
      simp only [right_eq_ite_iff]
      intro h33
      exact False.elim $ hk4.1 h33.symm
    use J3
    apply And.intro hJ3.1 (And.intro _ h22)
    apply @parent_simplex_case_D SC n1 hn1 I hs J3 _ _ hi1 hJ3.1
    rwa [hJ3.2]
    rwa [hJ3.2]
  obtain ⟨J1, hJ1⟩ := h5 k1 hk1
  obtain ⟨J2, hJ2⟩ := h5 k2 hk2
  have h6 J3 : I = @delete_vertex SC n1 hn1 j1 J3 → is_face SC I J3
    → ∀ k, I i1 k ≤ J3 j1 k ∧ J3 j1 k ≤ I (i1+1) k := by
    intro h14 h13 k3
    rw [h14]
    apply And.intro
    apply monotone_1_of_simplex SC J3 h13.2.1 _ _ h12.1
    apply monotone_1_of_simplex SC J3 h13.2.1 _ _ h12.2
  have h7 J3 k3 : I = @delete_vertex SC n1 hn1 j1 J3 ∧ is_face SC I J3 ∧ J3 j1 k3 ≠ I i1 k3
      → J3 j1 k3 = I (i1+1) k3 ∧ ∀ k4, k3 ≠ k4 → J3 j1 k4 = I i1 k4 := by
    intro h9
    have h6 := h6 J3 h9.1 h9.2.1
    have h31 := h3
    rw [h9.1] at h31
    have h21 := ccc_add SC J3 h9.2.1.2.1 _ _ _ h12
    unfold delete_vertex at h31
    rw [h31] at h21
    have h22 c1 c2 : 2 = c1 + c2 → 0 < c2 → c1 ≤ 1 := by omega
    have h23 : coord_change_count SC (I i1) (J3 j1) ≤ 1 := by
      rw [h9.1]
      apply h22 _ _ h21
      apply ccc_pos SC
      exact h9.2.1.2.1
      symm
      apply insert_index_ne
    apply And.intro
    · apply le_antisymm (h6 k3).2
      rw [Fin.le_def]
      have h24 := le_add_one_of_simplex SC I hs (i1+1) i1 k3
      apply le_trans h24
      apply Fin.val_add_one_le_of_lt (lt_of_le_of_ne (h6 k3).1 h9.2.2.symm)
    intro k4 hk4
    contrapose! h23
    refine Finset.one_lt_card_iff.mpr ?_
    use k3, k4
    simp only [ne_eq, Finset.mem_filter, Finset.mem_univ, true_and]
    exact And.intro h9.2.2.symm ( And.intro h23.symm hk4)
  refine Finset.card_eq_two.mpr ?_
  use J1, J2
  apply And.intro
  · have h71 := (h7 J1 k1 hJ1).2 k2 h4.1
    intro h9
    apply hJ2.2.2
    rw [←h9, h71]
  apply subset_antisymm
  · intro J3
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
      Finset.mem_singleton]
    intro hJ3
    have h14 := (@child_simplex_char SC n1 hn1 I J3 hJ3.2.1).mp hJ3
    obtain ⟨j2, hj2⟩ := h14
    rw [hj2] at hj1
    have h13 := @delete_vertex_ccc_fun_match SC n1 hn1 J3 hJ3.2.1 j2 j1 hj1
    have h15 := @case_D_iff_not_end_2 SC n1 hn1 J3 hJ3.2.1 j2
    rw [←hj2] at h15
    have h16 : j2 = j1 := h13.2 (h15.mp h1).1
    rw [h16] at hj2
    rw [same_delete_index_eq_iff SC J3 J1 j1, same_delete_index_eq_iff SC J3 J2 j1]
    have h71 := h7 J1 k1 hJ1
    have h72 := h7 J2 k2 hJ2
    have h18 : ∃ k5, J3 j1 k5 ≠ I i1 k5 := by
      suffices h19 : J3 j1 ≠ I i1 by exact Function.ne_iff.mp h19
      intro h19
      apply @insert_index_ne SC n1 hn1 j1 i1
      apply hJ3.2.1.1
      rw [h19, hj2]
      rfl
    obtain ⟨k5, hk5⟩ := h18
    have h73 := h7 J3 k5 ⟨hj2, ⟨ hJ3, hk5⟩ ⟩
    clear h15 h13
    have h19 : k5 = k1 ∨ k5 = k2 := by
      have h21 : I i1 k5 ≠ I (i1+1) k5 := by
        rw [←h73.1]
        exact hk5.symm
      exact h4.2.subset h21
    have h20 (J4 : _ → SC.G) : (J4 j1 k5 = I (i1+1) k5 ∧ ∀ k4, k5 ≠ k4 → J4 j1 k4 = I i1 k4)
        → J3 j1 = J4 j1:= by
      intro h21
      apply funext
      intro k6
      by_cases h22 : k5 = k6
      rw [←h22,h21.1,h73.1]
      rw [h21.2 k6 h22, h73.2 k6 h22]
    cases h19
    left
    rename_i h21
    apply h20
    rwa [h21]
    right
    rename_i h21
    apply h20
    rwa [h21]
    rw [←hJ2.1, ←hj2]
    any_goals exact hn1
    rw [←hJ1.1, ←hj2]
  · refine Finset.insert_subset ?_ ?_
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact hJ1.2.1
    simp only [Finset.singleton_subset_iff, Finset.mem_filter, Finset.mem_univ, true_and]
    exact hJ2.2.1

end Sol_Plasticity_Ext_Brouwer_interior

theorem solution (SC : CubicalSperner.SpernerCube) {n1 : ℕ} (hn1 : n1 + 1 = SC.n)
    (I : Fin (n1 + 1) → SC.G) (hI : CubicalSperner.simplex SC n1 I)
    (hD : ∀ (j : Fin SC.n) (q : Fin (SC.p + 1)), ∃ k, I k j ≠ q) :
    Nat.card {J : Fin (SC.n + 1) → SC.G // CubicalSperner.is_face SC I J} = 2 := by
  classical
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  convert Sol_Plasticity_Ext_Brouwer_interior.case_D_parent_count SC (hn1 := hn1) I hI hD
