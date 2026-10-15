-- Prove2me | solution 1 for Plasticity.Ext.Brouwer.facets
-- status  : ACCEPTED   (prove)
-- author  : @scanstone
-- created : 2026-10-14T09:30:53.261222+00:00
-- url     : https://prove2.me/submissions/aa814f11-084e-4492-94f1-36bb31725e79

import Definitions.Def_Plasticity_CubicalSperner
import Mathlib.Data.Fintype.Card
import Mathlib.Order.Fin.Basic
import Mathlib.Tactic.ByContra
import Mathlib.Tactic.Contrapose
import Mathlib.Tactic.Use
import Mathlib.Tactic.Convert
import Mathlib.Tactic.NthRewrite
import Mathlib.Tactic.Cases
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Algebra.Order.Group.Nat

/-!
# Facets of a full-dimensional grid simplex are its vertex deletions

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

namespace Sol_Plasticity_Ext_Brouwer_facets

open Classical

variable (SC : SpernerCube)
variable {n1 : ℕ}
variable {hn1 : n1 + 1 = SC.n}

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

lemma delete_vertex_simplex J {hs : simplex SC SC.n J} i :
    simplex SC n1 (@delete_vertex SC n1 hn1 i J) := by
  apply And.intro
  · intro k1 k2 h2
    apply insert_index_inj SC i
    apply hs.1 h2
  · intro i2 hi2 j
    unfold delete_vertex
    apply And.intro
    · apply monotone_1_of_simplex SC J hs
      rw [StrictMono.le_iff_le]
      · simp only [Fin.ofNat_eq_cast]
        apply Fin.natCast_mono hi2
        exact Nat.le_add_right i2 1
      apply insert_index_strict_mono
    apply le_add_one_of_simplex SC J hs

lemma delete_vertex_is_face J {hs : simplex SC SC.n J} i :
    is_face SC (@delete_vertex SC n1 hn1 i J) J := by
  apply And.intro
  · apply delete_vertex_simplex
    exact hs
  · apply And.intro hs
    intro c hc
    obtain ⟨ i2, hi2 ⟩ := hc
    use @insert_index SC n1 hn1 i i2
    exact hi2

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

lemma child_simplex_char (I : Fin (n1 +1) → SC.G) J {hs : simplex SC SC.n J}
    : is_face SC I J ↔ ∃ i, I = @delete_vertex SC n1 hn1 i J := by
  apply Iff.intro
  · intro h1
    have h2 : ∃ (f : Fin (n1+1) → Fin (SC.n+1)), ∀ k, I k = J (f k) := by
      have h2 := h1.2.2
      have h3 : ∀ k, ∃ j, I k = J j := by
        intro k
        have h4 : I k ∈ Set.range I := by
          exact Set.mem_range_self k
        have h3 := h2 h4
        obtain ⟨j, hj⟩ := h2 h4
        use j
        exact hj.symm
      apply Classical.skolem.mp h3
    obtain ⟨f, hf ⟩ := h2
    have h31 : Function.Injective f := by
      intro k1 k2 h2
      apply h1.1.1
      rw [hf k1, hf k2, h2]
    have h3 : StrictMono f := by
      apply Monotone.strictMono_of_injective _ h31
      intro k1 k2 h2
      rw [monotone_2_of_simplex SC J hs]
      rw [← hf k1, ← hf k2]
      rwa [←monotone_2_of_simplex SC I h1.1]
    obtain ⟨j, hj⟩ := is_insert_index_of_strict_mono SC f h3
    use j
    ext k
    unfold delete_vertex
    rw [hf k, hj]
  · intro h1
    obtain ⟨ i, hi⟩ := h1
    rw [hi]
    apply @delete_vertex_is_face SC _ _ J hs

end Sol_Plasticity_Ext_Brouwer_facets

theorem solution (SC : CubicalSperner.SpernerCube) {n1 : ℕ} (hn1 : n1 + 1 = SC.n)
    (I : Fin (n1 + 1) → SC.G) (J : Fin (SC.n + 1) → SC.G) (hJ : CubicalSperner.simplex SC SC.n J) :
    CubicalSperner.is_face SC I J ↔ ∃ i, I = @CubicalSperner.delete_vertex SC n1 hn1 i J :=
  @Sol_Plasticity_Ext_Brouwer_facets.child_simplex_char SC n1 hn1 I J hJ
