-- Prove2me | solution 1 for QCircMITM.Search.generation
-- status  : ACCEPTED   (prove)
-- author  : @Ethan Cheung
-- created : 2026-10-21T16:40:23.537609+00:00
-- url     : https://prove2.me/submissions/c5e0f22e-76f5-4db7-b1c6-f4d61b269013

import Mathlib
import Definitions.Def_QCircMITM_Search_Algorithm

open QCircMITM.Search

theorem qc_mem_circuits {n : ℕ} (V : Finset (Unitary n)) (i : ℕ) (c : List (Unitary n)) :
    c ∈ circuits V i ↔ c.length = i ∧ ∀ W ∈ c, W ∈ V := by
  induction i generalizing c with
  | zero =>
    simp only [circuits, Finset.mem_singleton]
    constructor
    · rintro rfl; simp
    · rintro ⟨h, -⟩; exact List.length_eq_zero_iff.1 h
  | succ i ih =>
    simp only [circuits, Finset.mem_image, Finset.mem_product]
    constructor
    · rintro ⟨⟨W, c'⟩, ⟨hW, hc'⟩, rfl⟩
      rw [ih] at hc'
      refine ⟨by simp [hc'.1], ?_⟩
      intro X hX
      rcases List.mem_cons.1 hX with rfl | hX
      · exact hW
      · exact hc'.2 X hX
    · rintro ⟨hlen, hall⟩
      cases c with
      | nil => simp at hlen
      | cons W c' =>
        refine ⟨⟨W, c'⟩, ⟨hall W (List.mem_cons_self), ?_⟩, rfl⟩
        rw [ih]
        exact ⟨by simpa using hlen, fun X hX => hall X (List.mem_cons_of_mem _ hX)⟩

theorem qc_S_eq {n : ℕ} (V : Finset (Unitary n)) (i : ℕ) :
    S V i = (circuits V i).image List.prod := by
  induction i with
  | zero => simp [S, circuits]
  | succ i ih =>
    ext U
    simp only [S, circuits, ih, Finset.mem_image, Finset.mem_product, Prod.exists]
    constructor
    · rintro ⟨W, X, ⟨hW, c, hc, rfl⟩, rfl⟩
      exact ⟨W :: c, ⟨W, c, ⟨hW, hc⟩, rfl⟩, by simp⟩
    · rintro ⟨_, ⟨W, c, ⟨hW, hc⟩, rfl⟩, rfl⟩
      exact ⟨W, c.prod, ⟨hW, c, hc, rfl⟩, by simp⟩

theorem qc_mem_S {n : ℕ} (V : Finset (Unitary n)) (i : ℕ) (U : Unitary n) :
    U ∈ S V i ↔ ∃ c : List (Unitary n), c.length = i ∧ (∀ W ∈ c, W ∈ V) ∧ c.prod = U := by
  rw [qc_S_eq, Finset.mem_image]
  constructor
  · rintro ⟨c, hc, rfl⟩
    rw [qc_mem_circuits] at hc
    exact ⟨c, hc.1, hc.2, rfl⟩
  · rintro ⟨c, h1, h2, rfl⟩
    exact ⟨c, (qc_mem_circuits V i c).2 ⟨h1, h2⟩, rfl⟩

theorem qc_split {n : ℕ} (V : Finset (Unitary n)) (p q : ℕ) (U : Unitary n) :
    (∃ a ∈ circuits V p, ∃ b ∈ circuits V q, a.prod⁻¹ * U = b.prod) ↔ U ∈ S V (p + q) := by
  rw [qc_mem_S]
  constructor
  · rintro ⟨a, ha, b, hb, hab⟩
    rw [qc_mem_circuits] at ha hb
    refine ⟨a ++ b, by simp [ha.1, hb.1], ?_, ?_⟩
    · intro W hW
      rcases List.mem_append.1 hW with h | h
      · exact ha.2 W h
      · exact hb.2 W h
    · rw [List.prod_append, ← hab, mul_inv_cancel_left]
  · rintro ⟨c, hlen, hall, rfl⟩
    refine ⟨c.take p, ?_, c.drop p, ?_, ?_⟩
    · rw [qc_mem_circuits]
      exact ⟨by simp [hlen], fun W hW => hall W (List.mem_of_mem_take hW)⟩
    · rw [qc_mem_circuits]
      exact ⟨by simp [hlen], fun W hW => hall W (List.mem_of_mem_drop hW)⟩
    · rw [inv_mul_eq_iff_eq_mul, ← List.prod_append, List.take_append_drop]
theorem solution {n : ℕ} (V : Finset (Unitary n)) (i : ℕ) :
    (∀ c : List (Unitary n), c ∈ circuits V i ↔ c.length = i ∧ ∀ W ∈ c, W ∈ V) ∧
      S V i = (circuits V i).image List.prod :=
  ⟨qc_mem_circuits V i, qc_S_eq V i⟩
