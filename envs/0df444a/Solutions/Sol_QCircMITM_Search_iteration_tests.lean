-- Prove2me | solution 1 for QCircMITM.Search.iteration_tests
-- status  : ACCEPTED   (prove)
-- author  : @Ethan Cheung
-- created : 2026-10-21T16:40:28.297503+00:00
-- url     : https://prove2.me/submissions/a7fd9862-dfbd-4146-bdae-1e9a180d41c7

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
theorem qc_iteration_tests {n : ℕ} (V : Finset (Unitary n)) (U : Unitary n) (i : ℕ) (hi : 1 ≤ i) :
    (mitmStep V U i = none ↔ U ∉ S V (2 * i - 1) ∧ U ∉ S V (2 * i)) ∧
    ∀ c, mitmStep V U i = some c →
      (∀ W ∈ c, W ∈ V) ∧ c.prod = U ∧
      (U ∈ S V (2 * i - 1) → c.length = 2 * i - 1) ∧
      (U ∉ S V (2 * i - 1) → c.length = 2 * i) := by
  have e1 := qc_split V (i - 1) i U
  have e2 := qc_split V i i U
  rw [show i - 1 + i = 2 * i - 1 by omega] at e1
  rw [show i + i = 2 * i by omega] at e2
  -- generic fact about a chosen pair
  have gen : ∀ p q (h : ∃ a ∈ circuits V p, ∃ b ∈ circuits V q, a.prod⁻¹ * U = b.prod),
      let c := Classical.choose h ++ Classical.choose (Classical.choose_spec h).2
      (∀ W ∈ c, W ∈ V) ∧ c.prod = U ∧ c.length = p + q := by
    intro p q h
    obtain ⟨ha, hrest⟩ := Classical.choose_spec h
    obtain ⟨hb, hab⟩ := Classical.choose_spec hrest
    rw [qc_mem_circuits] at ha hb
    refine ⟨?_, ?_, ?_⟩
    · intro W hW
      rcases List.mem_append.1 hW with h' | h'
      · exact ha.2 W h'
      · exact hb.2 W h'
    · rw [List.prod_append, ← hab, mul_inv_cancel_left]
    · rw [List.length_append, ha.1, hb.1]
  constructor
  · unfold mitmStep
    split_ifs with h1 h2
    · simp only [reduceCtorEq, false_iff, not_and, not_not]
      intro h; exact absurd (e1.1 h1) h
    · simp only [reduceCtorEq, false_iff, not_and, not_not]
      intro _; exact e2.1 h2
    · simp only [true_iff]
      exact ⟨fun h => h1 (e1.2 h), fun h => h2 (e2.2 h)⟩
  · intro c hc
    unfold mitmStep at hc
    split_ifs at hc with h1 h2
    · obtain ⟨g1, g2, g3⟩ := gen _ _ h1
      simp only [Option.some.injEq] at hc
      subst hc
      refine ⟨g1, g2, fun _ => by rw [g3]; omega, fun h => absurd (e1.1 h1) h⟩
    · obtain ⟨g1, g2, g3⟩ := gen _ _ h2
      simp only [Option.some.injEq] at hc
      subst hc
      refine ⟨g1, g2, fun h => absurd (e1.2 h) h1, fun _ => by rw [g3]; omega⟩
theorem solution {n : ℕ} (V : Finset (Unitary n)) (U : Unitary n) (i : ℕ) (hi : 1 ≤ i) :
    (mitmStep V U i = none ↔ U ∉ S V (2 * i - 1) ∧ U ∉ S V (2 * i)) ∧
    ∀ c, mitmStep V U i = some c →
      (∀ W ∈ c, W ∈ V) ∧ c.prod = U ∧
      (U ∈ S V (2 * i - 1) → c.length = 2 * i - 1) ∧
      (U ∉ S V (2 * i - 1) → c.length = 2 * i) :=
  qc_iteration_tests V U i hi
