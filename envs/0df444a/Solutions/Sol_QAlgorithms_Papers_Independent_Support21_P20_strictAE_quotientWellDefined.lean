-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Support21.P20.strictAE_quotientWellDefined
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-21T07:13:04.057117+00:00
-- url     : https://prove2.me/submissions/7781f0e9-9662-4dbc-8093-314c717d5431

import Definitions.Def_QAlgorithms_Papers_Independent_Support21_P20

open QAlgorithms.Papers.Independent.Support21.P20

open Set Filter

open scoped NNReal

universe u v

theorem g67c_union {X : Type u} (E : Enhanced X) {a b : Set X}
    (ha : a ∈ E.negligible) (hb : b ∈ E.negligible) : a ∪ b ∈ E.negligible := by
  have h := E.sigmaIdeal.2.2 (fun n => if n = 0 then a else b) (by
    intro i; by_cases h : i = 0 <;> simp [h, ha, hb])
  have : (⋃ i, (fun n => if n = 0 then a else b) i) = a ∪ b := by
    ext x; simp only [mem_iUnion, mem_union]
    constructor
    · rintro ⟨i, hi⟩; by_cases h : i = 0 <;> simp_all
    · rintro (h | h)
      · exact ⟨0, by simpa using h⟩
      · exact ⟨1, by simpa using h⟩
  rw [this] at h; exact h

theorem g67c_mono {X : Type u} (E : Enhanced X) {a b : Set X}
    (hab : a ⊆ b) (hb : b ∈ E.negligible) : a ∈ E.negligible :=
  E.sigmaIdeal.2.1 a b hab hb

theorem g67c_empty {X : Type u} (E : Enhanced X) : (∅ : Set X) ∈ E.negligible :=
  E.sigmaIdeal.1

theorem g67c_countable {X : Type u} (E : Enhanced X) {ι : Type*} (S : Set ι)
    (hS : S.Countable) (N : ι → Set X) (hN : ∀ s ∈ S, N s ∈ E.negligible) :
    (⋃ s ∈ S, N s) ∈ E.negligible := by
  rcases S.eq_empty_or_nonempty with h | h
  · subst h; simpa using g67c_empty E
  obtain ⟨e, he⟩ := hS.exists_eq_range h
  have h2 := E.sigmaIdeal.2.2 (fun n => N (e n)) (fun n => hN _ (by rw [he]; exact ⟨n, rfl⟩))
  have : (⋃ s ∈ S, N s) = ⋃ n, N (e n) := by
    rw [he]; ext x; simp
  rw [this]; exact h2

theorem g67c_pre_comp {X Y Z : Type*} (g : Y → Option Z) (f : X → Option Y) (s : Set Z) :
    partialPreimage (partialCompose g f) s = partialPreimage f (partialPreimage g s) := by
  ext x
  simp only [partialPreimage, partialCompose, mem_setOf_eq]
  constructor
  · rintro ⟨z, hz, h⟩
    cases hfx : f x with
    | none => simp [hfx] at h
    | some y => rw [hfx] at h; exact ⟨y, ⟨z, hz, h⟩, rfl⟩
  · rintro ⟨y, ⟨z, hz, h⟩, hf⟩
    exact ⟨z, hz, by rw [hf]; simpa using h⟩

theorem g67c_pre_diff {X Y : Type*} (f : X → Option Y) (s t : Set Y) :
    partialPreimage f s \ partialPreimage f t = partialPreimage f (s \ t) := by
  ext x
  simp only [partialPreimage, mem_diff, mem_setOf_eq, not_exists, not_and]
  constructor
  · rintro ⟨⟨y, hy, h⟩, h2⟩
    exact ⟨y, ⟨hy, fun ht => h2 y ht h⟩, h⟩
  · rintro ⟨y, ⟨hy, hyt⟩, h⟩
    refine ⟨⟨y, hy, h⟩, fun y' hy' h' => ?_⟩
    rw [h] at h'; cases h'; exact hyt hy'

theorem g67c_pre_neg {X Y : Type u} {E : Enhanced X} {F : Enhanced Y} (f : Premap E F)
    {s : Set Y} (hs : s ∈ F.negligible) : partialPreimage f.val s ∈ E.negligible :=
  f.2.2.2 s hs

theorem g67c_pre_meas {X Y : Type u} {E : Enhanced X} {F : Enhanced Y} (f : Premap E F)
    {s : Set Y} (hs : s ∈ F.measurable) : partialPreimage f.val s ∈ E.measurable :=
  f.2.2.1 s hs

theorem g67c_meas_diff {X : Type u} (E : Enhanced X) {a b : Set X}
    (ha : a ∈ E.measurable) (hb : b ∈ E.measurable) : a \ b ∈ E.measurable := by
  -- a \ b = (aᶜ ∪ b)ᶜ
  have hc := E.sigmaAlgebra.2.1
  have hu := E.sigmaAlgebra.2.2 (fun n => if n = 0 then aᶜ else b) (by
    intro i; by_cases h : i = 0 <;> simp [h, hc a ha, hb])
  have : (⋃ i, (fun n => if n = 0 then aᶜ else b) i) = aᶜ ∪ b := by
    ext x; simp only [mem_iUnion, mem_union]
    constructor
    · rintro ⟨i, hi⟩; by_cases h : i = 0 <;> simp_all
    · rintro (h | h)
      · exact ⟨0, by simpa using h⟩
      · exact ⟨1, by simpa using h⟩
  rw [this] at hu
  have := hc _ hu
  rw [compl_union, compl_compl] at this
  rw [Set.diff_eq]; exact this

theorem g67c_weak_equiv {X Y : Type u} (E : Enhanced X) (F : Enhanced Y) :
    Equivalence (weakHomRelation E F) := by
  refine ⟨fun f => ?_, fun {f g} h => ?_, fun {f g k} h1 h2 => ?_⟩
  · intro s hs; simpa using g67c_empty E
  · intro s hs; rw [union_comm]; exact h s hs
  · intro s hs
    refine g67c_mono E ?_ (g67c_union E (h1 s hs) (h2 s hs))
    intro x hx
    by_cases hg : x ∈ partialPreimage g.val s
    · rcases hx with ⟨h, h'⟩ | ⟨h, h'⟩
      · exact Or.inr (Or.inl ⟨hg, h'⟩)
      · exact Or.inl (Or.inr ⟨hg, h'⟩)
    · rcases hx with ⟨h, h'⟩ | ⟨h, h'⟩
      · exact Or.inl (Or.inl ⟨h, hg⟩)
      · exact Or.inr (Or.inr ⟨h, hg⟩)

theorem g67c_strict_equiv {X Y : Type u} (E : Enhanced X) (F : Enhanced Y) :
    Equivalence (strictHomRelation E F) := by
  refine ⟨fun f => ?_, fun {f g} h => ?_, fun {f g k} h1 h2 => ?_⟩
  · show {x | f.val x ≠ f.val x} ∈ E.negligible
    simpa using g67c_empty E
  · show {x | g.val x ≠ f.val x} ∈ E.negligible
    have : {x | g.val x ≠ f.val x} = {x | f.val x ≠ g.val x} := by
      ext x; simp [ne_comm]
    rw [this]; exact h
  · show {x | f.val x ≠ k.val x} ∈ E.negligible
    refine g67c_mono E ?_ (g67c_union E h1 h2)
    intro x hx
    by_cases h : f.val x = g.val x
    · right; show g.val x ≠ k.val x; rw [← h]; exact hx
    · left; exact h

theorem g67c_strict_weak {X Y : Type u} (E : Enhanced X) (F : Enhanced Y)
    (f g : Premap E F) (h : StrictAE E f.val g.val) : WeakAE E F f.val g.val := by
  intro s hs
  refine g67c_mono E ?_ h
  intro x hx
  show f.val x ≠ g.val x
  intro heq
  rcases hx with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact h2 (by simpa [partialPreimage, heq] using h1)
  · exact h2 (by simpa [partialPreimage, heq] using h1)

theorem solution (X Y Z : Type u)
    (E : Enhanced X) (F : Enhanced Y) (G : Enhanced Z) :
    Equivalence (strictHomRelation E F) ∧
    ∀ (f g : Premap E F) (h k : Premap F G),
      StrictAE E f.val g.val → StrictAE F h.val k.val →
      StrictAE E (partialCompose h.val f.val) (partialCompose k.val g.val) := by
  refine ⟨g67c_strict_equiv E F, ?_⟩
  intro f g h k hfg hhk
  refine g67c_mono E ?_ (g67c_union E hfg (g67c_pre_neg f hhk))
  intro x hx
  by_cases he : f.val x = g.val x
  · right
    simp only [partialCompose, Set.mem_setOf_eq] at hx
    cases hfx : f.val x with
    | none => rw [← he, hfx] at hx; exact absurd rfl hx
    | some y =>
      refine ⟨y, ?_, hfx⟩
      show h.val y ≠ k.val y
      rw [← he, hfx] at hx; simpa using hx
  · left; exact he
