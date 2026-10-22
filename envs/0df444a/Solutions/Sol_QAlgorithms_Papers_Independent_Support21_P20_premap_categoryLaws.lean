-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Support21.P20.premap_categoryLaws
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-21T07:12:21.422609+00:00
-- url     : https://prove2.me/submissions/f96028c2-ffb4-43ab-b349-0847e8d5b2cf

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

theorem solution :
    (∀ (X : Type u) (E : Enhanced X), IsPremap E E (fun x => some x)) ∧
    (∀ (X Y Z : Type u) (E : Enhanced X) (F : Enhanced Y) (G : Enhanced Z)
      (f : Premap E F) (g : Premap F G),
      IsPremap E G (partialCompose g.val f.val) ∧
      partialDomain (partialCompose g.val f.val) =
        partialDomain f.val ∩ partialPreimage f.val (partialDomain g.val)) ∧
    (∀ (X Y Z W : Type u) (E : Enhanced X) (F : Enhanced Y)
      (G : Enhanced Z) (H : Enhanced W)
      (f : Premap E F) (g : Premap F G) (h : Premap G H),
      partialCompose h.val (partialCompose g.val f.val) =
        partialCompose (partialCompose h.val g.val) f.val) ∧
    (∀ (X Y : Type u) (E : Enhanced X) (F : Enhanced Y) (f : Premap E F),
      partialCompose (fun y => some y) f.val = f.val ∧
      partialCompose f.val (fun x => some x) = f.val) := by
  have hid : ∀ {X : Type u} (s : Set X), partialPreimage (fun x : X => some x) s = s := by
    intro X s; ext x; simp [partialPreimage]
  have hdom : ∀ {X Y Z : Type u} (g : Y → Option Z) (f : X → Option Y),
      partialDomain (partialCompose g f) = partialDomain f ∩ partialPreimage f (partialDomain g) := by
    intro X Y Z g f
    ext x
    simp only [partialDomain, partialPreimage, partialCompose, Set.mem_inter_iff, Set.mem_setOf_eq]
    constructor
    · rintro ⟨z, hz⟩
      cases hfx : f x with
      | none => simp [hfx] at hz
      | some y => rw [hfx] at hz; exact ⟨⟨y, rfl⟩, y, ⟨z, hz⟩, rfl⟩
    · rintro ⟨_, y, ⟨z, hz⟩, hf⟩
      exact ⟨z, by rw [hf]; simpa using hz⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro X E
    refine ⟨?_, ?_, ?_⟩
    · have : (partialDomain (fun x : X => some x))ᶜ = ∅ := by
        ext x; simp [partialDomain]
      rw [this]; exact g67c_empty E
    · intro s hs; rw [hid]; exact hs
    · intro s hs; rw [hid]; exact hs
  · intro X Y Z E F G f g
    refine ⟨⟨?_, ?_, ?_⟩, hdom _ _⟩
    · rw [hdom, Set.compl_inter]
      refine g67c_union E f.2.1 ?_
      refine g67c_mono E ?_ (g67c_union E f.2.1 (g67c_pre_neg f g.2.1))
      intro x hx
      cases hfx : f.val x with
      | none => left; rintro ⟨y, hy⟩; rw [hfx] at hy; cases hy
      | some y =>
        right
        refine ⟨y, ?_, hfx⟩
        intro hy
        exact hx ⟨y, hy, hfx⟩
    · intro s hs; rw [g67c_pre_comp]; exact g67c_pre_meas f (g67c_pre_meas g hs)
    · intro s hs; rw [g67c_pre_comp]; exact g67c_pre_neg f (g67c_pre_neg g hs)
  · intro X Y Z W E F G H f g h
    funext x
    simp only [partialCompose]
    cases f.val x <;> rfl
  · intro X Y E F f
    constructor
    · funext x; simp only [partialCompose]; cases f.val x <;> rfl
    · funext x; rfl
