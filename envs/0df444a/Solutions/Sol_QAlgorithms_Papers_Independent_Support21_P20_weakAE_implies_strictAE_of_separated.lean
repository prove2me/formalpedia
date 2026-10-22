-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Support21.P20.weakAE_implies_strictAE_of_separated
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-21T07:14:09.872115+00:00
-- url     : https://prove2.me/submissions/59462162-269f-4253-9816-813344077dec

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

theorem g67c_weak_strict {X Y : Type u} (E : Enhanced X) (F : Enhanced Y)
    (hF : IsCountablySeparated F) (f g : Premap E F) (h : WeakAE E F f.val g.val) :
    StrictAE E f.val g.val := by
  obtain ⟨S, hSc, hSm, hsep, hcov⟩ := hF
  have hN := g67c_countable E S hSc
    (fun s => (partialPreimage f.val s \ partialPreimage g.val s) ∪
      (partialPreimage g.val s \ partialPreimage f.val s)) (fun s hs => h s (hSm hs))
  refine g67c_mono E ?_ hN
  intro x hx
  simp only [Set.mem_iUnion]
  have key : ∀ (a b : Option Y), a = f.val x → b = g.val x → a ≠ b →
      ∃ s ∈ S, x ∈ (partialPreimage f.val s \ partialPreimage g.val s) ∪
        (partialPreimage g.val s \ partialPreimage f.val s) := by
    intro a b ha hb hab
    have nf : ∀ s y, f.val x = some y → y ∈ s → x ∈ partialPreimage f.val s :=
      fun s y h1 h2 => ⟨y, h2, h1⟩
    have nf' : ∀ s y, f.val x = some y → y ∉ s → x ∉ partialPreimage f.val s := by
      rintro s y h1 h2 ⟨y', hy', h3⟩; rw [h1] at h3; cases h3; exact h2 hy'
    have nfn : ∀ s, f.val x = none → x ∉ partialPreimage f.val s := by
      rintro s h1 ⟨y', hy', h3⟩; rw [h1] at h3; cases h3
    have ng : ∀ s y, g.val x = some y → y ∈ s → x ∈ partialPreimage g.val s :=
      fun s y h1 h2 => ⟨y, h2, h1⟩
    have ng' : ∀ s y, g.val x = some y → y ∉ s → x ∉ partialPreimage g.val s := by
      rintro s y h1 h2 ⟨y', hy', h3⟩; rw [h1] at h3; cases h3; exact h2 hy'
    have ngn : ∀ s, g.val x = none → x ∉ partialPreimage g.val s := by
      rintro s h1 ⟨y', hy', h3⟩; rw [h1] at h3; cases h3
    cases a with
    | none =>
      cases b with
      | none => exact absurd rfl hab
      | some y =>
        obtain ⟨s, hs, hys⟩ := hcov y
        exact ⟨s, hs, Or.inr ⟨ng s y hb.symm hys, nfn s ha.symm⟩⟩
    | some y =>
      cases b with
      | none =>
        obtain ⟨s, hs, hys⟩ := hcov y
        exact ⟨s, hs, Or.inl ⟨nf s y ha.symm hys, ngn s hb.symm⟩⟩
      | some y' =>
        have hne : y ≠ y' := fun e => hab (by rw [e])
        obtain ⟨s, hs, h1, h2⟩ := hsep y y' hne
        exact ⟨s, hs, Or.inl ⟨nf s y ha.symm h1, ng' s y' hb.symm h2⟩⟩
  obtain ⟨s, hs, hm⟩ := key _ _ rfl rfl hx
  exact ⟨s, hs, hm⟩

theorem solution (X Y : Type u)
    (E : Enhanced X) (F : Enhanced Y) (hF : IsCountablySeparated F) :
    (∀ f g : Premap E F, WeakAE E F f.val g.val → StrictAE E f.val g.val) ∧
    ∃ q : Quot (strictHomRelation E F) → Quot (weakHomRelation E F),
      Function.Bijective q ∧ ∀ f : Premap E F,
        q (Quot.mk (strictHomRelation E F) f) = Quot.mk (weakHomRelation E F) f := by
  refine ⟨g67c_weak_strict E F hF, ?_⟩
  refine ⟨Quot.lift (fun f => Quot.mk (weakHomRelation E F) f)
    (fun f g h => Quot.sound (g67c_strict_weak E F f g h)), ⟨?_, ?_⟩, fun f => rfl⟩
  · intro a b hab
    induction a using Quot.ind with
    | mk f =>
      induction b using Quot.ind with
      | mk g =>
        have h1 : Quot.mk (weakHomRelation E F) f = Quot.mk (weakHomRelation E F) g := hab
        have h2 := (Equivalence.eqvGen_iff (g67c_weak_equiv E F)).1 (Quot.eqvGen_exact h1)
        exact Quot.sound (g67c_weak_strict E F hF f g h2)
  · intro y
    induction y using Quot.ind with
    | mk f => exact ⟨Quot.mk _ f, rfl⟩
