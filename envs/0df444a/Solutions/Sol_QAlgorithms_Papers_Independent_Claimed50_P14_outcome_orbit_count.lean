-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Claimed50.P14.outcome_orbit_count
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-20T11:23:40.291857+00:00
-- url     : https://prove2.me/submissions/0c7517f9-1e4e-4068-b37e-1a5b605ac794

import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P14
noncomputable section

open MeasureTheory TopologicalSpace

open scoped BigOperators Matrix ComplexConjugate ComplexOrder Matrix.Norms.Elementwise

attribute [local instance] Classical.decEq Classical.propDecidable

open QAlgorithms.Papers.Independent.Claimed50.P14

attribute [local instance] QAlgorithms.Papers.Independent.Claimed50.P14.learningMatrixContinuousENorm

theorem g58d_orbit_iff {d M : ℕ} (x y : Fin M → Fin d) :
    (∃ σ : Equiv.Perm (Fin d), y = σ ∘ x) ↔ ∀ a b, (x a = x b ↔ y a = y b) := by
  constructor
  · rintro ⟨σ, rfl⟩ a b
    simp
  · intro h
    let f : {v // v ∈ Set.range x} → {v // v ∈ Set.range y} :=
      fun v => ⟨y (Classical.choose v.2), ⟨_, rfl⟩⟩
    have hf : ∀ a, f ⟨x a, ⟨a, rfl⟩⟩ = ⟨y a, ⟨a, rfl⟩⟩ := by
      intro a
      apply Subtype.ext
      show y (Classical.choose (⟨a, rfl⟩ : x a ∈ Set.range x)) = y a
      exact (h _ _).mp (Classical.choose_spec (⟨a, rfl⟩ : x a ∈ Set.range x))
    have hbij : Function.Bijective f := by
      constructor
      · rintro ⟨_, ⟨a, rfl⟩⟩ ⟨_, ⟨b, rfl⟩⟩ hab
        rw [hf, hf] at hab
        apply Subtype.ext
        exact (h a b).mpr (congrArg Subtype.val hab)
      · rintro ⟨_, ⟨a, rfl⟩⟩
        exact ⟨⟨x a, ⟨a, rfl⟩⟩, hf a⟩
    let e := Equiv.ofBijective f hbij
    refine ⟨e.extendSubtype, ?_⟩
    funext a
    simp only [Function.comp]
    rw [Equiv.extendSubtype_apply_of_mem e (x a) ⟨a, rfl⟩]
    show y a = (f ⟨x a, ⟨a, rfl⟩⟩).val
    rw [hf]

theorem solution (d N : ℕ) (hd : 1 ≤ d) (hN : 1 ≤ N) :
    (∀ x y : Labels d (N+1), (outcomeOrbit d N).r x y ↔
      ∀ a b, (x a = x b ↔ y a = y b)) ∧
    Nat.card (Quotient (outcomeOrbit d N)) = Nat.card (BoundedPartitions d N) := by
  have part1 : ∀ x y : Labels d (N+1), (outcomeOrbit d N).r x y ↔ ∀ a b, (x a = x b ↔ y a = y b) :=
    fun x y => g58d_orbit_iff x y
  refine ⟨part1, ?_⟩
  have hcard : ∀ x : Labels d (N+1), Nat.card (Quotient (Setoid.ker x)) ≤ d := by
    intro x
    have := Nat.card_le_card_of_injective _ (Setoid.kerLift_injective x)
    simpa using this
  let F : Quotient (outcomeOrbit d N) → BoundedPartitions d N :=
    Quotient.lift (fun x => (⟨Setoid.ker x, hcard x⟩ : BoundedPartitions d N)) (by
      intro x y hxy
      apply Subtype.ext
      ext a b
      simp only [Setoid.ker_def]
      exact (part1 x y).mp hxy a b)
  have hinj : Function.Injective F := by
    intro q1 q2 h
    induction q1 using Quotient.inductionOn with | h x => ?_
    induction q2 using Quotient.inductionOn with | h y => ?_
    apply Quotient.sound
    have h' : Setoid.ker x = Setoid.ker y := congrArg Subtype.val h
    refine (part1 x y).mpr (fun a b => ?_)
    have := congrArg (fun s : Setoid (Fin (N+1)) => s.r a b) h'
    simpa [Setoid.ker_def] using this
  have hsurj : Function.Surjective F := by
    rintro ⟨s, hs⟩
    letI : Fintype (Quotient s) := Fintype.ofFinite _
    have hle : Fintype.card (Quotient s) ≤ Fintype.card (Fin d) := by
      rw [Fintype.card_fin, ← Nat.card_eq_fintype_card]; exact hs
    obtain ⟨g⟩ := Function.Embedding.nonempty_of_card_le hle
    refine ⟨Quotient.mk _ (fun a => g (Quotient.mk s a)), ?_⟩
    apply Subtype.ext
    change Setoid.ker (fun a => g (Quotient.mk s a)) = s
    ext a b
    simp only [Setoid.ker_def]
    rw [g.injective.eq_iff, Quotient.eq]
  exact Nat.card_congr (Equiv.ofBijective F ⟨hinj, hsurj⟩)
