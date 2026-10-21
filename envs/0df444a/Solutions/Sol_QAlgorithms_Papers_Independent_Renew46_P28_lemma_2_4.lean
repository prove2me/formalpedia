-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Renew46.P28.lemma_2_4
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-21T04:01:48.606863+00:00
-- url     : https://prove2.me/submissions/e385d8a9-9f7f-4405-9c4c-69aac15ceed8

import Definitions.Def_QAlgorithms_Papers_Independent_Renew46_P28
open QAlgorithms.Papers.Independent.Renew46.P28

open Set

open scoped TensorProduct

universe u v w

/-- Lemma 2.4, PDF p.17: a unital subalgebra of a finite-dimensional unital
associative algebra has exactly the ambient units which lie in it. -/
theorem solution
    (K : Type u) [Field K] [TopologicalSpace K] [T2Space K]
    [IsTopologicalDivisionRing K] (hK : ¬ DiscreteTopology K)
    (A : Type v) [Ring A] [Algebra K A] [FiniteDimensional K A]
    (B : Subalgebra K A) :
    (Subtype.val '' {b : B | IsUnit b} : Set A) =
      {a : A | IsUnit a} ∩ (B : Set A) := by
  ext a
  constructor
  · rintro ⟨b, hb, rfl⟩
    exact ⟨(show IsUnit b from hb).map B.val, b.2⟩
  · rintro ⟨ha, haB⟩
    have ha' : IsUnit a := ha
    let b : B := ⟨a, haB⟩
    have hinj : Function.Injective (LinearMap.mulLeft K b) := by
      intro x y h
      apply Subtype.ext
      have h' := congrArg Subtype.val h
      simp only [LinearMap.mulLeft_apply, Subalgebra.coe_mul] at h'
      exact ha'.mul_left_cancel h'
    obtain ⟨c, hc⟩ := (LinearMap.injective_iff_surjective.mp hinj) 1
    simp only [LinearMap.mulLeft_apply] at hc
    have hc' : a * (c : A) = 1 := by
      have := congrArg Subtype.val hc; simpa [b] using this
    obtain ⟨u, hu⟩ := ha'
    have hcu : (c : A) = (u⁻¹ : Aˣ) := by
      calc (c : A) = (u⁻¹ : Aˣ) * (a * c) := by rw [← hu, ← mul_assoc, Units.inv_mul, one_mul]
        _ = (u⁻¹ : Aˣ) := by rw [hc', mul_one]
    have hcb : c * b = 1 := by
      apply Subtype.ext
      simp only [Subalgebra.coe_mul, Subalgebra.coe_one]
      show (c : A) * a = 1
      rw [hcu, ← hu, Units.inv_mul]
    exact ⟨b, ⟨⟨b, c, hc, hcb⟩, rfl⟩, rfl⟩


