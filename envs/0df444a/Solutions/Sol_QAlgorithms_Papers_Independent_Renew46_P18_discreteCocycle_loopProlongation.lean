-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Renew46.P18.discreteCocycle_loopProlongation
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-21T00:18:22.80506+00:00
-- url     : https://prove2.me/submissions/fc80e1ee-25fd-4295-8881-6bbc3cce6234

import Definitions.Def_QAlgorithms_Papers_Independent_Renew46_P18
open QAlgorithms.Papers.Independent.Renew46.P18

universe u v w x

theorem solution
    {H : Type u} {Z : Type v} [Group H] [AddCommGroup Z]
    (A : AddSubgroup Z) (F : H → H → Z) (theta : H → H → H → A)
    (h : IsDiscreteGeneralisedCocycle A F theta) :
    IsLoopProlongation (twistedMul F) (0, 1)
      (twistedMul (quotientCocycle A F)) (0, 1)
      (twistedRightInverse (quotientCocycle A F))
      (twistedProjection A) (coefficientInclusion A) (inflatedTheta A theta) := by
  obtain ⟨hF1, hF2, ⟨ht1, ht2, ht3, htc⟩, hcoc⟩ := h
  -- cocycle identity in the quotient
  have hq : ∀ g k l : H, quotientCocycle A F k l - quotientCocycle A F (g * k) l +
      quotientCocycle A F g (k * l) - quotientCocycle A F g k = 0 := by
    intro g k l
    simp only [quotientCocycle, ← map_sub, ← map_add, hcoc]
    exact (QuotientAddGroup.eq_zero_iff _).2 (theta g k l).2
  have hq1 : ∀ g, quotientCocycle A F 1 g = 0 := by intro g; simp [quotientCocycle, hF1]
  have hq2 : ∀ g, quotientCocycle A F g 1 = 0 := by intro g; simp [quotientCocycle, hF2]
  refine ⟨⟨?_, ?_, ?_, ?_⟩, ⟨?_, ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  -- loop
  · intro a; ext <;> simp [twistedMul, hF1]
  · intro a; ext <;> simp [twistedMul, hF2]
  · intro a
    constructor
    · intro b c hbc
      simp only [twistedMul, Prod.mk.injEq] at hbc
      have h2 : b.2 = c.2 := mul_left_cancel hbc.2
      have h1 : b.1 = c.1 := by
        have := hbc.1; rw [h2] at this; simpa using this
      exact Prod.ext h1 h2
    · intro y
      refine ⟨(y.1 - a.1 - F a.2 (a.2⁻¹ * y.2), a.2⁻¹ * y.2), ?_⟩
      ext
      · simp only [twistedMul]; abel
      · simp [twistedMul]
  · intro a
    constructor
    · intro b c hbc
      simp only [twistedMul, Prod.mk.injEq] at hbc
      have h2 : b.2 = c.2 := mul_right_cancel hbc.2
      have h1 : b.1 = c.1 := by
        have := hbc.1; rw [h2] at this; simpa using this
      exact Prod.ext h1 h2
    · intro y
      refine ⟨(y.1 - a.1 - F (y.2 * a.2⁻¹) a.2, y.2 * a.2⁻¹), ?_⟩
      ext
      · simp only [twistedMul]; abel
      · simp [twistedMul]
  -- group
  · intro a; ext <;> simp [twistedMul, hq1]
  · intro a; ext <;> simp [twistedMul, hq2]
  · intro a b c
    ext
    · simp only [twistedMul]
      have := hq a.2 b.2 c.2
      rw [← sub_eq_zero, ← neg_eq_zero, ← this]; abel
    · simp [twistedMul, mul_assoc]
  · intro a
    ext
    · simp only [twistedRightInverse, twistedMul]
      have := hq a.2 a.2⁻¹ a.2
      rw [mul_inv_cancel, inv_mul_cancel, hq1, hq2] at this
      rw [← this]; abel
    · simp [twistedRightInverse, twistedMul]
  · intro a
    ext
    · simp only [twistedRightInverse, twistedMul]; abel
    · simp [twistedRightInverse, twistedMul]
  -- projection
  · intro y
    obtain ⟨z, hz⟩ := QuotientAddGroup.mk'_surjective A y.1
    exact ⟨(z, y.2), Prod.ext hz rfl⟩
  · simp [twistedProjection]
  · intro a b
    ext <;> simp [twistedProjection, twistedMul, quotientCocycle]
  -- inclusion
  · intro a b hab
    simp only [coefficientInclusion, Prod.mk.injEq] at hab
    exact Subtype.ext hab.1
  · simp [coefficientInclusion]
  · intro a b
    ext <;> simp [coefficientInclusion, twistedMul, hF1]
  · intro c
    ext
    · simp [coefficientInclusion, twistedProjection]
    · simp [coefficientInclusion, twistedProjection]
  -- associator
  · intro a b c
    ext
    · simp only [twistedMul, coefficientInclusion, inflatedTheta, twistedProjection, one_mul, hF1]
      have := hcoc a.2 b.2 c.2
      rw [← this]; abel
    · simp [twistedMul, coefficientInclusion, mul_assoc]
  · intro k a b hk
    have hk2 : k.2 = 1 := congrArg Prod.snd hk
    simp only [inflatedTheta, twistedProjection, hk2, ht1, ht2, ht3, coefficientInclusion]
    exact ⟨rfl, rfl, rfl⟩
  · intro k a b c _
    ext <;> simp [twistedMul, coefficientInclusion, hF1, hF2, add_comm]
  · intro a c
    ext <;> simp [twistedMul, coefficientInclusion, hF1, hF2, add_comm]
  · refine ⟨?_, ?_, ?_, ?_⟩
    · intro g k; simp [inflatedTheta, ht1]
    · intro g k; simp [inflatedTheta, ht2]
    · intro g k; simp [inflatedTheta, ht3]
    · intro g k l m
      simp only [inflatedTheta, twistedMul]
      exact htc _ _ _ _
