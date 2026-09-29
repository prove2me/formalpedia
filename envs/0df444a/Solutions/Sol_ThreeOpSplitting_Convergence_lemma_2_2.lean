-- Prove2me | solution 1 for ThreeOpSplitting.Convergence.lemma_2_2
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-28T16:59:13.912607+00:00
-- url     : https://prove2.me/submissions/1ae2116a-8c57-4a65-aa40-8a3642e8fae2

import Mathlib
import Definitions.Def_ThreeOpSplitting_Convergence_MonotoneOperators
import Definitions.Def_ThreeOpSplitting_Convergence_ThreeOperatorIteration

open InnerProductSpace

namespace ThreeOpSplitting.Convergence

/-- The resolvent of a monotone operator is determined: if `u ∈ A x` then `J (x + γ u) = x`. -/
lemma resolvent_eq {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (γ : ℝ) (A : H → Set H) (J : H → H) (hγ : 0 < γ) (hAm : IsMonotoneOp A)
    (hJ : IsResolvent γ A J) (x u : H) (hu : u ∈ A x) : J (x + γ • u) = x := by
  set y := J (x + γ • u) with hy
  have h1 := hJ (x + γ • u)
  rw [← hy] at h1
  have hm := hAm y x _ u h1 hu
  have e : γ⁻¹ • (x + γ • u - y) - u = γ⁻¹ • (x - y) := by
    rw [smul_sub, smul_add, smul_smul, inv_mul_cancel₀ hγ.ne', one_smul, smul_sub]; abel
  rw [e, real_inner_smul_right] at hm
  have h2 : 0 ≤ ⟪y - x, x - y⟫_ℝ := (mul_nonneg_iff_of_pos_left (inv_pos.2 hγ)).1 hm
  have e2 : x - y = -(y - x) := by abel
  rw [e2, inner_neg_right, real_inner_self_eq_norm_sq] at h2
  have : ‖y - x‖ = 0 := by nlinarith [norm_nonneg (y - x)]
  rw [norm_eq_zero, sub_eq_zero] at this
  exact this

theorem lemma_2_2 {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (A B : H → Set H) (C : H → H) (β γ : ℝ) (JA JB : H → H)
    (hA : IsMaximalMonotone A) (hB : IsMaximalMonotone B)
    (hβ : 0 < β) (hC : IsCocoercive β C) (hγ : 0 < γ)
    (hJA : IsResolvent γ A JA) (hJB : IsResolvent γ B JB) :
    zer (opSum A B C) = JB '' Function.fixedPoints (threeOp γ JA JB C) ∧
      Function.fixedPoints (threeOp γ JA JB C) =
        {z : H | ∃ x u : H, (0 : H) ∈ opSum A B C x ∧ u ∈ B x ∧
          (∃ a ∈ A x, u = -a - C x) ∧ z = x + γ • u} := by
  have hg : γ ≠ 0 := hγ.ne'
  -- fixed points from data
  have hfix_of : ∀ x u a : H, u ∈ B x → a ∈ A x → u = -a - C x →
      threeOp γ JA JB C (x + γ • u) = x + γ • u := by
    intro x u a hu ha hua
    have h1 : JB (x + γ • u) = x := resolvent_eq γ B JB hγ hB.1 hJB x u hu
    have h2 : (2 : ℝ) • JB (x + γ • u) - (x + γ • u) - γ • C (JB (x + γ • u)) = x + γ • a := by
      rw [h1, hua]; module
    have h3 : JA (x + γ • a) = x := resolvent_eq γ A JA hγ hA.1 hJA x a ha
    simp only [threeOp]
    rw [h2, h3, h1]; abel
  -- data from fixed points
  have hdata : ∀ z, threeOp γ JA JB C z = z →
      ∃ a ∈ A (JB z), γ⁻¹ • (z - JB z) ∈ B (JB z) ∧ γ⁻¹ • (z - JB z) = -a - C (JB z) ∧
        z = JB z + γ • (γ⁻¹ • (z - JB z)) := by
    intro z hz
    set x := JB z with hx
    set z'' := (2 : ℝ) • x - z - γ • C x with hz''
    have hxA : JA z'' = x := by
      have h : JA z'' + z - x = z := hz
      calc JA z'' = (JA z'' + z - x) - z + x := by abel
        _ = x := by rw [h]; abel
    refine ⟨γ⁻¹ • (z'' - x), ?_, hJB z, ?_, ?_⟩
    · have := hJA z''; rwa [hxA] at this
    · rw [hz'']
      have e : (2 : ℝ) • x - z - γ • C x - x = -(z - x) - γ • C x := by module
      rw [e, smul_sub γ⁻¹ (-(z - x)) (γ • C x), smul_neg, smul_smul, inv_mul_cancel₀ hg, one_smul]
      abel
    · rw [smul_smul, mul_inv_cancel₀ hg, one_smul]; abel
  have hfixset : Function.fixedPoints (threeOp γ JA JB C) =
      {z : H | ∃ x u : H, (0 : H) ∈ opSum A B C x ∧ u ∈ B x ∧
        (∃ a ∈ A x, u = -a - C x) ∧ z = x + γ • u} := by
    ext z
    constructor
    · intro hz
      obtain ⟨a, ha, hu, hua, hzeq⟩ := hdata z hz
      refine ⟨JB z, γ⁻¹ • (z - JB z), ⟨a, ha, _, hu, ?_⟩, hu, ⟨a, ha, hua⟩, hzeq⟩
      rw [hua]; abel
    · rintro ⟨x, u, _, hu, ⟨a, ha, hua⟩, rfl⟩
      exact hfix_of x u a hu ha hua
  refine ⟨?_, hfixset⟩
  ext x
  constructor
  · rintro ⟨a, ha, b, hb, h0⟩
    refine ⟨x + γ • b, hfix_of x b a hb ha ?_, resolvent_eq γ B JB hγ hB.1 hJB x b hb⟩
    have : b = -a - C x + (a + b + C x) := by abel
    rw [this, ← h0, add_zero]
  · rintro ⟨z, hz, rfl⟩
    obtain ⟨a, ha, hu, hua, _⟩ := hdata z hz
    exact ⟨a, ha, _, hu, by rw [hua]; abel⟩

end ThreeOpSplitting.Convergence

open ThreeOpSplitting.Convergence

theorem solution {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (A B : H → Set H) (C : H → H) (β γ : ℝ) (JA JB : H → H)
    (hA : IsMaximalMonotone A) (hB : IsMaximalMonotone B)
    (hβ : 0 < β) (hC : IsCocoercive β C) (hγ : 0 < γ)
    (hJA : IsResolvent γ A JA) (hJB : IsResolvent γ B JB) :
    zer (opSum A B C) = JB '' Function.fixedPoints (threeOp γ JA JB C) ∧
      Function.fixedPoints (threeOp γ JA JB C) =
        {z : H | ∃ x u : H, (0 : H) ∈ opSum A B C x ∧ u ∈ B x ∧
          (∃ a ∈ A x, u = -a - C x) ∧ z = x + γ • u} := by
  exact lemma_2_2 A B C β γ JA JB hA hB hβ hC hγ hJA hJB
