-- Prove2me | solution 1 for Transcendence.exp_e_or_exp_e_sq_transcendental
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-30T07:41:56.773888+00:00
-- url     : https://prove2.me/submissions/093a57a8-ae45-4e30-852a-c8c24c427b7b

import Mathlib
import Theorems.Thm_DiazModulus_hermite_lindemann_holds
import Theorems.Thm_Transcendence_trdeg_adjoin_le_one_of_isAlgebraic_adjoin
import Theorems.Thm_DiazModulus_two_algebraically_independent_of_exp_column

/-!
# `e^e` or `e^{e²}` is transcendental

Suppose that `e^e` and `e^{e²}` are both algebraic. Apply Waldschmidt's theorem of 1973
(`DiazModulus.two_algebraically_independent_of_exp_column`) to

  `x₁ = 1`, `x₂ = e`, `y₁ = 1`, `y₂ = e`.

The number `e` is transcendental by Hermite–Lindemann, so `1, e` are `ℚ`-linearly independent. The
column is `e^{x₁y₂} = e^e` and `e^{x₂y₂} = e^{e²}`, algebraic by assumption. So two of the eight
numbers

  `1`, `e`, `1`, `e`, `e^{1·1} = e`, `e^e`, `e^e`, `e^{e²}`

are algebraically independent. But all eight are algebraic over `ℚ[e]`, so the `ℚ`-algebra they
generate has transcendence degree at most `1`, which contradicts the two algebraically independent
numbers it contains.
-/

namespace T2_exp_e_or_exp_e_sq_transcendental

/-! ## Numbers algebraic over `ℚ[x]` -/

/-- The complex numbers algebraic over `ℚ[x]`, as a `ℚ`-subalgebra of `ℂ`. -/
noncomputable def algOver (x : ℂ) : Subalgebra ℚ ℂ :=
  (Subalgebra.algebraicClosure ↥(Algebra.adjoin ℚ ({x} : Set ℂ)) ℂ).restrictScalars ℚ

theorem mem_algOver_of_isAlgebraic {x z : ℂ} (h : IsAlgebraic ℚ z) : z ∈ algOver x :=
  h.extendScalars (algebraMap ℚ ↥(Algebra.adjoin ℚ ({x} : Set ℂ))).injective

theorem self_mem_algOver (x : ℂ) : x ∈ algOver x :=
  isAlgebraic_algebraMap (⟨x, Algebra.subset_adjoin rfl⟩ : ↥(Algebra.adjoin ℚ ({x} : Set ℂ)))

/-- If every element of `S` is algebraic over `ℚ[x]`, no two elements of `S` are algebraically
independent over `ℚ`: they would sit in `ℚ[S]`, of transcendence degree at most one. -/
theorem not_algIndep_of_forall_mem_algOver {x : ℂ} {S : Set ℂ} (hS : ∀ s ∈ S, s ∈ algOver x)
    {a b : ℂ} (ha : a ∈ S) (hb : b ∈ S) : ¬ AlgebraicIndependent ℚ ![a, b] := fun hab => by
  have hv : AlgebraicIndependent ℚ (![⟨a, Algebra.subset_adjoin ha⟩, ⟨b, Algebra.subset_adjoin hb⟩] :
      Fin 2 → ↥(Algebra.adjoin ℚ S)) :=
    .of_comp (Algebra.adjoin ℚ S).val (by convert hab using 1; funext i; fin_cases i <;> rfl)
  have h := hv.cardinalMk_le_trdeg.trans
    (Transcendence.trdeg_adjoin_le_one_of_isAlgebraic_adjoin (K := ℚ) x S hS)
  rw [Cardinal.mk_fin] at h
  norm_num at h

/-! ## The choice of `x` and `y` -/

/-- `1` and `e` are `ℚ`-linearly independent, because `e` is irrational. -/
theorem linIndep_one_exp_one (he : Transcendental ℚ (Complex.exp 1)) :
    LinearIndependent ℚ ![(1 : ℂ), Complex.exp 1] := by
  rw [LinearIndependent.pair_iff]
  intro s t hst
  rw [Rat.smul_def, Rat.smul_def, mul_one] at hst
  by_cases ht : t = 0
  · subst ht
    simp only [Rat.cast_zero, zero_mul, add_zero, Rat.cast_eq_zero] at hst
    exact ⟨hst, rfl⟩
  · exfalso
    apply he
    have htC : (t : ℂ) ≠ 0 := by exact_mod_cast ht
    have h' : Complex.exp 1 = ((-s / t : ℚ) : ℂ) := by
      push_cast
      field_simp
      linear_combination hst
    rw [h']
    exact isAlgebraic_ratCast ℚ _

end T2_exp_e_or_exp_e_sq_transcendental

open T2_exp_e_or_exp_e_sq_transcendental in
theorem solution :
    Transcendental ℚ (Complex.exp (Complex.exp 1)) ∨
      Transcendental ℚ (Complex.exp (Complex.exp 1 ^ 2)) := by
  by_contra h
  simp only [not_or, Transcendental, not_not] at h
  obtain ⟨h1, h2⟩ := h
  -- `e` is transcendental, by Hermite–Lindemann
  have he : Transcendental ℚ (Complex.exp 1) :=
    DiazModulus.hermite_lindemann_holds 1 one_ne_zero isAlgebraic_one
  -- the column `e^{x₁y₂} = e^e`, `e^{x₂y₂} = e^{e²}`
  have h12 : IsAlgebraic ℚ (Complex.exp (1 * Complex.exp 1)) := by
    rw [one_mul]
    exact h1
  have h22 : IsAlgebraic ℚ (Complex.exp (Complex.exp 1 * Complex.exp 1)) := by
    rw [← sq]
    exact h2
  obtain ⟨a, ha, b, hb, hab⟩ := DiazModulus.two_algebraically_independent_of_exp_column 1
    (Complex.exp 1) 1 (Complex.exp 1) (linIndep_one_exp_one he) (linIndep_one_exp_one he) h12 h22
  -- all eight numbers are algebraic over `ℚ[e]`
  refine not_algIndep_of_forall_mem_algOver (x := Complex.exp 1) ?_ ha hb hab
  intro s hs
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hs
  rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · -- `x₁ = 1`
    exact one_mem _
  · -- `x₂ = e`
    exact self_mem_algOver _
  · -- `y₁ = 1`
    exact one_mem _
  · -- `y₂ = e`
    exact self_mem_algOver _
  · -- `e^{x₁y₁} = e`
    rw [mul_one]
    exact self_mem_algOver _
  · -- `e^{x₁y₂} = e^e`
    exact mem_algOver_of_isAlgebraic h12
  · -- `e^{x₂y₁} = e^e`
    rw [mul_one]
    exact mem_algOver_of_isAlgebraic h1
  · -- `e^{x₂y₂} = e^{e²}`
    exact mem_algOver_of_isAlgebraic h22
