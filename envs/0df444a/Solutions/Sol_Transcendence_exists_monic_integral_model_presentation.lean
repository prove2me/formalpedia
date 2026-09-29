-- Prove2me | solution 1 for Transcendence.exists_monic_integral_model_presentation
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-27T08:09:49.858065+00:00
-- url     : https://prove2.me/submissions/7878bb56-8356-491c-a527-d2d4dc2d38d0

import Mathlib
import Theorems.Thm_Transcendence_exists_monic_integral_model

/-!
# A common presentation over one monic integral model

Let `ω` be transcendental and let `z₁, …, z_k` be algebraic over `ℚ(ω)`. By the primitive element
theorem they lie in `ℚ(ω)[θ]` for one `θ` algebraic over `ℚ(ω)`; rescale `θ` to `ω₁ = v(ω) θ`, a
root of a polynomial `Q ∈ ℤ[X][Y]` monic in `Y` and minimal at `(ω, ω₁)`. Call `y` presentable if
`y · D(ω, ω₁) = E(ω, ω₁)` for some `D, E ∈ ℤ[X][Y]` with `D(ω, ω₁) ≠ 0`. Presentable numbers are
closed under sums and products; every element of `ℚ(ω)` is presentable, as `r(ω) / s(ω)` with
`r, s ∈ ℤ[X]`, and so is `θ = ω₁ / v(ω)`. Hence every `zᵢ = pᵢ(θ)` is presentable, and a product of
denominators serves all the `zᵢ` at once.
-/

namespace S7W4_exists_monic_integral_model_presentation

open Polynomial

/-- Evaluation of `A ∈ ℤ[X][Y]` at `(ω, ω₁)`, as a ring hom. -/
noncomputable def evH (ω ω₁ : ℂ) : Polynomial (Polynomial ℤ) →+* ℂ :=
  Polynomial.eval₂RingHom (Polynomial.eval₂RingHom (Int.castRingHom ℂ) ω) ω₁

/-- `y` has a presentation `y · D = E` at `(ω, ω₁)` with `D ≠ 0` there. -/
def Presentable (ω ω₁ y : ℂ) : Prop :=
  ∃ D E : Polynomial (Polynomial ℤ), evH ω ω₁ D ≠ 0 ∧ y * evH ω ω₁ D = evH ω ω₁ E

lemma presentable_add {ω ω₁ y z : ℂ} (hy : Presentable ω ω₁ y) (hz : Presentable ω ω₁ z) :
    Presentable ω ω₁ (y + z) := by
  obtain ⟨D₁, E₁, h₁, e₁⟩ := hy
  obtain ⟨D₂, E₂, h₂, e₂⟩ := hz
  refine ⟨D₁ * D₂, E₁ * D₂ + E₂ * D₁, by simp [h₁, h₂], ?_⟩
  simp only [map_mul, map_add]
  rw [← e₁, ← e₂]
  ring

lemma presentable_mul {ω ω₁ y z : ℂ} (hy : Presentable ω ω₁ y) (hz : Presentable ω ω₁ z) :
    Presentable ω ω₁ (y * z) := by
  obtain ⟨D₁, E₁, h₁, e₁⟩ := hy
  obtain ⟨D₂, E₂, h₂, e₂⟩ := hz
  refine ⟨D₁ * D₂, E₁ * E₂, by simp [h₁, h₂], ?_⟩
  simp only [map_mul]
  rw [← e₁, ← e₂]
  ring

lemma presentable_pow {ω ω₁ θ : ℂ} (hθ : Presentable ω ω₁ θ) (n : ℕ) :
    Presentable ω ω₁ (θ ^ n) := by
  induction n with
  | zero => exact ⟨1, 1, by simp, by simp⟩
  | succ n ih => rw [pow_succ]; exact presentable_mul ih hθ

lemma common_denominator {ω ω₁ : ℂ} {ι : Type*} [Fintype ι] (f : ι → ℂ)
    (h : ∀ i, Presentable ω ω₁ (f i)) :
    ∃ D : Polynomial (Polynomial ℤ), evH ω ω₁ D ≠ 0 ∧
      ∀ i, ∃ E : Polynomial (Polynomial ℤ), f i * evH ω ω₁ D = evH ω ω₁ E := by
  classical
  choose D E hD hE using h
  refine ⟨∏ i, D i, ?_, fun i => ⟨E i * ∏ j ∈ Finset.univ.erase i, D j, ?_⟩⟩
  · rw [map_prod (evH ω ω₁)]
    exact Finset.prod_ne_zero_iff.2 fun i _ => hD i
  · rw [map_prod (evH ω ω₁), map_mul (evH ω ω₁), map_prod (evH ω ω₁),
      ← Finset.mul_prod_erase Finset.univ (fun j => evH ω ω₁ (D j)) (Finset.mem_univ i),
      ← mul_assoc, hE i]

/-- A rational polynomial becomes integral after multiplying by a non-zero integer. -/
lemma exists_int_scaled (p : ℚ[X]) :
    ∃ b : ℤ, b ≠ 0 ∧ ∃ q : ℤ[X], q.map (Int.castRingHom ℚ) = C (b : ℚ) * p := by
  obtain ⟨b, hb, h⟩ := IsLocalization.integerNormalization_spec (nonZeroDivisors ℤ) p
  refine ⟨b, nonZeroDivisors.ne_zero hb, IsLocalization.integerNormalization (nonZeroDivisors ℤ) p,
    Polynomial.ext fun i => ?_⟩
  simpa [coeff_map, coeff_C_mul, algebraMap_int_eq] using congrArg (fun q => q.coeff i) h

lemma evH_C (ω ω₁ : ℂ) (q : ℤ[X]) :
    evH ω ω₁ (C q) = aeval ω (q.map (Int.castRingHom ℚ)) := by
  simp only [evH, Polynomial.coe_eval₂RingHom, eval₂_C, aeval_def, eval₂_map]
  congr 1

/-- Every element of `ℚ(ω)` is presentable. -/
lemma presentable_of_mem {ω ω₁ y : ℂ} (hy : y ∈ IntermediateField.adjoin ℚ ({ω} : Set ℂ)) :
    Presentable ω ω₁ y := by
  rw [IntermediateField.mem_adjoin_simple_iff] at hy
  obtain ⟨r, s, rfl⟩ := hy
  obtain ⟨n₁, hn₁, q₁, e₁⟩ := exists_int_scaled r
  obtain ⟨n₂, hn₂, q₂, e₂⟩ := exists_int_scaled s
  by_cases hs : aeval ω s = 0
  · rw [hs, div_zero]
    exact ⟨1, 0, by simp, by simp⟩
  refine ⟨C (C n₁ * q₂), C (C n₂ * q₁), ?_, ?_⟩
  · rw [evH_C, Polynomial.map_mul, e₂, Polynomial.map_C]
    simp only [eq_intCast, map_mul, map_intCast]
    exact mul_ne_zero (Int.cast_ne_zero.2 hn₁) (mul_ne_zero (Int.cast_ne_zero.2 hn₂) hs)
  · rw [evH_C, evH_C, Polynomial.map_mul, Polynomial.map_mul, e₁, e₂, Polynomial.map_C,
      Polynomial.map_C]
    simp only [eq_intCast, map_mul, map_intCast]
    field_simp

/-- If `θ` is presentable, so is every `p(θ)` with `p ∈ ℚ(ω)[X]`. -/
lemma presentable_aeval {ω ω₁ θ : ℂ} (hθ : Presentable ω ω₁ θ)
    (p : Polynomial (IntermediateField.adjoin ℚ ({ω} : Set ℂ))) :
    Presentable ω ω₁ (aeval θ p) := by
  induction p using Polynomial.induction_on with
  | C a =>
    rw [aeval_C]
    exact presentable_of_mem a.2
  | add p q hp hq => rw [map_add (aeval θ)]; exact presentable_add hp hq
  | monomial n a _ =>
    rw [map_mul (aeval θ), map_pow (aeval θ), aeval_C, aeval_X]
    exact presentable_mul (presentable_of_mem a.2) (presentable_pow hθ (n + 1))

/-- Finitely many elements algebraic over `F` lie in `F[θ]` for one integral `θ`. -/
lemma exists_primitive (F : IntermediateField ℚ ℂ) (S : Finset ℂ) (hS : ∀ z ∈ S, IsAlgebraic F z) :
    ∃ θ : ℂ, IsIntegral F θ ∧ ∀ z ∈ S, ∃ p : Polynomial F, aeval θ p = z := by
  classical
  set E := IntermediateField.adjoin F (S : Set ℂ) with hE
  have : FiniteDimensional F E :=
    IntermediateField.finiteDimensional_adjoin fun z hz => (hS z hz).isIntegral
  obtain ⟨α, hα⟩ := Field.exists_primitive_element F E
  have hαint : IsIntegral F α := .of_finite F α
  refine ⟨(α : ℂ), hαint.map E.val, fun z hz => ?_⟩
  have hzE : (⟨z, IntermediateField.subset_adjoin F _ hz⟩ : E) ∈
      IntermediateField.adjoin F ({α} : Set E) := by
    rw [hα]; exact IntermediateField.mem_top
  have hsub : (IntermediateField.adjoin F ({α} : Set E)).toSubalgebra = Algebra.adjoin F {α} :=
    IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic hαint.isAlgebraic
  have hmem : (⟨z, IntermediateField.subset_adjoin F _ hz⟩ : E) ∈ Algebra.adjoin F {α} := by
    rw [← hsub]; exact hzE
  rw [Algebra.adjoin_singleton_eq_range_aeval] at hmem
  obtain ⟨p, hp⟩ := hmem
  refine ⟨p, ?_⟩
  have := congrArg E.val hp
  simpa [Polynomial.aeval_algHom_apply] using this

end S7W4_exists_monic_integral_model_presentation

open Polynomial S7W4_exists_monic_integral_model_presentation in
theorem solution (ω : ℂ) (hω : Transcendental ℚ ω)
    {ι : Type*} [Finite ι] (z : ι → ℂ)
    (hz : ∀ i, IsAlgebraic (IntermediateField.adjoin ℚ ({ω} : Set ℂ)) (z i)) :
    ∃ (ω₁ : ℂ) (Q : Polynomial (Polynomial ℤ)), Q.Monic ∧ 0 < Q.natDegree ∧
      Polynomial.eval₂ (Polynomial.eval₂RingHom (Int.castRingHom ℂ) ω) ω₁ Q = 0 ∧
      (∀ A : Polynomial (Polynomial ℤ), A.natDegree < Q.natDegree →
        Polynomial.eval₂ (Polynomial.eval₂RingHom (Int.castRingHom ℂ) ω) ω₁ A = 0 → A = 0) ∧
      ∃ (D : Polynomial (Polynomial ℤ)) (E : ι → Polynomial (Polynomial ℤ)),
        Polynomial.eval₂ (Polynomial.eval₂RingHom (Int.castRingHom ℂ) ω) ω₁ D ≠ 0 ∧
        ∀ i, z i * Polynomial.eval₂ (Polynomial.eval₂RingHom (Int.castRingHom ℂ) ω) ω₁ D =
          Polynomial.eval₂ (Polynomial.eval₂RingHom (Int.castRingHom ℂ) ω) ω₁ (E i) := by
  classical
  have := Fintype.ofFinite ι
  obtain ⟨θ, hθ, hgen⟩ := exists_primitive (IntermediateField.adjoin ℚ ({ω} : Set ℂ))
    (Finset.univ.image z) fun y hy => by
      obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 hy
      exact hz i
  obtain ⟨ω₁, Q, hQm, hQd, hQroot, hQmin, v, hv0, hω₁⟩ :=
    Transcendence.exists_monic_integral_model ω θ hω hθ.isAlgebraic
  have hCv : evH ω ω₁ (C v) = aeval ω v := by
    simp [evH, aeval_def, algebraMap_int_eq]
  have hθpres : Presentable ω ω₁ θ :=
    ⟨C v, X, by rw [hCv]; exact hv0, by rw [hCv, hω₁, mul_comm]; simp [evH]⟩
  have hpres : ∀ i, Presentable ω ω₁ (z i) := fun i => by
    obtain ⟨p, hp⟩ := hgen (z i) (Finset.mem_image_of_mem z (Finset.mem_univ i))
    rw [← hp]
    exact presentable_aeval hθpres p
  obtain ⟨D, hD, hE⟩ := common_denominator z hpres
  choose E hE using hE
  exact ⟨ω₁, Q, hQm, hQd, hQroot, hQmin, D, E, hD, hE⟩

#print axioms solution
