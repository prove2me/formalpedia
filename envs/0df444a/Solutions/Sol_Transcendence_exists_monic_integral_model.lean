-- Prove2me | solution 1 for Transcendence.exists_monic_integral_model
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-27T08:16:47.542753+00:00
-- url     : https://prove2.me/submissions/eeb3febd-a72f-4bf8-94ca-36f5200f7287

import Mathlib

/-!
# A monic integral model of a simple algebraic extension of `ℚ(ω)`

Let `ω` be transcendental and `θ` algebraic over `ℚ(ω)`, with minimal polynomial `m` of degree `d`.
Every element of `ℚ(ω)` is a quotient `r(ω) / s(ω)` with `r, s ∈ ℤ[X]`. Clearing the denominators
of the coefficients of `m` with one `v ∈ ℤ[X]`, the product of the `s_k`, and rescaling
`ω₁ = v(ω) θ`, gives a polynomial `Q ∈ ℤ[X][Y]`, monic of degree `d` in `Y`, with
`Q(ω, ω₁) = v(ω)^d m(θ) = 0`. Since `ω₁` also has degree `d` over `ℚ(ω)`, and `q ↦ q(ω)` is
injective on `ℤ[X]` because `ω` is transcendental, no non-zero `A ∈ ℤ[X][Y]` of `Y`-degree below
`d` vanishes at `(ω, ω₁)`.
-/

namespace S7W4_exists_monic_integral_model

open Polynomial

/-- A rational polynomial becomes integral after multiplying by a non-zero integer. -/
lemma exists_int_scaled (p : ℚ[X]) :
    ∃ b : ℤ, b ≠ 0 ∧ ∃ q : ℤ[X], q.map (Int.castRingHom ℚ) = C (b : ℚ) * p := by
  obtain ⟨b, hb, h⟩ := IsLocalization.integerNormalization_spec (nonZeroDivisors ℤ) p
  refine ⟨b, nonZeroDivisors.ne_zero hb, IsLocalization.integerNormalization (nonZeroDivisors ℤ) p,
    Polynomial.ext fun i => ?_⟩
  simpa [coeff_map, coeff_C_mul, algebraMap_int_eq] using congrArg (fun q => q.coeff i) h

/-- The embedding `ℤ[X] → ℚ(ω)`, `q ↦ q(ω)`. -/
noncomputable def phiω (ω : ℂ) : ℤ[X] →+* IntermediateField.adjoin ℚ ({ω} : Set ℂ) :=
  Polynomial.eval₂RingHom (Int.castRingHom _) ⟨ω, IntermediateField.mem_adjoin_simple_self ℚ ω⟩

lemma phi_eval (ω : ℂ) :
    (algebraMap (IntermediateField.adjoin ℚ ({ω} : Set ℂ)) ℂ).comp (phiω ω)
      = Polynomial.eval₂RingHom (Int.castRingHom ℂ) ω := by
  refine Polynomial.ringHom_ext (fun a => ?_) ?_
  · simp [phiω]
  · simp [phiω]

lemma phi_coe (ω : ℂ) (q : ℤ[X]) :
    ((phiω ω q : IntermediateField.adjoin ℚ ({ω} : Set ℂ)) : ℂ) = aeval ω q := by
  rw [aeval_def, algebraMap_int_eq]
  exact RingHom.congr_fun (phi_eval ω) q

lemma phi_injective {ω : ℂ} (hω : Transcendental ℚ ω) : Function.Injective (phiω ω) := by
  rw [injective_iff_map_eq_zero (phiω ω)]
  intro q hq
  by_contra hq0
  apply hω
  refine ⟨q.map (Int.castRingHom ℚ), (Polynomial.map_ne_zero_iff (RingHom.injective_int _)).2 hq0, ?_⟩
  have h := phi_coe ω q
  rw [hq] at h
  rw [← algebraMap_int_eq, aeval_map_algebraMap]
  simpa using h.symm

/-- Every element of `ℚ(ω)` is `r(ω)/s(ω)` with `r, s ∈ ℤ[X]`. -/
lemma int_frac {ω : ℂ} (y : IntermediateField.adjoin ℚ ({ω} : Set ℂ)) :
    ∃ r s : ℤ[X], phiω ω s ≠ 0 ∧ y * phiω ω s = phiω ω r := by
  have hy := y.2
  rw [IntermediateField.mem_adjoin_simple_iff] at hy
  obtain ⟨r, s, hrs⟩ := hy
  obtain ⟨n₁, hn₁, q₁, e₁⟩ := exists_int_scaled r
  obtain ⟨n₂, hn₂, q₂, e₂⟩ := exists_int_scaled s
  have hq : ∀ (q : ℤ[X]) (b : ℤ) (p : ℚ[X]), q.map (Int.castRingHom ℚ) = C (b : ℚ) * p →
      ((phiω ω q : IntermediateField.adjoin ℚ ({ω} : Set ℂ)) : ℂ) = (b : ℂ) * aeval ω p := by
    intro q b p e
    rw [phi_coe, ← aeval_map_algebraMap ℚ, algebraMap_int_eq, e, map_mul (aeval ω), aeval_C,
      map_intCast (algebraMap ℚ ℂ)]
  by_cases hs : aeval ω s = 0
  · refine ⟨0, 1, by simp, ?_⟩
    apply Subtype.ext
    simp [hrs, hs]
  refine ⟨C n₂ * q₁, C n₁ * q₂, fun h0 => ?_, Subtype.ext ?_⟩
  · have h := congrArg (fun z : IntermediateField.adjoin ℚ ({ω} : Set ℂ) => (z : ℂ)) h0
    simp only [IntermediateField.coe_zero, map_mul, IntermediateField.coe_mul, hq q₂ n₂ s e₂] at h
    rw [phi_coe, aeval_C, algebraMap_int_eq, eq_intCast (Int.castRingHom ℂ)] at h
    exact mul_ne_zero (Int.cast_ne_zero.2 hn₁) (mul_ne_zero (Int.cast_ne_zero.2 hn₂) hs) h
  · simp only [map_mul, IntermediateField.coe_mul, hq q₁ n₁ r e₁, hq q₂ n₂ s e₂, hrs]
    rw [phi_coe, phi_coe, aeval_C, aeval_C, algebraMap_int_eq, eq_intCast (Int.castRingHom ℂ),
      eq_intCast (Int.castRingHom ℂ)]
    field_simp

end S7W4_exists_monic_integral_model

open Polynomial S7W4_exists_monic_integral_model in
theorem solution (ω θ : ℂ) (hω : Transcendental ℚ ω)
    (hθ : IsAlgebraic (IntermediateField.adjoin ℚ ({ω} : Set ℂ)) θ) :
    ∃ (ω₁ : ℂ) (Q : Polynomial (Polynomial ℤ)), Q.Monic ∧ 0 < Q.natDegree ∧
      Polynomial.eval₂ (Polynomial.eval₂RingHom (Int.castRingHom ℂ) ω) ω₁ Q = 0 ∧
      (∀ A : Polynomial (Polynomial ℤ), A.natDegree < Q.natDegree →
        Polynomial.eval₂ (Polynomial.eval₂RingHom (Int.castRingHom ℂ) ω) ω₁ A = 0 → A = 0) ∧
      ∃ v : Polynomial ℤ, Polynomial.aeval ω v ≠ 0 ∧ ω₁ = Polynomial.aeval ω v * θ := by
  classical
  set F := IntermediateField.adjoin ℚ ({ω} : Set ℂ) with hF
  have hθi : IsIntegral F θ := hθ.isIntegral
  set φ := Polynomial.eval₂RingHom (Polynomial.eval₂RingHom (Int.castRingHom ℂ) ω)
  set m := minpoly F θ with hm
  set d := m.natDegree with hd
  have hmon : m.Monic := minpoly.monic hθi
  have hdpos : 0 < d := minpoly.natDegree_pos hθi
  choose r s hs hrs using fun k : ℕ => int_frac (ω := ω) (m.coeff k)
  set v : ℤ[X] := ∏ k : Fin d, s k with hv
  have hv0 : phiω ω v ≠ 0 := by
    rw [hv, map_prod (phiω ω)]
    exact Finset.prod_ne_zero_iff.2 fun k _ => hs k
  set t : Fin d → ℤ[X] := fun k => r k * (∏ j ∈ Finset.univ.erase k, s j) * v ^ (d - 1 - k) with ht
  set Q : Polynomial (Polynomial ℤ) := X ^ d + ∑ k : Fin d, C (t k) * X ^ (k : ℕ) with hQ
  set c : ℂ := algebraMap F ℂ (phiω ω v) with hc
  set ω₁ : ℂ := c * θ with hω₁
  have hc0 : c ≠ 0 := by
    rw [hc]; exact (map_ne_zero_iff _ (algebraMap F ℂ).injective).2 hv0
  have hEC : ∀ q : ℤ[X], φ ω₁ (C q) = algebraMap F ℂ (phiω ω q) := fun q => by
    simp only [φ, coe_eval₂RingHom, eval₂_C]
    exact (RingHom.congr_fun (phi_eval ω) q).symm
  have hdeg : (∑ k : Fin d, C (t k) * X ^ (k : ℕ)).degree < (d : WithBot ℕ) :=
    Polynomial.degree_sum_fin_lt t
  have hQmon : Q.Monic := Polynomial.monic_X_pow_add hdeg
  have hQdeg : Q.natDegree = d := by
    rw [hQ, Polynomial.natDegree_add_eq_left_of_degree_lt (by rwa [Polynomial.degree_X_pow]),
      Polynomial.natDegree_X_pow]
  refine ⟨ω₁, Q, hQmon, by rw [hQdeg]; exact hdpos, ?_, ?_, v, ?_, ?_⟩
  · -- `Q(ω, ω₁) = c^d · m(θ) = 0`
    have hsum : aeval θ m = 0 := minpoly.aeval F θ
    rw [hmon.as_sum] at hsum
    simp only [map_add, map_pow, aeval_X, map_sum, map_mul, aeval_C] at hsum
    rw [← Fin.sum_univ_eq_sum_range (fun i => algebraMap F ℂ (m.coeff i) * θ ^ i) d] at hsum
    have key : ∀ k : Fin d, φ ω₁ (C (t k)) * ω₁ ^ (k : ℕ)
        = c ^ d * (algebraMap F ℂ (m.coeff k) * θ ^ (k : ℕ)) := by
      intro k
      have hrk : algebraMap F ℂ (phiω ω (r k))
          = algebraMap F ℂ (m.coeff k) * algebraMap F ℂ (phiω ω (s k)) := by
        rw [← map_mul (algebraMap F ℂ), hrs k]
      have hvprod : algebraMap F ℂ (phiω ω (s k))
          * algebraMap F ℂ (phiω ω (∏ j ∈ Finset.univ.erase k, s j)) = c := by
        rw [← map_mul (algebraMap F ℂ), ← map_mul (phiω ω), hc, hv,
          Finset.mul_prod_erase Finset.univ (fun j : Fin d => s j) (Finset.mem_univ k)]
      have htk : φ ω₁ (C (t k)) = algebraMap F ℂ (phiω ω (r k))
          * algebraMap F ℂ (phiω ω (∏ j ∈ Finset.univ.erase k, s j)) * c ^ (d - 1 - (k : ℕ)) := by
        rw [hEC, ht]
        simp only [map_mul, map_pow, hc]
      have hexp : c ^ d = c * c ^ (d - 1 - (k : ℕ)) * c ^ (k : ℕ) := by
        rw [← pow_succ', ← pow_add]; congr 1; omega
      rw [htk, hrk, hω₁, mul_pow, hexp, ← hvprod]
      ring
    calc φ ω₁ Q = ω₁ ^ d + ∑ k : Fin d, φ ω₁ (C (t k)) * ω₁ ^ (k : ℕ) := by
          simp only [hQ, map_add, map_pow, map_sum, map_mul, φ, coe_eval₂RingHom, eval₂_X]
      _ = c ^ d * (θ ^ d + ∑ k : Fin d, algebraMap F ℂ (m.coeff k) * θ ^ (k : ℕ)) := by
          rw [Finset.sum_congr rfl fun k _ => key k, ← Finset.mul_sum, hω₁, mul_pow]
          ring
      _ = 0 := by rw [hsum, mul_zero]
  · -- minimality: `ω₁` has degree `d` over `ℚ(ω)`, and `q ↦ q(ω)` is injective on `ℤ[X]`
    intro A hA hA0
    rw [hQdeg] at hA
    have hB : aeval ω₁ (A.map (phiω ω)) = φ ω₁ A := by
      rw [aeval_def, eval₂_map, phi_eval]
      rfl
    have hint : IsIntegral F ω₁ := (isIntegral_algebraMap (x := phiω ω v)).mul hθi
    have hadj : IntermediateField.adjoin F ({ω₁} : Set ℂ) = IntermediateField.adjoin F ({θ} : Set ℂ) := by
      apply le_antisymm
      · rw [IntermediateField.adjoin_simple_le_iff]
        exact mul_mem (IntermediateField.algebraMap_mem _ _) (IntermediateField.mem_adjoin_simple_self F θ)
      · rw [IntermediateField.adjoin_simple_le_iff]
        have hθeq : θ = algebraMap F ℂ (phiω ω v)⁻¹ * ω₁ := by
          rw [hω₁, hc, ← mul_assoc, ← map_mul (algebraMap F ℂ), inv_mul_cancel₀ hv0,
            map_one (algebraMap F ℂ), one_mul]
        rw [hθeq]
        exact mul_mem (IntermediateField.algebraMap_mem _ _) (IntermediateField.mem_adjoin_simple_self F ω₁)
    have hdeg1 : (minpoly F ω₁).natDegree = d := by
      rw [← IntermediateField.adjoin.finrank hint, hadj, IntermediateField.adjoin.finrank hθi]
    by_contra hA0'
    have hB0 : A.map (phiω ω) ≠ 0 := (Polynomial.map_ne_zero_iff (phi_injective hω)).2 hA0'
    have h1 := minpoly.degree_le_of_ne_zero F ω₁ hB0 (hB.trans hA0)
    have h2 := Polynomial.natDegree_le_natDegree h1
    rw [hdeg1, Polynomial.natDegree_map_eq_of_injective (phi_injective hω)] at h2
    omega
  · rw [← phi_coe]; exact hc0
  · rw [← phi_coe]; rfl

#print axioms solution
