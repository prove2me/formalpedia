-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Gap48.P16.reversible_ideal_cofinite
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-22T00:48:55.055131+00:00
-- url     : https://prove2.me/submissions/74c0b766-4e63-41af-b2a8-2093dd7275fd

import Definitions.Def_QAlgorithms_Papers_Independent_Gap48_P16
noncomputable section

universe u

open QAlgorithms.Papers.Independent.Gap48.P16

open scoped TensorProduct

section Laurent

variable {R : Type u} [CommRing R]

theorem g74b_Tinv {R : Type u} [CommRing R] (q : Polynomial R) (hq : IsReversiblePolynomial q) :
    ∃ (r : Polynomial R) (c : LaurentPolynomial R),
      (LaurentPolynomial.T (-1) : LaurentPolynomial R) - r.toLaurent = c * q.toLaurent := by
  obtain ⟨u, hu⟩ := hq.2
  refine ⟨-(Polynomial.C (↑u⁻¹ : R) * q.divX),
    LaurentPolynomial.C (↑u⁻¹ : R) * LaurentPolynomial.T (-1), ?_⟩
  have hqd : q.toLaurent = LaurentPolynomial.T 1 * q.divX.toLaurent +
      LaurentPolynomial.C (↑u : R) := by
    conv_lhs => rw [← Polynomial.X_mul_divX_add q]
    rw [map_add, map_mul, Polynomial.toLaurent_X, Polynomial.toLaurent_C, hu]
  have h1 : (LaurentPolynomial.T (-1) : LaurentPolynomial R) * LaurentPolynomial.T 1 = 1 := by
    rw [← LaurentPolynomial.T_add]; simp
  have h2 : LaurentPolynomial.C (↑u⁻¹ : R) * LaurentPolynomial.C (↑u : R) =
      (1 : LaurentPolynomial R) := by
    rw [← map_mul, Units.inv_mul, map_one]
  rw [hqd, map_neg, map_mul, Polynomial.toLaurent_C]
  linear_combination (-(LaurentPolynomial.C (↑u⁻¹ : R) * q.divX.toLaurent)) * h1 -
    LaurentPolynomial.T (-1) * h2

theorem g74b_surj {R : Type u} [CommRing R] (q : Polynomial R) (hq : IsReversiblePolynomial q)
    (I : Ideal (LaurentPolynomial R)) (hI : q.toLaurent ∈ I) :
    Function.Surjective (fun p : Polynomial R => Ideal.Quotient.mk I p.toLaurent) := by
  intro y
  obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective y
  obtain ⟨n, f', hf'⟩ := LaurentPolynomial.exists_T_pow f
  obtain ⟨r, c, hrc⟩ := g74b_Tinv q hq
  have hT : Ideal.Quotient.mk I (LaurentPolynomial.T (-1)) = Ideal.Quotient.mk I r.toLaurent :=
    Ideal.Quotient.eq.2 (by rw [hrc]; exact I.mul_mem_left c hI)
  refine ⟨f' * r ^ n, ?_⟩
  simp only [map_mul, map_pow]
  rw [← hT, ← map_pow, ← map_mul]
  congr 1
  rw [hf', LaurentPolynomial.T_pow, mul_assoc, ← LaurentPolynomial.T_add]
  simp

theorem g74b_Xunit {R : Type u} [CommRing R] (q : Polynomial R) (hq : IsReversiblePolynomial q) :
    ∃ s c : Polynomial R, Polynomial.X * s - 1 = c * q := by
  obtain ⟨u, hu⟩ := hq.2
  refine ⟨-(Polynomial.C (↑u⁻¹ : R) * q.divX), -Polynomial.C (↑u⁻¹ : R), ?_⟩
  have hdec := Polynomial.X_mul_divX_add q
  rw [← hu] at hdec
  have h2 : Polynomial.C (↑u⁻¹ : R) * Polynomial.C (↑u : R) = 1 := by
    rw [← map_mul, Units.inv_mul, map_one]
  linear_combination (-Polynomial.C (↑u⁻¹ : R)) * hdec + h2

/-- the canonical map R[X]/(q) → L/I. -/
def g74b_lift {R : Type u} [CommRing R] (q : Polynomial R) (I : Ideal (LaurentPolynomial R))
    (hI : q.toLaurent ∈ I) : (Polynomial R ⧸ Ideal.span {q}) →ₐ[R] LaurentPolynomial R ⧸ I :=
  Ideal.Quotient.liftₐ (Ideal.span {q}) ((Ideal.Quotient.mkₐ R I).comp Polynomial.toLaurentAlg)
    (by
      intro a ha
      obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.1 ha
      simp only [AlgHom.coe_comp, Function.comp_apply, Polynomial.toLaurentAlg_apply, map_mul,
        Ideal.Quotient.mkₐ_eq_mk]
      rw [Ideal.Quotient.eq_zero_iff_mem.2 hI, mul_zero])

theorem g74b_lift_mk {R : Type u} [CommRing R] (q : Polynomial R) (I : Ideal (LaurentPolynomial R))
    (hI : q.toLaurent ∈ I) (p : Polynomial R) :
    g74b_lift q I hI (Ideal.Quotient.mk _ p) = Ideal.Quotient.mk I p.toLaurent := by
  rfl

theorem g74b_lift_surj {R : Type u} [CommRing R] (q : Polynomial R) (hq : IsReversiblePolynomial q)
    (I : Ideal (LaurentPolynomial R)) (hI : q.toLaurent ∈ I) :
    Function.Surjective (g74b_lift q I hI) := by
  intro y
  obtain ⟨p, hp⟩ := g74b_surj q hq I hI y
  exact ⟨Ideal.Quotient.mk _ p, by rw [g74b_lift_mk]; exact hp⟩

/-- Proposition 4.13, PDF p.16: only the converse requires noetherianness. -/
theorem solution (I : Ideal (LaurentPolynomial R)) :
    (IsReversibleIdeal I → Module.Finite R (LaurentPolynomial R ⧸ I)) ∧
    (IsNoetherianRing R → Module.Finite R (LaurentPolynomial R ⧸ I) → IsReversibleIdeal I) := by
  constructor
  · rintro ⟨q, hq, hqI⟩
    haveI : Module.Finite R (Polynomial R ⧸ Ideal.span {q}) := hq.1.finite_adjoinRoot
    exact Module.Finite.of_surjective (g74b_lift q I hqI).toLinearMap (g74b_lift_surj q hq I hqI)
  · intro _ hfin
    haveI := hfin
    have hint : Algebra.IsIntegral R (LaurentPolynomial R ⧸ I) := inferInstance
    obtain ⟨p, hpm, hp⟩ := hint.isIntegral (Ideal.Quotient.mk I (LaurentPolynomial.T 1))
    obtain ⟨s, hsm, hs⟩ := hint.isIntegral (Ideal.Quotient.mk I (LaurentPolynomial.T (-1)))
    have hpI : p.toLaurent ∈ I := by
      rw [← Ideal.Quotient.eq_zero_iff_mem]
      let f : Polynomial R →ₐ[R] LaurentPolynomial R ⧸ I :=
        (Ideal.Quotient.mkₐ R I).comp Polynomial.toLaurentAlg
      have h1 := Polynomial.aeval_algHom_apply f Polynomial.X p
      rw [Polynomial.aeval_X_left_apply] at h1
      have h2 : f Polynomial.X = Ideal.Quotient.mk I (LaurentPolynomial.T 1) := by
        simp [f, Polynomial.toLaurentAlg_apply]
      rw [h2, Polynomial.aeval_def, hp] at h1
      rw [← h1.symm.trans rfl]
      simp [f, Polynomial.toLaurentAlg_apply]
    have hsI : (LaurentPolynomial.invert s.toLaurent) ∈ I := by
      rw [← Ideal.Quotient.eq_zero_iff_mem]
      let f : Polynomial R →ₐ[R] LaurentPolynomial R ⧸ I :=
        (Ideal.Quotient.mkₐ R I).comp
          ((LaurentPolynomial.invert (R := R)).toAlgHom.comp Polynomial.toLaurentAlg)
      have h1 := Polynomial.aeval_algHom_apply f Polynomial.X s
      rw [Polynomial.aeval_X_left_apply] at h1
      have h2 : f Polynomial.X = Ideal.Quotient.mk I (LaurentPolynomial.T (-1)) := by
        simp [f, Polynomial.toLaurentAlg_apply]
      rw [h2, Polynomial.aeval_def, hs] at h1
      rw [← h1.symm.trans rfl]
      simp [f, Polynomial.toLaurentAlg_apply]
    have hrI : s.reverse.toLaurent ∈ I := by
      rw [LaurentPolynomial.toLaurent_reverse]
      exact I.mul_mem_right _ hsI
    set d := s.reverse.natDegree + 1 with hd
    refine ⟨Polynomial.X ^ d * p + s.reverse, ⟨?_, ?_⟩, ?_⟩
    · rcases subsingleton_or_nontrivial R with hR | hR
      · exact Polynomial.monic_of_subsingleton _
      apply ((Polynomial.monic_X_pow d).mul hpm).add_of_left
      apply Polynomial.degree_lt_degree
      rw [((Polynomial.monic_X_pow d)).natDegree_mul hpm, Polynomial.natDegree_X_pow]
      omega
    · rw [Polynomial.coeff_add, Polynomial.coeff_X_pow_mul', Polynomial.coeff_zero_reverse,
        hsm.leadingCoeff]
      simp [hd]
    · rw [map_add, map_mul]
      exact I.add_mem (I.mul_mem_left _ hpI) hrI


end Laurent



end
