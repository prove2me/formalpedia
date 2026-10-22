-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Gap48.P16.reversible_quotient
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-22T00:45:38.318363+00:00
-- url     : https://prove2.me/submissions/9244fdac-16e8-45ae-aa26-7e549f9c6917

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

/-- Lemma 4.12, PDF pp.15-16: the quotient isomorphism induced by polynomial inclusion. -/
theorem solution [IsNoetherianRing R] (q : Polynomial R) (hq : IsReversiblePolynomial q) :
    ∃ e : (Polynomial R ⧸ Ideal.span {q}) ≃ₐ[R]
        (LaurentPolynomial R ⧸ Ideal.span {q.toLaurent}),
      ∀ p : Polynomial R, e (Ideal.Quotient.mk (Ideal.span {q}) p) =
        Ideal.Quotient.mk (Ideal.span {q.toLaurent}) p.toLaurent := by
  have hJ : q.toLaurent ∈ Ideal.span {q.toLaurent} := Ideal.subset_span rfl
  have hinj : Function.Injective (g74b_lift q _ hJ) := by
    rw [injective_iff_map_eq_zero]
    intro x hx
    obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective x
    rw [g74b_lift_mk, Ideal.Quotient.eq_zero_iff_mem] at hx
    obtain ⟨l, hl⟩ := Ideal.mem_span_singleton'.1 hx
    obtain ⟨n, l', hl'⟩ := LaurentPolynomial.exists_T_pow l
    have hpoly : p * Polynomial.X ^ n = l' * q := by
      apply Polynomial.toLaurent_injective
      rw [map_mul, map_mul, Polynomial.toLaurent_X_pow, hl', ← hl]
      ring
    obtain ⟨s, c, hsc⟩ := g74b_Xunit q hq
    have hXs : Ideal.Quotient.mk (Ideal.span {q}) Polynomial.X *
        Ideal.Quotient.mk (Ideal.span {q}) s = 1 := by
      rw [← map_mul, ← map_one (Ideal.Quotient.mk (Ideal.span {q})), Ideal.Quotient.eq, hsc]
      exact Ideal.mul_mem_left _ _ (Ideal.subset_span rfl)
    have hz : Ideal.Quotient.mk (Ideal.span {q}) (p * Polynomial.X ^ n) = 0 := by
      rw [hpoly, Ideal.Quotient.eq_zero_iff_mem]
      exact Ideal.mul_mem_left _ _ (Ideal.subset_span rfl)
    calc Ideal.Quotient.mk (Ideal.span {q}) p
        = Ideal.Quotient.mk (Ideal.span {q}) p *
          (Ideal.Quotient.mk (Ideal.span {q}) Polynomial.X *
            Ideal.Quotient.mk (Ideal.span {q}) s) ^ n := by rw [hXs, one_pow, mul_one]
      _ = Ideal.Quotient.mk (Ideal.span {q}) (p * Polynomial.X ^ n) *
            Ideal.Quotient.mk (Ideal.span {q}) s ^ n := by rw [map_mul, map_pow]; ring
      _ = 0 := by rw [hz, zero_mul]
  have hbij : Function.Bijective (g74b_lift q _ hJ) := ⟨hinj, g74b_lift_surj q hq _ hJ⟩
  exact ⟨AlgEquiv.ofBijective (g74b_lift q _ hJ) hbij, fun p => g74b_lift_mk q _ hJ p⟩


end Laurent



end
