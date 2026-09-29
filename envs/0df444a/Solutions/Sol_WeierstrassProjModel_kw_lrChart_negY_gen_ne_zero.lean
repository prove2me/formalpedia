-- Prove2me | solution 1 for WeierstrassProjModel.kw_lrChart_negY_gen_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.822295+00:00
-- url     : https://prove2.me/submissions/d5c087fe-807c-53c3-8e1d-fac9eb0b492f

import Definitions.Def_WeierstrassCurve_ProjModel_GroupLawVocabulary
import Mathlib.RingTheory.Localization.Away.Basic
import Mathlib.Algebra.Polynomial.Degree.Operations
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_WeierstrassProjModel_kw_lrChart_negY_gen_ne_zero

set_option autoImplicit false
set_option maxHeartbeats 6400000
set_option synthInstance.maxHeartbeats 1600000
set_option linter.unusedSimpArgs false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra WeierstrassProjModel
open MvPolynomial WeierstrassCurve HomogeneousLocalization
open scoped TensorProduct

universe u

attribute [local instance] MvPolynomial.gradedAlgebra
attribute [local instance] WeierstrassProjModel.kw_pbac_awayAlgebra

variable {R : Type u} [CommRing R] (W : WeierstrassCurve R)

set_option quotPrecheck false in
local notation "𝒜" i => HomogeneousLocalization.Away (projModelGradingCR W.toProjective)
  (Ideal.Quotient.mk (projModelHomogeneousIdealCR W.toProjective).toIdeal
    (X i : MvPolynomial (Fin 3) R))

set_option quotPrecheck false in
local notation "mk₃" => Ideal.Quotient.mk (projModelHomogeneousIdealCR W.toProjective).toIdeal

theorem aux_not_X2_dvd [Nontrivial R] :
    ¬ (X 2 : MvPolynomial (Fin 3) R) ∣ W.toProjective.polynomial := by
  intro hd
  have h := map_dvd (MvPolynomial.eval ![(1:R), 0, 0]) hd
  rw [show (MvPolynomial.eval ![(1:R), 0, 0]) (X 2 : MvPolynomial (Fin 3) R) = 0 from by simp,
    zero_dvd_iff,
    show (MvPolynomial.eval ![(1:R), 0, 0]) W.toProjective.polynomial = -1 from by
      rw [WeierstrassCurve.Projective.polynomial]; simp] at h
  exact neg_ne_zero.mpr one_ne_zero h

theorem aux_cancel_X2 [IsDomain R] (L : MvPolynomial (Fin 3) R) :
    ∀ n, W.toProjective.polynomial ∣ (X 2)^n * L → W.toProjective.polynomial ∣ L := by
  intro n
  induction n with
  | zero => rw [pow_zero, one_mul]; exact id
  | succ n ih =>
    rintro ⟨f, hf⟩
    have hXf : (X 2 : MvPolynomial (Fin 3) R) ∣ f :=
      ((MvPolynomial.X_prime (i := (2:Fin 3))).dvd_mul.mp
        ⟨(X 2)^n * L, by rw [← hf]; ring⟩).resolve_left (aux_not_X2_dvd W)
    obtain ⟨g, rfl⟩ := hXf
    refine ih ⟨g, mul_left_cancel₀ (MvPolynomial.X_ne_zero (2:Fin 3)) ?_⟩
    rw [pow_succ] at hf; linear_combination hf

theorem aux_eq_zero_of_coeff_two_one_dvd [IsDomain R] {p q : Polynomial R}
    (hp2 : p.coeff 2 = 1) (hq1 : q.natDegree ≤ 1) (hd : p ∣ q) : q = 0 := by
  by_contra hq0
  have hle := Polynomial.natDegree_le_of_dvd hd hq0
  have hp2' : 2 ≤ p.natDegree := Polynomial.le_natDegree_of_ne_zero (hp2 ▸ one_ne_zero)
  omega

theorem aux_eq_zero_of_coeff_three_dvd [IsDomain R] {p q : Polynomial R}
    (hp3 : p.coeff 3 = 1 ∨ p.coeff 3 = -1) (hq1 : q.natDegree ≤ 1) (hd : p ∣ q) : q = 0 := by
  by_contra hq0
  have hle := Polynomial.natDegree_le_of_dvd hd hq0
  have hc3 : p.coeff 3 ≠ 0 := by
    rcases hp3 with h | h
    · exact h ▸ one_ne_zero
    · exact h ▸ neg_ne_zero.mpr one_ne_zero
  have hp3' : 3 ≤ p.natDegree := Polynomial.le_natDegree_of_ne_zero hc3
  omega

theorem solution [IsDomain R] [W.IsElliptic] :
    (2 : (𝒜 (2 : Fin 3))) * kw_lrChart_gen W 2 1
      + (algebraMap R (𝒜 (2 : Fin 3)) W.a₁) * kw_lrChart_gen W 2 0
      + algebraMap R (𝒜 (2 : Fin 3)) W.a₃ ≠ 0 := by

  set L : MvPolynomial (Fin 3) R := C 2 * X 1 + C W.a₁ * X 0 + C W.a₃ * X 2 with hL
  have hg22 : kw_lrChart_gen W 2 (2:Fin 3) = 1 := by
    apply HomogeneousLocalization.val_injective
    rw [kw_lrChart_gen_val, HomogeneousLocalization.val_one]
    exact Localization.mk_self
      (⟨mk₃ (X 2 : MvPolynomial (Fin 3) R), 1, pow_one _⟩
        : Submonoid.powers (mk₃ (X 2 : MvPolynomial (Fin 3) R)))
  have hrewrite : (2 : (𝒜 (2:Fin 3))) * kw_lrChart_gen W 2 1
      + (algebraMap R (𝒜 (2:Fin 3)) W.a₁) * kw_lrChart_gen W 2 0
      + algebraMap R (𝒜 (2:Fin 3)) W.a₃
    = kw_lrChart_dehom W 2 L := by
    simp only [hL, kw_lrChart_dehom, map_add, map_mul, aeval_C, aeval_X, hg22, mul_one,
      map_ofNat]
  rw [hrewrite]

  have hLhom : L.IsHomogeneous 1 := by
    rw [hL]
    refine IsHomogeneous.add (IsHomogeneous.add ?_ ?_) ?_
    · exact (isHomogeneous_C (Fin 3) (2:R)).mul (isHomogeneous_X R 1)
    · exact (isHomogeneous_C (Fin 3) W.a₁).mul (isHomogeneous_X R 0)
    · exact (isHomogeneous_C (Fin 3) W.a₃).mul (isHomogeneous_X R 2)

  intro h
  have hval := congrArg
    (algebraMap (𝒜 (2:Fin 3)) (Localization.Away (mk₃ (X 2 : MvPolynomial (Fin 3) R)))) h
  rw [map_zero, HomogeneousLocalization.algebraMap_apply,
    kw_lrChart_dehom_isHomogeneous_val W 2 1 L hLhom,
    Localization.mk_eq_mk', IsLocalization.mk'_eq_zero_iff] at hval
  obtain ⟨⟨_, n, rfl⟩, hn⟩ := hval
  simp only at hn
  rw [← map_pow, ← map_mul, Ideal.Quotient.eq_zero_iff_mem,
    projModelHomogeneousIdealCR_toIdeal, Ideal.mem_span_singleton] at hn

  have hdvd : W.toProjective.polynomial ∣ L := aux_cancel_X2 W L n hn

  have hev1 := map_dvd (MvPolynomial.eval₂Hom Polynomial.C
      ![(0:Polynomial R), Polynomial.X, 1]) hdvd
  rw [show (MvPolynomial.eval₂Hom Polynomial.C ![(0:Polynomial R), Polynomial.X, 1])
        W.toProjective.polynomial
      = Polynomial.X^2 + Polynomial.C W.a₃ * Polynomial.X - Polynomial.C W.a₆ from by
        rw [WeierstrassCurve.Projective.polynomial]
        simp only [map_sub, map_add, map_mul, map_pow, MvPolynomial.eval₂Hom_X',
          Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
          Matrix.cons_val_two, Matrix.tail_cons, MvPolynomial.eval₂Hom_C]
        ring,
    show (MvPolynomial.eval₂Hom Polynomial.C ![(0:Polynomial R), Polynomial.X, 1]) L
      = Polynomial.C (2:R) * Polynomial.X + Polynomial.C W.a₃ from by
        rw [hL]
        simp only [map_add, map_mul, MvPolynomial.eval₂Hom_C, MvPolynomial.eval₂Hom_X',
          Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
          Matrix.cons_val_two, Matrix.tail_cons, mul_zero, zero_add, add_zero, mul_one]] at hev1
  have hL1z : Polynomial.C (2:R) * Polynomial.X + Polynomial.C W.a₃ = 0 :=
    aux_eq_zero_of_coeff_two_one_dvd
      (by simp [Polynomial.coeff_X_pow])
      (by
        refine (Polynomial.natDegree_add_le _ _).trans (max_le ?_ ?_)
        · exact (Polynomial.natDegree_C_mul_le _ _).trans Polynomial.natDegree_X.le
        · exact (Polynomial.natDegree_C _).trans_le (Nat.zero_le 1))
      hev1
  have h2 : (2 : R) = 0 := by
    have := congrArg (Polynomial.coeff · 1) hL1z
    simpa using this
  have ha₃ : W.a₃ = 0 := by
    have := congrArg (Polynomial.coeff · 0) hL1z
    simpa using this

  have hev2 := map_dvd (MvPolynomial.eval₂Hom Polynomial.C
      ![Polynomial.X, (0:Polynomial R), 0]) hdvd
  rw [show (MvPolynomial.eval₂Hom Polynomial.C ![Polynomial.X, (0:Polynomial R), 0])
        W.toProjective.polynomial
      = -Polynomial.X^3 from by
        rw [WeierstrassCurve.Projective.polynomial]
        simp only [map_sub, map_add, map_mul, map_pow, MvPolynomial.eval₂Hom_X',
          Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
          Matrix.cons_val_two, Matrix.tail_cons, MvPolynomial.eval₂Hom_C]
        ring,
    show (MvPolynomial.eval₂Hom Polynomial.C ![Polynomial.X, (0:Polynomial R), 0]) L
      = Polynomial.C W.a₁ * Polynomial.X from by
        rw [hL]
        simp only [map_add, map_mul, MvPolynomial.eval₂Hom_C, MvPolynomial.eval₂Hom_X',
          Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
          Matrix.cons_val_two, Matrix.tail_cons, mul_zero, add_zero, zero_add, mul_one]] at hev2
  have hL2z : Polynomial.C W.a₁ * Polynomial.X = 0 :=
    aux_eq_zero_of_coeff_three_dvd
      (Or.inr (by simp [Polynomial.coeff_X_pow]))
      ((Polynomial.natDegree_C_mul_le _ _).trans Polynomial.natDegree_X.le)
      hev2
  have ha₁ : W.a₁ = 0 := by
    have := congrArg (Polynomial.coeff · 1) hL2z
    simpa using this

  have hΔ : W.Δ = 0 := by
    have hb : W.Δ = -64*W.a₂^3*W.a₆ + 16*W.a₂^2*W.a₄^2 - 64*W.a₄^3 - 432*W.a₆^2
        + 288*W.a₂*W.a₄*W.a₆ := by
      simp only [WeierstrassCurve.Δ, WeierstrassCurve.b₂, WeierstrassCurve.b₄,
        WeierstrassCurve.b₆, WeierstrassCurve.b₈, ha₁, ha₃]
      ring
    rw [hb]
    linear_combination (-32*W.a₂^3*W.a₆ + 8*W.a₂^2*W.a₄^2 - 32*W.a₄^3 - 216*W.a₆^2
      + 144*W.a₂*W.a₄*W.a₆) * h2
  exact W.isUnit_Δ.ne_zero hΔ

end

end S_WeierstrassProjModel_kw_lrChart_negY_gen_ne_zero
end P2MW
export P2MW.S_WeierstrassProjModel_kw_lrChart_negY_gen_ne_zero (solution)
