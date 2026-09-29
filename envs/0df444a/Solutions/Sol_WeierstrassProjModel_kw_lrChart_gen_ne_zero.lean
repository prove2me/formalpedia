-- Prove2me | solution 1 for WeierstrassProjModel.kw_lrChart_gen_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.822295+00:00
-- url     : https://prove2.me/submissions/27ed8b31-3a53-5663-a1e3-f22c093afc8e

import Definitions.Def_WeierstrassCurve_ProjModel_GroupLawVocabulary
import Mathlib.RingTheory.Localization.Away.Basic
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_WeierstrassProjModel_kw_lrChart_gen_ne_zero

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

theorem aux_not_X_dvd_polynomial [Nontrivial R] (i : Fin 3) :
    ¬ (X i : MvPolynomial (Fin 3) R) ∣ W.toProjective.polynomial := by
  obtain ⟨S, _, _, φ, hφX, hφW⟩ : ∃ (S : Type u), ∃ (_ : CommRing S), ∃ (_ : Nontrivial S),
      ∃ (φ : MvPolynomial (Fin 3) R →+* S),
        φ (X i) = 0 ∧ φ W.toProjective.polynomial ≠ 0 := by
    fin_cases i
    · refine ⟨Polynomial R, inferInstance, inferInstance,
        MvPolynomial.eval₂Hom Polynomial.C ![(0 : Polynomial R), Polynomial.X, 1],
        by simp, ?_⟩
      rw [WeierstrassCurve.Projective.polynomial]; simp
      intro h
      have hc := congrArg (Polynomial.coeff · 2) h
      simp [Polynomial.coeff_X_pow] at hc
    · exact ⟨R, inferInstance, inferInstance, MvPolynomial.eval ![(1:R),0,0],
        by simp, by rw [WeierstrassCurve.Projective.polynomial]; simp⟩
    · exact ⟨R, inferInstance, inferInstance, MvPolynomial.eval ![(1:R),0,0],
        by simp, by rw [WeierstrassCurve.Projective.polynomial]; simp⟩
  intro hd
  exact hφW (zero_dvd_iff.mp (hφX ▸ map_dvd φ hd))

theorem aux_not_isUnit_polynomial [Nontrivial R] :
    ¬ IsUnit W.toProjective.polynomial := fun hu => by
  have h := (MvPolynomial.eval ![(0:R),1,0]).isUnit_map hu
  rw [show eval ![(0:R),1,0] W.toProjective.polynomial = 0 from by
    rw [WeierstrassCurve.Projective.polynomial]; simp] at h
  exact not_isUnit_zero h

theorem aux_isUnit_of_dvd_X_pow {S : Type*} [CommRing S] [IsDomain S] {σ : Type*}
    (i : σ) (q : MvPolynomial σ S) (hnd : ¬ (X i : MvPolynomial σ S) ∣ q) :
    ∀ n, q ∣ (X i) ^ n → IsUnit q := by
  intro n
  induction n with
  | zero => intro hd; rw [pow_zero] at hd; exact isUnit_of_dvd_one hd
  | succ n ih =>
    rintro ⟨f, hf⟩
    have hXf : (X i : MvPolynomial σ S) ∣ f :=
      ((MvPolynomial.X_prime (i := i)).dvd_mul.mp
        (hf ▸ dvd_pow_self (X i) n.succ_ne_zero)).resolve_left hnd
    obtain ⟨g, rfl⟩ := hXf
    refine ih ⟨g, mul_left_cancel₀ (MvPolynomial.X_ne_zero i) ?_⟩
    rw [pow_succ'] at hf
    linear_combination hf

theorem aux_isUnit_of_dvd_X_mul_X_pow {S : Type*} [CommRing S] [IsDomain S] {σ : Type*}
    (i m : σ) (q : MvPolynomial σ S)
    (hi : ¬ (X i : MvPolynomial σ S) ∣ q) (hm : ¬ (X m : MvPolynomial σ S) ∣ q) :
    ∀ n, q ∣ X m * (X i) ^ n → IsUnit q := by
  intro n
  induction n with
  | zero =>
    intro hd; rw [pow_zero, mul_one] at hd
    exact aux_isUnit_of_dvd_X_pow m q hm 1 (by rw [pow_one]; exact hd)
  | succ n ih =>
    rintro ⟨f, hf⟩
    have hXf : (X i : MvPolynomial σ S) ∣ f :=
      ((MvPolynomial.X_prime (i := i)).dvd_mul.mp
        (hf ▸ Dvd.intro (X m * X i ^ n) (by ring))).resolve_left hi
    obtain ⟨g, rfl⟩ := hXf
    refine ih ⟨g, mul_left_cancel₀ (MvPolynomial.X_ne_zero i) ?_⟩
    rw [pow_succ] at hf
    linear_combination hf

theorem solution [IsDomain R] [IsNoetherianRing R] [W.IsElliptic] (i m : Fin 3) :
    kw_lrChart_gen W i m ≠ 0 := by
  intro h

  have hval := congrArg
    (algebraMap (𝒜 i) (Localization.Away (mk₃ (X i : MvPolynomial (Fin 3) R)))) h
  rw [map_zero, HomogeneousLocalization.algebraMap_apply, kw_lrChart_gen_val,
    Localization.mk_eq_mk', IsLocalization.mk'_eq_zero_iff] at hval

  obtain ⟨⟨_, n, rfl⟩, hn⟩ := hval

  simp only at hn
  rw [← map_pow, ← map_mul, Ideal.Quotient.eq_zero_iff_mem,
    projModelHomogeneousIdealCR_toIdeal, Ideal.mem_span_singleton] at hn

  exact aux_not_isUnit_polynomial W
    (aux_isUnit_of_dvd_X_mul_X_pow i m W.toProjective.polynomial
      (aux_not_X_dvd_polynomial W i) (aux_not_X_dvd_polynomial W m) n
      (by rw [mul_comm]; exact hn))

end

end S_WeierstrassProjModel_kw_lrChart_gen_ne_zero
end P2MW
export P2MW.S_WeierstrassProjModel_kw_lrChart_gen_ne_zero (solution)
