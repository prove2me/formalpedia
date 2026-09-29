-- Prove2me | solution 1 for WeierstrassProjModel.kw_lr_chartTensor_genProd_ne_genTensOne_xzCase
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.822295+00:00
-- url     : https://prove2.me/submissions/b05a3bf9-606a-56fd-acbb-a3f058b407d9

import Definitions.Def_WeierstrassCurve_ProjModel_GroupLawVocabulary
import Mathlib.RingTheory.Localization.Away.Basic
import Mathlib.Algebra.Polynomial.Degree.Operations
import Mathlib.RingTheory.TensorProduct.Basic
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_WeierstrassProjModel_kw_lr_chartTensor_genProd_ne_genTensOne_xzCase

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

set_option quotPrecheck false in
local notation "ℬ" => MvPolynomial (Fin 3) R ⧸ (projModelHomogeneousIdealCR W.toProjective).toIdeal

set_option quotPrecheck false in
local notation "S₀₂" => Localization.Away
  (Ideal.Quotient.mk (projModelHomogeneousIdealCR W.toProjective).toIdeal
    (X 0 * X 2 : MvPolynomial (Fin 3) R))

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

theorem aux_cancel_X [IsDomain R] (i : Fin 3) (M : MvPolynomial (Fin 3) R) :
    ∀ n, W.toProjective.polynomial ∣ (X i)^n * M → W.toProjective.polynomial ∣ M := by
  intro n
  induction n with
  | zero => rw [pow_zero, one_mul]; exact id
  | succ n ih =>
    rintro ⟨f, hf⟩
    have hXf : (X i : MvPolynomial (Fin 3) R) ∣ f :=
      ((MvPolynomial.X_prime (i := i)).dvd_mul.mp
        ⟨(X i)^n * M, by rw [← hf]; ring⟩).resolve_left (aux_not_X_dvd_polynomial W i)
    obtain ⟨g, rfl⟩ := hXf
    refine ih ⟨g, mul_left_cancel₀ (MvPolynomial.X_ne_zero i) ?_⟩
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

theorem aux_not_dvd_L [IsDomain R] [W.IsElliptic] :
    ¬ W.toProjective.polynomial ∣ (C 2 * X 1 + C W.a₁ * X 0 + C W.a₃ * X 2
      : MvPolynomial (Fin 3) R) := by
  intro hdvd

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
    show (MvPolynomial.eval₂Hom Polynomial.C ![(0:Polynomial R), Polynomial.X, 1])
        (C 2 * X 1 + C W.a₁ * X 0 + C W.a₃ * X 2 : MvPolynomial (Fin 3) R)
      = Polynomial.C (2:R) * Polynomial.X + Polynomial.C W.a₃ from by
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
    show (MvPolynomial.eval₂Hom Polynomial.C ![Polynomial.X, (0:Polynomial R), 0])
        (C 2 * X 1 + C W.a₁ * X 0 + C W.a₃ * X 2 : MvPolynomial (Fin 3) R)
      = Polynomial.C W.a₁ * Polynomial.X from by
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

theorem aux_isUnit_mkX (m : Fin 3) (hm : m ≠ 1) :
    IsUnit (algebraMap ℬ S₀₂ (mk₃ (X m : MvPolynomial (Fin 3) R))) := by
  have h02 : IsUnit (algebraMap ℬ S₀₂ (mk₃ (X 0 * X 2 : MvPolynomial (Fin 3) R))) :=
    IsLocalization.Away.algebraMap_isUnit _
  rw [map_mul, map_mul] at h02
  fin_cases m
  · exact isUnit_of_mul_isUnit_left h02
  · exact absurd rfl hm
  · exact isUnit_of_mul_isUnit_right h02

def auxPlain (m : Fin 3) (hm : m ≠ 1) : (𝒜 m) →+* S₀₂ :=
  (IsLocalization.Away.lift (mk₃ (X m : MvPolynomial (Fin 3) R))
      (g := algebraMap ℬ S₀₂) (aux_isUnit_mkX W m hm)).comp
    (algebraMap (𝒜 m) (Localization.Away (mk₃ (X m : MvPolynomial (Fin 3) R))))

theorem auxPlain_gen (m : Fin 3) (hm : m ≠ 1) (k : Fin 3) :
    algebraMap ℬ S₀₂ (mk₃ (X k : MvPolynomial (Fin 3) R))
      = algebraMap ℬ S₀₂ (mk₃ (X m : MvPolynomial (Fin 3) R))
        * auxPlain W m hm (kw_lrChart_gen W m k) := by
  rw [auxPlain, RingHom.comp_apply, HomogeneousLocalization.algebraMap_apply,
    kw_lrChart_gen_val, Localization.mk_eq_mk', IsLocalization.Away.lift]
  exact (IsLocalization.lift_mk'_spec _ _ _ _).mp rfl

theorem auxPlain_algebraMap (m : Fin 3) (hm : m ≠ 1) (r : R) :
    auxPlain W m hm (algebraMap R (𝒜 m) r) = algebraMap R S₀₂ r := by
  rw [auxPlain, RingHom.comp_apply, HomogeneousLocalization.algebraMap_apply,
    show algebraMap R (𝒜 m) r = kw_lrChart_dehom W m (C r) from
      (aeval_C (kw_lrChart_gen W m) r).symm,
    kw_lrChart_dehom_C_val, Localization.mk_one_eq_algebraMap, IsLocalization.Away.lift,
    IsLocalization.lift_eq, IsScalarTower.algebraMap_apply R ℬ S₀₂]
  rfl

theorem aux_negQuotHom_mk (p : MvPolynomial (Fin 3) R) :
    kw_lrAddNegDiag_negQuotHom W (mk₃ p) = mk₃ (kw_lrAddNegDiag_negSubst W p) :=
  Ideal.Quotient.lift_mk _ _ _

theorem aux_negQuotHom_mkX (m : Fin 3) (hm : m ≠ 1) :
    kw_lrAddNegDiag_negQuotHom W (mk₃ (X m : MvPolynomial (Fin 3) R))
      = mk₃ (X m : MvPolynomial (Fin 3) R) := by
  rw [aux_negQuotHom_mk, kw_lrAddNegDiag_negSubst, aeval_X]
  fin_cases m
  · rfl
  · exact absurd rfl hm
  · rfl

def auxNeg (m : Fin 3) (hm : m ≠ 1) : (𝒜 m) →+* S₀₂ :=
  (IsLocalization.Away.lift (mk₃ (X m : MvPolynomial (Fin 3) R))
      (g := (algebraMap ℬ S₀₂).comp (kw_lrAddNegDiag_negQuotHom W))
      (by rw [RingHom.comp_apply, aux_negQuotHom_mkX W m hm]; exact aux_isUnit_mkX W m hm)).comp
    (algebraMap (𝒜 m) (Localization.Away (mk₃ (X m : MvPolynomial (Fin 3) R))))

theorem auxNeg_gen (m : Fin 3) (hm : m ≠ 1) (k : Fin 3) :
    algebraMap ℬ S₀₂ (mk₃ (kw_lrAddNegDiag_negSubstGen W k))
      = algebraMap ℬ S₀₂ (mk₃ (X m : MvPolynomial (Fin 3) R))
        * auxNeg W m hm (kw_lrChart_gen W m k) := by
  have h : ((algebraMap ℬ S₀₂).comp (kw_lrAddNegDiag_negQuotHom W))
        (mk₃ (X k : MvPolynomial (Fin 3) R))
      = ((algebraMap ℬ S₀₂).comp (kw_lrAddNegDiag_negQuotHom W))
          (mk₃ (X m : MvPolynomial (Fin 3) R))
        * auxNeg W m hm (kw_lrChart_gen W m k) := by
    simp only [auxNeg, RingHom.coe_comp, Function.comp_apply,
      HomogeneousLocalization.algebraMap_apply, kw_lrChart_gen_val, Localization.mk_eq_mk']
    exact (IsLocalization.lift_mk'_spec
      (M := Submonoid.powers (mk₃ (X m : MvPolynomial (Fin 3) R)))
      (S := Localization.Away (mk₃ (X m : MvPolynomial (Fin 3) R)))
      (g := (algebraMap ℬ S₀₂).comp (kw_lrAddNegDiag_negQuotHom W)) _ _ _ _).mp rfl
  rw [RingHom.comp_apply, RingHom.comp_apply, aux_negQuotHom_mkX W m hm,
    aux_negQuotHom_mk, kw_lrAddNegDiag_negSubst, aeval_X] at h
  exact h

theorem auxNeg_algebraMap (m : Fin 3) (hm : m ≠ 1) (r : R) :
    auxNeg W m hm (algebraMap R (𝒜 m) r) = algebraMap R S₀₂ r := by
  rw [auxNeg, RingHom.comp_apply, HomogeneousLocalization.algebraMap_apply,
    show algebraMap R (𝒜 m) r = kw_lrChart_dehom W m (C r) from
      (aeval_C (kw_lrChart_gen W m) r).symm,
    kw_lrChart_dehom_C_val, Localization.mk_one_eq_algebraMap, IsLocalization.Away.lift,
    IsLocalization.lift_eq, RingHom.comp_apply, aux_negQuotHom_mk, kw_lrAddNegDiag_negSubst,
    aeval_C, IsScalarTower.algebraMap_apply R ℬ S₀₂]
  rfl

theorem solution [IsDomain R] [IsNoetherianRing R] [W.IsElliptic] (i j : Fin 3)
    (hi : i ≠ 1) (hj : j ≠ 1) :
    ∃ k : Fin 3, (kw_lrChart_gen W i j : (𝒜 i)) ⊗ₜ[R] (kw_lrChart_gen W j k : (𝒜 j))
      ≠ (kw_lrChart_gen W i k) ⊗ₜ[R] (1 : (𝒜 j)) := by
  refine ⟨1, fun heq => ?_⟩
  let f : (𝒜 i) →ₐ[R] S₀₂ := { auxPlain W i hi with commutes' := auxPlain_algebraMap W i hi }
  let g : (𝒜 j) →ₐ[R] S₀₂ := { auxNeg W j hj with commutes' := auxNeg_algebraMap W j hj }
  have hφ := congrArg (Algebra.TensorProduct.productMap f g) heq
  rw [Algebra.TensorProduct.productMap_apply_tmul, Algebra.TensorProduct.productMap_apply_tmul,
    map_one, mul_one] at hφ
  change auxPlain W i hi (kw_lrChart_gen W i j) * auxNeg W j hj (kw_lrChart_gen W j 1)
    = auxPlain W i hi (kw_lrChart_gen W i 1) at hφ
  have hA := auxPlain_gen W i hi j
  have hB := auxNeg_gen W j hj 1
  have hC := auxPlain_gen W i hi 1

  have key : algebraMap ℬ S₀₂ (mk₃ (X 1 : MvPolynomial (Fin 3) R))
      = algebraMap ℬ S₀₂ (mk₃ (kw_lrAddNegDiag_negSubstGen W 1)) := by
    linear_combination hC - hB - (auxNeg W j hj (kw_lrChart_gen W j 1)) * hA
      - (algebraMap ℬ S₀₂ (mk₃ (X i : MvPolynomial (Fin 3) R))) * hφ
  rw [← sub_eq_zero, ← map_sub, ← map_sub,
    show (X 1 : MvPolynomial (Fin 3) R) - kw_lrAddNegDiag_negSubstGen W 1
      = C 2 * X 1 + C W.a₁ * X 0 + C W.a₃ * X 2 from by
        show (X 1 : MvPolynomial (Fin 3) R) - (-X 1 - C W.a₁ * X 0 - C W.a₃ * X 2) = _
        rw [map_ofNat]; ring,
    IsLocalization.map_eq_zero_iff
      (Submonoid.powers (mk₃ (X 0 * X 2 : MvPolynomial (Fin 3) R))) S₀₂] at key
  obtain ⟨⟨_, n, rfl⟩, hn⟩ := key
  simp only at hn
  rw [← map_pow, ← map_mul, Ideal.Quotient.eq_zero_iff_mem,
    projModelHomogeneousIdealCR_toIdeal, Ideal.mem_span_singleton, mul_pow, mul_assoc] at hn
  exact aux_not_dvd_L W (aux_cancel_X W 2 _ n (aux_cancel_X W 0 _ n hn))

end

end S_WeierstrassProjModel_kw_lr_chartTensor_genProd_ne_genTensOne_xzCase
end P2MW
export P2MW.S_WeierstrassProjModel_kw_lr_chartTensor_genProd_ne_genTensOne_xzCase (solution)
