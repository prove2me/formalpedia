-- Prove2me | solution 1 for WeierstrassCurve.exists_variableChange_smul_eq_of_functionField_algEquiv
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.822295+00:00
-- url     : https://prove2.me/submissions/c1570c01-adfb-57d0-806d-fe8e263212cf

import Mathlib
import Definitions.Def_WeierstrassCurve_FunctionFieldQuadratic
import Definitions.Def_EllipticCurve_ValuationInfty
import Definitions.Def_WeierstrassCurve_VariableChangePointEquiv
import Theorems.Thm_WeierstrassCurve_Affine_FunctionField_eq_valuationSubring_of_X_not_mem
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_WeierstrassCurve_exists_variableChange_smul_eq_of_functionField_algEquiv

set_option autoImplicit false

noncomputable section

p2m_open "Polynomial WeierstrassCurve P2MW.S_WeierstrassCurve_exists_variableChange_smul_eq_of_functionField_algEquiv.WeierstrassCurve WeierstrassCurve.Affine"
open scoped Polynomial.Bivariate

namespace WeierstrassCurve
p2m_export "WeierstrassCurve" "Affine VariableChange.map a₃ a₁ map Affine.CoordinateRing mk a₄ a₂ a₆ toAffine Affine.CoordinateRing.mk map_a₆ map_a₁ map_a₄ VariableChange map_a₂ map_variableChange map_a₃ Affine.valuationInfty"
namespace B2a
p2m_open "WeierstrassCurve"

theorem valuation_eq_of_valuationSubring_eq {L : Type*} [Field L]
    (v w : Valuation L (WithZero (Multiplicative ℤ)))
    (h : v.valuationSubring = w.valuationSubring)
    (hv : Function.Surjective v) (hw : Function.Surjective w) : v = w := by
  have he : v.IsEquiv w := (Valuation.isEquiv_iff_valuationSubring v w).mpr h

  obtain ⟨π, hπ⟩ := hv (WithZero.exp 1)
  have hπ0 : π ≠ 0 := by
    rintro rfl
    rw [map_zero] at hπ
    exact WithZero.zero_ne_coe hπ

  have hwπ0 : w π ≠ 0 := (Valuation.ne_zero_iff w).mpr hπ0
  have hwπgt : 1 < w π := by
    have h1 : ¬ v π ≤ v 1 := by rw [hπ, map_one]; decide
    have h2 : ¬ w π ≤ w 1 := fun hle => h1 ((he π 1).mpr hle)
    rw [map_one] at h2
    exact lt_of_not_ge h2
  have hwπ : w π = WithZero.exp 1 := by
    obtain ⟨m, hm⟩ : ∃ m : ℤ, w π = WithZero.exp m := ⟨WithZero.log (w π), (WithZero.exp_log hwπ0).symm⟩
    rw [hm] at hwπgt ⊢
    have hm1 : 1 ≤ m := by
      rw [← WithZero.exp_zero, WithZero.exp_lt_exp] at hwπgt
      omega
    rcases hm1.lt_or_eq with hlt | heq
    ·
      exfalso
      obtain ⟨y, hy⟩ := hw (WithZero.exp 1)
      have hy0 : y ≠ 0 := by
        rintro rfl
        rw [map_zero] at hy
        exact WithZero.zero_ne_coe hy
      have hvy0 : v y ≠ 0 := (Valuation.ne_zero_iff v).mpr hy0
      have h1 : v 1 < v y := by
        have : w 1 < w y := by rw [map_one, hy, ← WithZero.exp_zero, WithZero.exp_lt_exp]; omega
        have h' : ¬ w y ≤ w 1 := not_le.mpr this
        have h'' : ¬ v y ≤ v 1 := fun hle => h' ((he y 1).mp hle)
        exact lt_of_not_ge h''
      have h2 : v y < v π := by
        have : w y < w π := by rw [hy, hm, WithZero.exp_lt_exp]; exact hlt
        have h' : ¬ w π ≤ w y := not_le.mpr this
        have h'' : ¬ v π ≤ v y := fun hle => h' ((he π y).mp hle)
        exact lt_of_not_ge h''
      rw [map_one] at h1
      rw [hπ] at h2
      obtain ⟨k, hk⟩ : ∃ k : ℤ, v y = WithZero.exp k := ⟨WithZero.log (v y), (WithZero.exp_log hvy0).symm⟩
      rw [hk, ← WithZero.exp_zero, WithZero.exp_lt_exp] at h1
      rw [hk, WithZero.exp_lt_exp] at h2
      omega
    · rw [heq]

  ext x
  rcases eq_or_ne x 0 with rfl | hx
  · rw [map_zero, map_zero]
  have hvx0 : v x ≠ 0 := (Valuation.ne_zero_iff v).mpr hx
  obtain ⟨n, hn⟩ : ∃ n : ℤ, v x = WithZero.exp n := ⟨WithZero.log (v x), (WithZero.exp_log hvx0).symm⟩
  have hvxn : v x = v (π ^ n) := by
    rw [map_zpow₀, hπ, ← WithZero.exp_zsmul, smul_eq_mul, mul_one, hn]
  have hwxn : w x = w (π ^ n) := (he.val_eq).mp hvxn
  rw [hwxn, map_zpow₀, hwπ, ← WithZero.exp_zsmul, smul_eq_mul, mul_one, hn]

variable {F : Type*} [Field F]

abbrev xf (W : WeierstrassCurve F) : W.toAffine.FunctionField :=
  algebraMap W.toAffine.CoordinateRing W.toAffine.FunctionField (CoordinateRing.mk W.toAffine (C X))

theorem xf_eq_polyToFunctionField (W : WeierstrassCurve F) : xf W = polyToFunctionField W.toAffine X := rfl

theorem valuationInfty_algebraMap_const (W : WeierstrassCurve F) (c : F) :
    valuationInfty W.toAffine (algebraMap F W.toAffine.FunctionField c) ≤ 1 := by
  rcases eq_or_ne c 0 with rfl | hc
  · rw [map_zero, map_zero]; exact zero_le_one
  · have h : algebraMap F W.toAffine.FunctionField c =
        algebraMap W.toAffine.CoordinateRing W.toAffine.FunctionField (CoordinateRing.mk W.toAffine (C (C c))) := by
      rw [← polyToFunctionField_C]; rfl
    have hne : CoordinateRing.mk W.toAffine (C (C c)) ≠ 0 := by
      rw [show CoordinateRing.mk W.toAffine (C (C c)) = algebraMap F W.toAffine.CoordinateRing c from rfl]
      exact (map_ne_zero_iff _ (FaithfulSMul.algebraMap_injective F W.toAffine.CoordinateRing)).mpr hc
    rw [h, valuationInfty_algebraMap_of_ne_zero _ hne, CoordinateRing.natDegree_norm_mk_C, natDegree_C,
      mul_zero, Nat.cast_zero, WithZero.exp_zero]

variable {W₁ W₂ : WeierstrassCurve F}
  (e : W₂.toAffine.FunctionField ≃ₐ[F] W₁.toAffine.FunctionField)

abbrev vPull : Valuation W₂.toAffine.FunctionField (WithZero (Multiplicative ℤ)) :=
  (valuationInfty W₁.toAffine).comap (e : W₂.toAffine.FunctionField →+* W₁.toAffine.FunctionField)

theorem vPull_apply (y : W₂.toAffine.FunctionField) : vPull e y = valuationInfty W₁.toAffine (e y) := rfl

variable (hinf : ¬ valuationInfty W₁.toAffine (e (xf W₂)) ≤ 1)
include hinf

theorem vPull_eq : vPull e = valuationInfty W₂.toAffine := by
  refine valuation_eq_of_valuationSubring_eq _ _ ?_ ?_ (valuationInfty_surjective _)
  · refine FunctionField.eq_valuationSubring_of_X_not_mem W₂ (vPull e).valuationSubring ?_ ?_
      (valuationInfty W₂.toAffine) (fun f hf => valuationInfty_algebraMap_of_ne_zero _ hf)
    · intro c
      rw [Valuation.mem_valuationSubring_iff, vPull_apply, AlgEquiv.commutes]
      exact valuationInfty_algebraMap_const W₁ c
    · rw [Valuation.mem_valuationSubring_iff]
      exact hinf
  · intro γ
    obtain ⟨z, hz⟩ := valuationInfty_surjective W₁.toAffine γ
    exact ⟨e.symm z, by rw [vPull_apply, AlgEquiv.apply_symm_apply, hz]⟩

theorem valuationInfty_apply (y : W₂.toAffine.FunctionField) :
    valuationInfty W₁.toAffine (e y) = valuationInfty W₂.toAffine y := by
  rw [← vPull_apply, vPull_eq e hinf]

omit hinf in

theorem val_Y_le_one_of_val_X_le_one
    (u : Valuation W₂.toAffine.FunctionField (WithZero (Multiplicative ℤ)))
    (hc : ∀ c : F, u (algebraMap F W₂.toAffine.FunctionField c) ≤ 1)
    (hX : u (xf W₂) ≤ 1) : u (yCoord W₂.toAffine) ≤ 1 := by
  by_contra hY
  rw [not_le] at hY
  have hrel := yCoord_relation (W := W₂.toAffine)

  have hpoly : ∀ p : F[X], u (polyToFunctionField W₂.toAffine p) ≤ 1 := by
    intro p
    induction p using Polynomial.induction_on' with
    | add p q hp hq => rw [map_add]; exact (u.map_add _ _).trans (max_le hp hq)
    | monomial n a =>
      rw [← C_mul_X_pow_eq_monomial, map_mul, map_pow, polyToFunctionField_C, map_mul, map_pow]
      exact mul_le_one' (hc a) (pow_le_one' hX n)
  have h1 : u (yCoord W₂.toAffine * yCoord W₂.toAffine) = u (yCoord W₂.toAffine) * u (yCoord W₂.toAffine) :=
    map_mul _ _ _
  have h2 : u (polyToFunctionField W₂.toAffine (X ^ 3 + C W₂.a₂ * X ^ 2 + C W₂.a₄ * X + C W₂.a₆) -
      polyToFunctionField W₂.toAffine (C W₂.a₁ * X + C W₂.a₃) * yCoord W₂.toAffine) <
      u (yCoord W₂.toAffine) * u (yCoord W₂.toAffine) := by
    refine lt_of_le_of_lt (u.map_sub _ _) (max_lt ?_ ?_)
    · exact lt_of_le_of_lt (hpoly _) (one_lt_mul'' hY hY)
    · rw [map_mul]
      have hY0 : u (yCoord W₂.toAffine) ≠ 0 := ne_of_gt (lt_trans zero_lt_one hY)
      obtain ⟨n, hn⟩ : ∃ n : ℤ, u (yCoord W₂.toAffine) = WithZero.exp n :=
        ⟨WithZero.log _, (WithZero.exp_log hY0).symm⟩
      have hn0 : 0 < n := by rw [hn, ← WithZero.exp_zero, WithZero.exp_lt_exp] at hY; exact hY
      calc u (polyToFunctionField W₂.toAffine (C W₂.a₁ * X + C W₂.a₃)) * u (yCoord W₂.toAffine)
          ≤ 1 * u (yCoord W₂.toAffine) := mul_le_mul_left (hpoly _) _
        _ = u (yCoord W₂.toAffine) := one_mul _
        _ < u (yCoord W₂.toAffine) * u (yCoord W₂.toAffine) := by
          rw [hn, ← WithZero.exp_add, WithZero.exp_lt_exp]; omega
  rw [← hrel, h1] at h2
  exact lt_irrefl _ h2

theorem exists_lift [IsDedekindDomain W₁.toAffine.CoordinateRing] (f : W₂.toAffine.CoordinateRing) :
    ∃ a : W₁.toAffine.CoordinateRing,
      algebraMap W₁.toAffine.CoordinateRing W₁.toAffine.FunctionField a =
        e (algebraMap W₂.toAffine.CoordinateRing W₂.toAffine.FunctionField f) := by
  have key : e (algebraMap W₂.toAffine.CoordinateRing W₂.toAffine.FunctionField f) ∈
      (algebraMap W₁.toAffine.CoordinateRing W₁.toAffine.FunctionField).range := by
    refine IsDedekindDomain.HeightOneSpectrum.mem_integers_of_valuation_le_one _ _ (fun w => ?_)
    let u : Valuation W₂.toAffine.FunctionField (WithZero (Multiplicative ℤ)) :=
      (w.valuation W₁.toAffine.FunctionField).comap
        (e : W₂.toAffine.FunctionField →+* W₁.toAffine.FunctionField)
    have hu : ∀ y, u y = w.valuation W₁.toAffine.FunctionField (e y) := fun y => rfl
    have hc : ∀ c : F, u (algebraMap F W₂.toAffine.FunctionField c) ≤ 1 := by
      intro c
      rw [hu, AlgEquiv.commutes, IsScalarTower.algebraMap_apply F W₁.toAffine.CoordinateRing W₁.toAffine.FunctionField]
      exact w.valuation_le_one _

    have hX : u (xf W₂) ≤ 1 := by
      by_contra hX
      have hO := FunctionField.eq_valuationSubring_of_X_not_mem W₂ u.valuationSubring
        (fun c => by rw [Valuation.mem_valuationSubring_iff]; exact hc c)
        (by rw [Valuation.mem_valuationSubring_iff]; exact hX)
        (valuationInfty W₂.toAffine) (fun f hf => valuationInfty_algebraMap_of_ne_zero _ hf)
      have h1 : e.symm (xf W₁) ∈ u.valuationSubring := by
        rw [Valuation.mem_valuationSubring_iff, hu, AlgEquiv.apply_symm_apply]
        exact w.valuation_le_one _
      rw [hO, Valuation.mem_valuationSubring_iff, ← valuationInfty_apply e hinf, AlgEquiv.apply_symm_apply,
        valuationInfty_X] at h1
      exact absurd h1 (by decide)
    have hY : u (yCoord W₂.toAffine) ≤ 1 := val_Y_le_one_of_val_X_le_one u hc hX
    obtain ⟨p, q, hpq⟩ := CoordinateRing.exists_smul_basis_eq f
    rw [← hu, ← hpq, algebraMap_smul_basis]
    have hpoly : ∀ p : F[X], u (polyToFunctionField W₂.toAffine p) ≤ 1 := by
      intro p
      induction p using Polynomial.induction_on' with
      | add p q hp hq => rw [map_add]; exact (u.map_add _ _).trans (max_le hp hq)
      | monomial n a =>
        rw [← C_mul_X_pow_eq_monomial, map_mul, map_pow, polyToFunctionField_C, map_mul, map_pow]
        exact mul_le_one' (hc a) (pow_le_one' hX n)
    refine (u.map_add _ _).trans (max_le (hpoly p) ?_)
    rw [map_mul]
    exact mul_le_one' (hpoly q) hY
  obtain ⟨a, ha⟩ := key
  exact ⟨a, ha⟩

theorem natDegree_norm_lift {f : W₂.toAffine.CoordinateRing} (hf : f ≠ 0) {a : W₁.toAffine.CoordinateRing}
    (ha : algebraMap W₁.toAffine.CoordinateRing W₁.toAffine.FunctionField a =
        e (algebraMap W₂.toAffine.CoordinateRing W₂.toAffine.FunctionField f)) :
    a ≠ 0 ∧ (Algebra.norm F[X] a).natDegree = (Algebra.norm F[X] f).natDegree := by
  have ha0 : a ≠ 0 := by
    rintro rfl
    rw [map_zero, eq_comm, EmbeddingLike.map_eq_zero_iff,
      map_eq_zero_iff _ (IsFractionRing.injective W₂.toAffine.CoordinateRing W₂.toAffine.FunctionField)] at ha
    exact hf ha
  refine ⟨ha0, ?_⟩
  have h := valuationInfty_apply e hinf (algebraMap W₂.toAffine.CoordinateRing W₂.toAffine.FunctionField f)
  rw [← ha, valuationInfty_algebraMap_of_ne_zero _ ha0, valuationInfty_algebraMap_of_ne_zero _ hf,
    WithZero.exp_inj, Nat.cast_inj] at h
  exact h

end WeierstrassCurve.B2a

namespace WeierstrassCurve
p2m_export "WeierstrassCurve" "Affine VariableChange.map a₃ a₁ map Affine.CoordinateRing mk a₄ a₂ a₆ toAffine Affine.CoordinateRing.mk map_a₆ map_a₁ map_a₄ VariableChange map_a₂ map_variableChange map_a₃ Affine.valuationInfty"
namespace B2a
p2m_open "WeierstrassCurve"

variable {F : Type*} [Field F] {W₁ W₂ : WeierstrassCurve F}
  (e : W₂.toAffine.FunctionField ≃ₐ[F] W₁.toAffine.FunctionField)
  (hinf : ¬ valuationInfty W₁.toAffine (e (xf W₂)) ≤ 1)
include hinf

theorem xf_shape [IsDedekindDomain W₁.toAffine.CoordinateRing] :
    ∃ u' r : F, u' ≠ 0 ∧ e (xf W₂) = algebraMap F _ u' * xf W₁ + algebraMap F _ r := by
  have hX0 : CoordinateRing.mk W₂.toAffine (C X) ≠ 0 := by
    simpa [CoordinateRing.XClass] using CoordinateRing.XClass_ne_zero (W' := W₂.toAffine) 0
  obtain ⟨aX, haX⟩ := exists_lift e hinf (CoordinateRing.mk W₂.toAffine (C X))
  obtain ⟨haX0, hnd⟩ := natDegree_norm_lift e hinf hX0 haX
  rw [CoordinateRing.natDegree_norm_mk_C, natDegree_X, mul_one] at hnd
  obtain ⟨p, q, hpq⟩ := CoordinateRing.exists_smul_basis_eq aX
  have hq0 : q = 0 := by
    by_contra hq
    have := CoordinateRing.natDegree_norm_smul_basis_of_ne_zero W₁.toAffine p q hq
    rw [hpq, hnd] at this
    omega
  subst hq0
  have hdegp : p.natDegree = 1 := by
    have := CoordinateRing.natDegree_norm_smul_basis_of_eq_zero W₁.toAffine p
    rw [hpq, hnd] at this
    omega
  refine ⟨p.coeff 1, p.coeff 0, ?_, ?_⟩
  · intro hc
    have hp0 : p ≠ 0 := by rintro rfl; simp at hdegp
    exact hp0 (Polynomial.leadingCoeff_eq_zero.mp (by rw [Polynomial.leadingCoeff, hdegp]; exact hc))
  · have hpdecomp : p = C (p.coeff 1) * X + C (p.coeff 0) :=
      (Polynomial.eq_X_add_C_of_natDegree_le_one hdegp.le).trans (by ring)
    show e (algebraMap _ _ _) = _
    rw [← haX, ← hpq, algebraMap_smul_basis, map_zero, zero_mul, add_zero]
    conv_lhs => rw [hpdecomp]
    rw [map_add, map_mul, polyToFunctionField_C, polyToFunctionField_C]
    rfl

theorem yf_shape [IsDedekindDomain W₁.toAffine.CoordinateRing] :
    ∃ v s' t : F, v ≠ 0 ∧ e (yCoord W₂.toAffine) =
      algebraMap F _ v * yCoord W₁.toAffine + algebraMap F _ s' * xf W₁ + algebraMap F _ t := by
  obtain ⟨aY, haY⟩ := exists_lift e hinf (CoordinateRing.mk W₂.toAffine Y)
  obtain ⟨haY0, hnd⟩ := natDegree_norm_lift e hinf (CoordinateRing.mk_Y_ne_zero W₂.toAffine) haY
  rw [CoordinateRing.natDegree_norm_mk_Y] at hnd
  obtain ⟨p, q, hpq⟩ := CoordinateRing.exists_smul_basis_eq aY
  have hq0 : q ≠ 0 := by
    rintro rfl
    have := CoordinateRing.natDegree_norm_smul_basis_of_eq_zero W₁.toAffine p
    rw [hpq, hnd] at this
    omega
  have hmax := CoordinateRing.natDegree_norm_smul_basis_of_ne_zero W₁.toAffine p q hq0
  rw [hpq, hnd] at hmax
  have hdegq : q.natDegree = 0 := by omega
  have hdegp : p.natDegree ≤ 1 := by omega
  refine ⟨q.coeff 0, p.coeff 1, p.coeff 0, ?_, ?_⟩
  · intro hc
    exact hq0 (by rw [Polynomial.eq_C_of_natDegree_eq_zero hdegq, hc, Polynomial.C_0])
  · have hqdecomp : q = C (q.coeff 0) := Polynomial.eq_C_of_natDegree_eq_zero hdegq
    have hpdecomp : p = C (p.coeff 1) * X + C (p.coeff 0) :=
      (Polynomial.eq_X_add_C_of_natDegree_le_one hdegp).trans (by ring)
    show e (algebraMap _ _ _) = _
    rw [← haY, ← hpq, algebraMap_smul_basis]
    conv_lhs => rw [hqdecomp, hpdecomp]
    rw [map_add, map_mul, polyToFunctionField_C, polyToFunctionField_C, polyToFunctionField_C]
    show _ + _ * yCoord W₁.toAffine = _
    rw [show polyToFunctionField W₁.toAffine X = xf W₁ from rfl]
    ring

omit hinf in

theorem equation_generic (W : WeierstrassCurve F) :
    (W.map (algebraMap F W.toAffine.FunctionField)).toAffine.Equation (xf W) (yCoord W.toAffine) := by
  rw [equation_iff]
  simp only [map_a₁, map_a₂, map_a₃, map_a₄, map_a₆]
  have h := yCoord_relation (W := W.toAffine)
  simp only [map_add, map_mul, map_pow, polyToFunctionField_C] at h
  rw [show polyToFunctionField W.toAffine X = xf W from rfl] at h
  linear_combination h

omit hinf in

theorem eq_of_equation_generic {V W : WeierstrassCurve F}
    (h : (V.map (algebraMap F W.toAffine.FunctionField)).toAffine.Equation (xf W) (yCoord W.toAffine)) :
    V = W := by
  have hW := equation_generic W
  rw [equation_iff] at h hW
  simp only [map_a₁, map_a₂, map_a₃, map_a₄, map_a₆] at h hW
  have hdiff : polyToFunctionField W.toAffine
        (C (W.a₂ - V.a₂) * X ^ 2 + C (W.a₄ - V.a₄) * X + C (W.a₆ - V.a₆))
      + polyToFunctionField W.toAffine (C (V.a₁ - W.a₁) * X + C (V.a₃ - W.a₃)) * yCoord W.toAffine = 0 := by
    simp only [map_add, map_mul, map_sub, map_pow, polyToFunctionField_C]
    rw [show polyToFunctionField W.toAffine X = xf W from rfl]
    linear_combination h - hW
  rw [show yCoord W.toAffine = algebraMap W.toAffine.CoordinateRing W.toAffine.FunctionField
      (CoordinateRing.mk W.toAffine Y) from rfl, ← algebraMap_smul_basis] at hdiff
  obtain ⟨hP, hQ⟩ := CoordinateRing.smul_basis_eq_zero
    ((map_eq_zero_iff _ (IsFractionRing.injective W.toAffine.CoordinateRing W.toAffine.FunctionField)).mp hdiff)
  have extract : ∀ (c : F) (n : ℕ), (Polynomial.C c * X ^ n : F[X]).coeff n = c := fun c n => by
    rw [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, if_pos rfl, mul_one]
  have extract0 : ∀ (c : F) (n k : ℕ), k ≠ n → (Polynomial.C c * X ^ n : F[X]).coeff k = 0 :=
    fun c n k hk => by rw [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, if_neg hk, mul_zero]
  refine WeierstrassCurve.ext ?_ ?_ ?_ ?_ ?_
  · have := congrArg (·.coeff 1) hQ
    simp only [pow_one (M := F[X]) X ▸ extract _ 1, Polynomial.coeff_add,
      Polynomial.coeff_C, if_neg one_ne_zero, add_zero, Polynomial.coeff_zero] at this
    exact sub_eq_zero.mp this
  · have := congrArg (·.coeff 2) hP
    simp only [extract _ 2, pow_one (M := F[X]) X ▸ extract0 _ 1 2 (by decide),
      Polynomial.coeff_add, Polynomial.coeff_C, if_neg two_ne_zero, add_zero,
      Polynomial.coeff_zero] at this
    exact (sub_eq_zero.mp this).symm
  · have := congrArg (·.coeff 0) hQ
    simp only [pow_one (M := F[X]) X ▸ extract0 _ 1 0 (by decide), Polynomial.coeff_add,
      Polynomial.coeff_C_zero, zero_add, Polynomial.coeff_zero] at this
    exact sub_eq_zero.mp this
  · have := congrArg (·.coeff 1) hP
    simp only [extract0 _ 2 1 (by decide), pow_one (M := F[X]) X ▸ extract _ 1,
      Polynomial.coeff_add, Polynomial.coeff_C, if_neg one_ne_zero, add_zero, zero_add,
      Polynomial.coeff_zero] at this
    exact (sub_eq_zero.mp this).symm
  · have := congrArg (·.coeff 0) hP
    simp only [extract0 _ 2 0 (by decide), pow_one (M := F[X]) X ▸ extract0 _ 1 0 (by decide),
      Polynomial.coeff_add, Polynomial.coeff_C_zero, zero_add, Polynomial.coeff_zero] at this
    exact (sub_eq_zero.mp this).symm

theorem exists_variableChange [IsDedekindDomain W₁.toAffine.CoordinateRing] :
    ∃ E : VariableChange F, E • W₂ = W₁ ∧
      e (xf W₂) = algebraMap F _ ((E.u : F) ^ 2) * xf W₁ + algebraMap F _ E.r ∧
      e (yCoord W₂.toAffine) = algebraMap F _ ((E.u : F) ^ 3) * yCoord W₁.toAffine +
        algebraMap F _ ((E.u : F) ^ 2 * E.s) * xf W₁ + algebraMap F _ E.t := by
  obtain ⟨u', r, hu'0, hXshape⟩ := xf_shape e hinf
  obtain ⟨v, s', t, hv0, hYshape⟩ := yf_shape e hinf

  have hEq₂ : (W₂.map (algebraMap F W₁.toAffine.FunctionField)).toAffine.Equation
      (e (xf W₂)) (e (yCoord W₂.toAffine)) := by
    have h := equation_generic W₂
    rw [equation_iff] at h ⊢
    simp only [map_a₁, map_a₂, map_a₃, map_a₄, map_a₆] at h ⊢
    have h' := congrArg e h
    simp only [map_add, map_mul, map_pow, AlgEquiv.commutes] at h'
    linear_combination h'

  have hu'v : u' ^ 3 = v ^ 2 := by
    have hEq₁ := equation_generic W₁
    have hEq₂' := hEq₂
    rw [hXshape, hYshape, equation_iff] at hEq₂'
    rw [equation_iff] at hEq₁
    simp only [map_a₁, map_a₂, map_a₃, map_a₄, map_a₆] at hEq₁ hEq₂'
    have hdiff : polyToFunctionField W₁.toAffine
          (C (v ^ 2 - u' ^ 3) * X ^ 3
            + C (v ^ 2 * W₁.a₂ + s' ^ 2 + W₂.a₁ * u' * s' - 3 * u' ^ 2 * r - W₂.a₂ * u' ^ 2)
              * X ^ 2
            + C (v ^ 2 * W₁.a₄ + 2 * s' * t + W₂.a₁ * u' * t + W₂.a₁ * r * s' + W₂.a₃ * s'
                - 3 * u' * r ^ 2 - 2 * W₂.a₂ * u' * r - W₂.a₄ * u') * X
            + C (v ^ 2 * W₁.a₆ + t ^ 2 + W₂.a₁ * r * t + W₂.a₃ * t
                - r ^ 3 - W₂.a₂ * r ^ 2 - W₂.a₄ * r - W₂.a₆))
        + polyToFunctionField W₁.toAffine
          (C (2 * v * s' + W₂.a₁ * u' * v - v ^ 2 * W₁.a₁) * X
            + C (2 * v * t + W₂.a₁ * r * v + W₂.a₃ * v - v ^ 2 * W₁.a₃))
          * yCoord W₁.toAffine = 0 := by
      simp only [map_add, map_mul, map_sub, map_pow, polyToFunctionField_C, map_ofNat]
      rw [show polyToFunctionField W₁.toAffine X = xf W₁ from rfl]
      linear_combination hEq₂' - (algebraMap F W₁.toAffine.FunctionField v) ^ 2 * hEq₁
    rw [show yCoord W₁.toAffine = algebraMap W₁.toAffine.CoordinateRing W₁.toAffine.FunctionField
      (CoordinateRing.mk W₁.toAffine Y) from rfl, ← algebraMap_smul_basis] at hdiff
    obtain ⟨hP, -⟩ := CoordinateRing.smul_basis_eq_zero
      ((map_eq_zero_iff _
        (IsFractionRing.injective W₁.toAffine.CoordinateRing W₁.toAffine.FunctionField)).mp hdiff)
    have hc3 := congrArg (·.coeff 3) hP
    simp only [Polynomial.coeff_add, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow,
      Polynomial.coeff_X, Polynomial.coeff_C, Polynomial.coeff_zero,
      show ((3:ℕ) = 2) = False from by decide, show ((1:ℕ) = 3) = False from by decide,
      show ((3:ℕ) = 0) = False from by decide, if_true, if_false, mul_one, mul_zero,
      add_zero] at hc3
    exact (sub_eq_zero.mp hc3).symm

  have hu0 : v / u' ≠ 0 := div_ne_zero hv0 hu'0
  have hu2 : (v / u') ^ 2 = u' := by
    rw [div_pow, eq_comm, eq_div_iff (pow_ne_zero 2 hu'0), ← pow_succ']; exact hu'v
  have hu3 : (v / u') ^ 3 = v := by
    rw [div_pow, div_eq_iff (pow_ne_zero 3 hu'0), hu'v]; ring
  let E : VariableChange F := ⟨Units.mk0 (v / u') hu0, r, s' * u'⁻¹, t⟩
  have hEu : ((E.u : Fˣ) : F) = v / u' := rfl
  have hEs : u' * E.s = s' := by show u' * (s' * u'⁻¹) = s'; field_simp
  have hX' : e (xf W₂) = algebraMap F _ ((E.u : F) ^ 2) * xf W₁ + algebraMap F _ E.r := by
    rw [hEu, hu2]; exact hXshape
  have hY' : e (yCoord W₂.toAffine) = algebraMap F _ ((E.u : F) ^ 3) * yCoord W₁.toAffine +
      algebraMap F _ ((E.u : F) ^ 2 * E.s) * xf W₁ + algebraMap F _ E.t := by
    rw [hEu, hu2, hu3, hEs]; exact hYshape
  refine ⟨E, ?_, hX', hY'⟩

  apply eq_of_equation_generic
  have hvc : ((E.map (algebraMap F W₁.toAffine.FunctionField)) •
      (W₂.map (algebraMap F W₁.toAffine.FunctionField))).toAffine.Equation (xf W₁) (yCoord W₁.toAffine) := by
    rw [equation_variableChange_iff]
    have hx : vcX (E.map (algebraMap F W₁.toAffine.FunctionField)) (xf W₁) = e (xf W₂) := by
      rw [hX', vcX]; simp [VariableChange.map, map_pow]
    have hy : vcY (E.map (algebraMap F W₁.toAffine.FunctionField)) (xf W₁) (yCoord W₁.toAffine) =
        e (yCoord W₂.toAffine) := by
      rw [hY', vcY]; simp [VariableChange.map, map_pow, map_mul]
    rw [hx, hy]
    exact hEq₂
  rwa [map_variableChange] at hvc

end WeierstrassCurve.B2a

open _root_.WeierstrassCurve _root_.P2MW.S_WeierstrassCurve_exists_variableChange_smul_eq_of_functionField_algEquiv.WeierstrassCurve WeierstrassCurve.Affine in
theorem solution
    {F : Type*} [Field F] {W₁ W₂ : WeierstrassCurve F}
    [IsDedekindDomain W₁.toAffine.CoordinateRing]
    (e : W₂.toAffine.FunctionField ≃ₐ[F] W₁.toAffine.FunctionField)
    (hinf : ¬ WeierstrassCurve.Affine.valuationInfty W₁.toAffine
      (e (algebraMap W₂.toAffine.CoordinateRing W₂.toAffine.FunctionField
        (WeierstrassCurve.Affine.CoordinateRing.mk W₂.toAffine (Polynomial.C Polynomial.X)))) ≤ 1) :
    ∃ C : WeierstrassCurve.VariableChange F, C • W₂ = W₁ ∧
      e (algebraMap W₂.toAffine.CoordinateRing W₂.toAffine.FunctionField
          (WeierstrassCurve.Affine.CoordinateRing.mk W₂.toAffine (Polynomial.C Polynomial.X)))
        = algebraMap F W₁.toAffine.FunctionField ((C.u : F) ^ 2)
            * algebraMap W₁.toAffine.CoordinateRing W₁.toAffine.FunctionField
                (WeierstrassCurve.Affine.CoordinateRing.mk W₁.toAffine (Polynomial.C Polynomial.X))
          + algebraMap F W₁.toAffine.FunctionField C.r ∧
      e (algebraMap W₂.toAffine.CoordinateRing W₂.toAffine.FunctionField
          (WeierstrassCurve.Affine.CoordinateRing.mk W₂.toAffine Polynomial.X))
        = algebraMap F W₁.toAffine.FunctionField ((C.u : F) ^ 3)
            * algebraMap W₁.toAffine.CoordinateRing W₁.toAffine.FunctionField
                (WeierstrassCurve.Affine.CoordinateRing.mk W₁.toAffine Polynomial.X)
          + algebraMap F W₁.toAffine.FunctionField ((C.u : F) ^ 2 * C.s)
            * algebraMap W₁.toAffine.CoordinateRing W₁.toAffine.FunctionField
                (WeierstrassCurve.Affine.CoordinateRing.mk W₁.toAffine (Polynomial.C Polynomial.X))
          + algebraMap F W₁.toAffine.FunctionField C.t :=
  WeierstrassCurve.B2a.exists_variableChange e hinf

end

end S_WeierstrassCurve_exists_variableChange_smul_eq_of_functionField_algEquiv
end P2MW
export P2MW.S_WeierstrassCurve_exists_variableChange_smul_eq_of_functionField_algEquiv (solution)
