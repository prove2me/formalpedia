-- Prove2me | solution 1 for WeierstrassCurve.isUnit_eval_PsiSq_and_eval_prePsi_smul_abscissa_eq_zero_of_eval_primitive_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.822295+00:00
-- url     : https://prove2.me/submissions/a3bbd123-7877-50c3-a53a-373dbad68040

import Mathlib
import Definitions.Def_WeierstrassCurve_Generic
import Theorems.Thm_WeierstrassCurve_Affine_Point_smul_some_eq_zero_iff
import Theorems.Thm_WeierstrassCurve_Affine_Point_zsmul_some_eq_some_div
import Theorems.Thm_WeierstrassCurve_separable_prePsi_of_isUnit
import Theorems.Thm_WeierstrassCurve_separable_prePsi_of_isUnit_of_even
import Theorems.Thm_WeierstrassCurve_prePsi_dvd_prePsi_of_dvd
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_WeierstrassCurve_isUnit_eval_PsiSq_and_eval_prePsi_smul_abscissa_eq_zero_of_eval_primitive_eq_zero
p2m_attr_erase "instance" "WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv"
p2m_attr_erase "simp" "compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two"

set_option autoImplicit false

universe u

noncomputable section

open Polynomial
open scoped Polynomial.Bivariate

namespace WeierstrassCurve
p2m_export "WeierstrassCurve" "Affine isUnit_Δ Affine.CoordinateRing.mk_Ψ_sq a₃ map_map preΨ_ofNat a₁ Ψ_ofNat map map_Φ Affine.CoordinateRing mk preΨ a₄ a₂ a₆ Affine.Point.some leadingCoeff_preΨ' map_preΨ' ψ_two preΨ' map_id map_ΨSq ΨSq toAffine Affine.Point Affine.CoordinateRing.mk Affine.CoordinateRing.mk_ψ ψ₂ map_injective map_Δ Affine.equation_iff_nonsingular Δ Affine.CoordinateRing.mk_φ Affine.equation_iff j Generic.poly Generic.classify Generic.poly_map_classify Generic.Δ_poly_ne_zero Affine.Point.smul_some_eq_zero_iff Affine.Point.zsmul_some_eq_some_div separable_prePsi_of_isUnit separable_prePsi_of_isUnit_of_even prePsi_dvd_prePsi_of_dvd"
namespace E24MulByPrimePower
p2m_open "WeierstrassCurve~evalEval_ψ_sq~evalEval_φ"

section Helpers

variable {R : Type*} [CommRing R] (W : WeierstrassCurve R)

theorem preΨ_pow_eq_preΨ' (p j : ℕ) : W.preΨ (p ^ j) = W.preΨ' (p ^ j) := by
  rw [← WeierstrassCurve.preΨ_ofNat]; norm_cast

theorem isUnit_leadingCoeff_preΨ' [Nontrivial R] {n : ℕ} (hn : IsUnit (n : R)) :
    IsUnit (W.preΨ' n).leadingCoeff := by
  rw [W.leadingCoeff_preΨ' hn.ne_zero]
  split_ifs with he
  · have h2 : (n : R) = ((2 : ℕ) : R) * ((n / 2 : ℕ) : R) := by
      rw [← Nat.cast_mul, Nat.two_mul_div_two_of_even he]
    exact isUnit_of_mul_isUnit_right (h2 ▸ hn)
  · exact hn

theorem separable_preΨ' {n : ℕ} (hu : IsUnit ((n : R) * W.Δ)) : (W.preΨ' n).Separable := by
  rcases n.even_or_odd with hn | hn
  · exact W.separable_prePsi_of_isUnit_of_even hn hu
  · exact W.separable_prePsi_of_isUnit hn hu

theorem eq_zero_of_pow_nsmul_of_zsmul {M : Type*} [AddCommGroup M] {p : ℕ} (hp : p.Prime) {a : ℤ}
    (ha : ¬ (p : ℤ) ∣ a) (k : ℕ) {Q : M} (hk : (p ^ k) • Q = 0) (haQ : a • Q = 0) : Q = 0 := by
  have hpa : IsCoprime ((p : ℤ) ^ k) a :=
    IsCoprime.pow_left (((Nat.prime_iff_prime_int.mp hp).coprime_iff_not_dvd).mpr ha)
  obtain ⟨c, d, hcd⟩ := hpa
  have hk' : ((p : ℤ) ^ k) • Q = 0 := by rw [← Nat.cast_pow, natCast_zsmul]; exact hk
  calc Q = (1 : ℤ) • Q := (one_zsmul Q).symm
    _ = (c * (p : ℤ) ^ k + d * a) • Q := by rw [hcd]
    _ = 0 := by rw [add_smul, mul_smul, mul_smul, hk', haQ, smul_zero, smul_zero, add_zero]

theorem nsmul_zsmul_comm {M : Type*} [AddCommGroup M] (n : ℕ) (a : ℤ) (P : M) :
    n • (a • P) = a • (n • P) := by
  rw [← natCast_zsmul, smul_smul, mul_comm, ← smul_smul, natCast_zsmul]

end Helpers

section Field

variable {F : Type*} [Field F] (W : WeierstrassCurve F)

def evalPt {x y : F} (h : W.toAffine.Equation x y) : W.toAffine.CoordinateRing →+* F :=
  AdjoinRoot.lift (evalRingHom x) y (by rw [eval₂_evalRingHom]; exact h)

theorem evalPt_mk {x y : F} (h : W.toAffine.Equation x y) (f : F[X][Y]) :
    evalPt W h (Affine.CoordinateRing.mk W f) = f.evalEval x y := by
  rw [evalPt, Affine.CoordinateRing.mk, AdjoinRoot.lift_mk, eval₂_evalRingHom]

theorem evalEval_ψ_sq {x y : F} (h : W.toAffine.Equation x y) (n : ℤ) :
    (W.ψ n).evalEval x y ^ 2 = (W.ΨSq n).eval x := by
  have e := congrArg (evalPt W h) ((Affine.CoordinateRing.mk_ψ (W := W) n).trans rfl)
  have e2 := congrArg (evalPt W h) (Affine.CoordinateRing.mk_Ψ_sq (W := W) n)
  rw [map_pow, evalPt_mk, evalPt_mk, evalEval_C] at e2
  rw [evalPt_mk, evalPt_mk] at e
  rw [e, e2]

theorem evalEval_φ {x y : F} (h : W.toAffine.Equation x y) (n : ℤ) :
    (W.φ n).evalEval x y = (W.Φ n).eval x := by
  have e := congrArg (evalPt W h) (Affine.CoordinateRing.mk_φ (W := W) n)
  rwa [evalPt_mk, evalPt_mk, evalEval_C] at e

theorem exists_equation [IsAlgClosed F] (x : F) : ∃ y, W.toAffine.Equation x y := by
  let q : F[X] := X ^ 2 + C (W.a₁ * x + W.a₃) * X - C (x ^ 3 + W.a₂ * x ^ 2 + W.a₄ * x + W.a₆)
  have hq : q.degree = 2 := by
    simp only [q]
    compute_degree!
  obtain ⟨y, hy⟩ := IsAlgClosed.exists_root q (by rw [hq]; norm_num)
  refine ⟨y, ?_⟩
  rw [Affine.equation_iff]
  simp only [q, IsRoot, eval_add, eval_sub, eval_mul, eval_pow, eval_X, eval_C] at hy
  linear_combination hy

theorem evalEval_ψ_eq_Ψ {x y : F} (h : W.toAffine.Equation x y) (n : ℤ) :
    (W.ψ n).evalEval x y = (W.Ψ n).evalEval x y := by
  have e := congrArg (evalPt W h) (Affine.CoordinateRing.mk_ψ (W := W) n)
  rwa [evalPt_mk, evalPt_mk] at e

section RootCriteria

variable [DecidableEq F]

theorem nsmul_eq_zero_of_eval_preΨ' {n : ℕ} {x y : F} (h : W.toAffine.Nonsingular x y)
    (hx : (W.preΨ' n).eval x = 0) : n • (Affine.Point.some x y h) = 0 := by
  have hΨ : (W.Ψ (n : ℤ)).evalEval x y = 0 := by
    rw [W.Ψ_ofNat, evalEval_mul, evalEval_C, hx, zero_mul]
  have hψ : (W.ψ (n : ℤ)).evalEval x y = 0 := by rw [evalEval_ψ_eq_Ψ W h.1, hΨ]
  have := (Affine.Point.smul_some_eq_zero_iff W h (n : ℤ)).mpr hψ
  rwa [Nat.cast_smul_eq_nsmul] at this

theorem two_nsmul_eq_zero_iff {x y : F} (h : W.toAffine.Nonsingular x y) :
    2 • (Affine.Point.some x y h) = 0 ↔ W.ψ₂.evalEval x y = 0 := by
  rw [← Nat.cast_smul_eq_nsmul ℤ, Affine.Point.smul_some_eq_zero_iff W h, Nat.cast_ofNat,
    WeierstrassCurve.ψ_two]

theorem eval_preΨ'_eq_zero_of_nsmul_eq_zero {n : ℕ} {x y : F} (h : W.toAffine.Nonsingular x y)
    (hn : n • (Affine.Point.some x y h) = 0)
    (h2 : Even n → 2 • (Affine.Point.some x y h) ≠ 0) : (W.preΨ' n).eval x = 0 := by
  have hψ : (W.ψ (n : ℤ)).evalEval x y = 0 := by
    refine (Affine.Point.smul_some_eq_zero_iff W h (n : ℤ)).mp ?_
    rw [Nat.cast_smul_eq_nsmul]
    exact hn
  rw [evalEval_ψ_eq_Ψ W h.1, W.Ψ_ofNat, evalEval_mul, evalEval_C] at hψ
  rcases mul_eq_zero.mp hψ with h0 | h0
  · exact h0
  · exfalso
    by_cases he : Even n
    · rw [if_pos he] at h0
      exact h2 he ((two_nsmul_eq_zero_iff W h).mpr h0)
    · rw [if_neg he, evalEval_one] at h0
      exact one_ne_zero h0

end RootCriteria

variable {W}
variable [W.IsElliptic] {p : ℕ} [Fact p.Prime]

theorem field_facts_mul [DecidableEq F] [IsAlgClosed F] (hpF : (p : F) ≠ 0) (hp2 : p ≠ 2) (j : ℕ) {Λ : F[X]}
    (hΛ : W.preΨ' (p ^ (j + 1)) = W.preΨ' (p ^ j) * Λ)
    {ξ y : F} (hξy : W.toAffine.Equation ξ y) (hξ : Λ.eval ξ = 0) :
    (W.ΨSq ((p ^ j : ℕ) : ℤ)).eval ξ ≠ 0 ∧
      (W.preΨ' p).eval ((W.Φ ((p ^ j : ℕ) : ℤ)).eval ξ / (W.ΨSq ((p ^ j : ℕ) : ℤ)).eval ξ) = 0 := by
  classical
  have pp : p.Prime := Fact.out
  have hpodd : Odd p := pp.odd_of_ne_two hp2
  have hnF : ((p ^ (j + 1) : ℕ) : F) ≠ 0 := by rw [Nat.cast_pow]; exact pow_ne_zero _ hpF

  have hsep : (W.preΨ' (p ^ (j + 1))).Separable :=
    separable_preΨ' W (isUnit_iff_ne_zero.mpr (mul_ne_zero hnF W.isUnit_Δ.ne_zero))
  rw [hΛ] at hsep
  have hcop : IsCoprime (W.preΨ' (p ^ j)) Λ := hsep.isCoprime
  have hns : W.toAffine.Nonsingular ξ y := (Affine.equation_iff_nonsingular).mp hξy
  set P : W.toAffine.Point := Affine.Point.some ξ y hns with hP
  have hnξ : (W.preΨ' (p ^ (j + 1))).eval ξ = 0 := by rw [hΛ, eval_mul, hξ, mul_zero]
  have hmξ : (W.preΨ' (p ^ j)).eval ξ ≠ 0 := by
    intro h0
    obtain ⟨c, d, hcd⟩ := hcop
    have e := congrArg (eval ξ) hcd
    rw [eval_add, eval_mul, eval_mul, h0, hξ, mul_zero, mul_zero, add_zero, eval_one] at e
    exact zero_ne_one e
  have hnP : (p ^ (j + 1)) • P = 0 := nsmul_eq_zero_of_eval_preΨ' W hns hnξ
  have hoddpow : ∀ i : ℕ, ¬ Even (p ^ i) := fun i h => by
    rcases i with _ | i
    · simp at h
    · exact (Nat.not_even_iff_odd.mpr (hpodd.pow)) h

  have hmP : (p ^ j) • P ≠ 0 := fun h0 =>
    hmξ (eval_preΨ'_eq_zero_of_nsmul_eq_zero W hns h0 (fun he => absurd he (hoddpow j)))
  have hmP' : (((p ^ j : ℕ) : ℤ)) • P ≠ 0 := by rwa [Nat.cast_smul_eq_nsmul]
  have hψa : (W.ψ ((p ^ j : ℕ) : ℤ)).evalEval ξ y ≠ 0 := fun h0 =>
    hmP' ((Affine.Point.smul_some_eq_zero_iff W hns _).mpr h0)
  refine ⟨?_, ?_⟩
  · rw [← evalEval_ψ_sq W hξy]
    exact pow_ne_zero 2 hψa
  · obtain ⟨y', h', haP'⟩ := Affine.Point.zsmul_some_eq_some_div W hns (n := ((p ^ j : ℕ) : ℤ)) hψa

    have hpQ : p • ((((p ^ j : ℕ) : ℤ)) • P) = 0 := by
      rw [Nat.cast_smul_eq_nsmul, ← mul_nsmul', ← pow_succ', hnP]
    rw [haP'] at hpQ
    exact eval_preΨ'_eq_zero_of_nsmul_eq_zero W h' hpQ (fun he => absurd he (by simpa using hoddpow 1))

end Field

section Numerator

variable {A : Type*} [CommRing A]

def numer (W : WeierstrassCurve A) (G : A[X]) (d : ℕ) (a : ℤ) : A[X] :=
  ∑ i ∈ Finset.range (d + 1), C (G.coeff i) * (W.Φ a) ^ i * (W.ΨSq a) ^ (d - i)

theorem numer_map {B : Type*} [CommRing B] (f : A →+* B) (W : WeierstrassCurve A) (G : A[X])
    (d : ℕ) (a : ℤ) : (numer W G d a).map f = numer (W.map f) (G.map f) d a := by
  simp only [numer, Polynomial.map_sum, Polynomial.map_mul, Polynomial.map_pow, map_C, map_Φ,
    map_ΨSq, coeff_map]

theorem eval_numer_of_isUnit (W : WeierstrassCurve A) {G : A[X]} {d : ℕ} (hd : G.natDegree ≤ d)
    (a : ℤ) {x : A} (hu : IsUnit ((W.ΨSq a).eval x)) :
    (numer W G d a).eval x =
      (W.ΨSq a).eval x ^ d * G.eval ((W.Φ a).eval x * Ring.inverse ((W.ΨSq a).eval x)) := by
  set s := (W.ΨSq a).eval x
  set φ := (W.Φ a).eval x
  have hdeg : G.natDegree < d + 1 := Nat.lt_succ_of_le hd
  rw [eval_eq_sum_range' hdeg, numer, eval_finsetSum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i hi => ?_
  have hi' : i ≤ d := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
  simp only [eval_mul, eval_pow, eval_C]
  rw [mul_pow]
  obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le hi'
  have hs : s * Ring.inverse s = 1 := Ring.mul_inverse_cancel s hu
  rw [hk, Nat.add_sub_cancel_left, pow_add]
  have : s ^ i * Ring.inverse s ^ i = 1 := by rw [← mul_pow, hs, one_pow]
  linear_combination (-(G.coeff i * φ ^ i * s ^ k)) * this

theorem eval_numer_eq_zero_field {F : Type*} [Field F] [DecidableEq F] [IsAlgClosed F] {W : WeierstrassCurve F}
    [W.IsElliptic] {p : ℕ} [Fact p.Prime] (hpF : (p : F) ≠ 0) (hp2 : p ≠ 2) (j : ℕ) {Λ : F[X]}
    (hΛ : W.preΨ' (p ^ (j + 1)) = W.preΨ' (p ^ j) * Λ) {d : ℕ} (hd : (W.preΨ' p).natDegree ≤ d)
    {ξ y : F} (hξy : W.toAffine.Equation ξ y) (hξ : Λ.eval ξ = 0) :
    (numer W (W.preΨ' p) d ((p ^ j : ℕ) : ℤ)).eval ξ = 0 := by
  obtain ⟨hs, hroot⟩ := field_facts_mul hpF hp2 j hΛ hξy hξ
  rw [eval_numer_of_isUnit W hd _ hs.isUnit, Ring.inverse_eq_inv', ← div_eq_mul_inv, hroot,
    mul_zero]

end Numerator

section Universal

variable (p : ℕ) [Fact p.Prime]

abbrev 𝓡 : Type := Localization.Away ((p : MvPolynomial (Fin 5) ℤ))

def W𝓡 : WeierstrassCurve (𝓡 p) := (Generic.poly ℤ).map (algebraMap (MvPolynomial (Fin 5) ℤ) (𝓡 p))

theorem natCast_mvPolynomial_ne_zero : ((p : MvPolynomial (Fin 5) ℤ)) ≠ 0 :=
  Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero

theorem powers_le : Submonoid.powers ((p : MvPolynomial (Fin 5) ℤ)) ≤
    nonZeroDivisors (MvPolynomial (Fin 5) ℤ) :=
  powers_le_nonZeroDivisors_of_noZeroDivisors (natCast_mvPolynomial_ne_zero p)

scoped instance : IsDomain (𝓡 p) := IsLocalization.isDomain_localization (powers_le p)

theorem algebraMap_𝓡_injective :
    Function.Injective (algebraMap (MvPolynomial (Fin 5) ℤ) (𝓡 p)) :=
  IsLocalization.injective (𝓡 p) (powers_le p)

omit [Fact p.Prime] in
theorem isUnit_natCast_𝓡 : IsUnit ((p : 𝓡 p)) := by
  have h := IsLocalization.Away.algebraMap_isUnit (S := 𝓡 p) ((p : MvPolynomial (Fin 5) ℤ))
  rwa [map_natCast] at h

theorem natCast_𝓡_ne_zero : (p : 𝓡 p) ≠ 0 := (isUnit_natCast_𝓡 p).ne_zero

theorem Δ_W𝓡_ne_zero : (W𝓡 p).Δ ≠ 0 := by
  rw [W𝓡, map_Δ]
  exact (map_ne_zero_iff _ (algebraMap_𝓡_injective p)).mpr (Generic.Δ_poly_ne_zero ℤ)

abbrev 𝓛 : Type := AlgebraicClosure (FractionRing (𝓡 p))

def ι𝓛 : 𝓡 p →+* 𝓛 p := algebraMap (𝓡 p) (𝓛 p)

theorem ι𝓛_injective : Function.Injective (ι𝓛 p) := by
  rw [ι𝓛, IsScalarTower.algebraMap_eq (𝓡 p) (FractionRing (𝓡 p)) (𝓛 p)]
  exact (algebraMap (FractionRing (𝓡 p)) (𝓛 p)).injective.comp (IsFractionRing.injective (𝓡 p) _)

scoped instance isElliptic_W𝓛 : ((W𝓡 p).map (ι𝓛 p)).IsElliptic := by
  refine ⟨?_⟩
  rw [map_Δ, isUnit_iff_ne_zero]
  exact (map_ne_zero_iff _ (ι𝓛_injective p)).mpr (Δ_W𝓡_ne_zero p)

theorem natCast_𝓛_ne_zero : (p : 𝓛 p) ≠ 0 := by
  rw [← map_natCast (ι𝓛 p) p]
  exact (map_ne_zero_iff _ (ι𝓛_injective p)).mpr (natCast_𝓡_ne_zero p)

variable {p}

theorem exists_Λ𝓡 (j : ℕ) :
    ∃ Λ : (𝓡 p)[X], (W𝓡 p).preΨ' (p ^ (j + 1)) = (W𝓡 p).preΨ' (p ^ j) * Λ := by
  obtain ⟨Λ, h⟩ := (W𝓡 p).prePsi_dvd_prePsi_of_dvd (m := ((p ^ j : ℕ) : ℤ))
    (n := ((p ^ (j + 1) : ℕ) : ℤ)) (Int.natCast_dvd_natCast.mpr (pow_dvd_pow p j.le_succ))
  exact ⟨Λ, by rwa [preΨ_ofNat, preΨ_ofNat] at h⟩

theorem Λ_dvd_numer (hp2 : p ≠ 2) (j : ℕ) {Λ : (𝓡 p)[X]}
    (hΛ : (W𝓡 p).preΨ' (p ^ (j + 1)) = (W𝓡 p).preΨ' (p ^ j) * Λ) :
    Λ ∣ numer (W𝓡 p) ((W𝓡 p).preΨ' p) ((W𝓡 p).preΨ' p).natDegree ((p ^ j : ℕ) : ℤ) := by
  classical

  have hun : IsUnit ((p ^ (j + 1) : ℕ) : 𝓡 p) := by
    rw [Nat.cast_pow]; exact (isUnit_natCast_𝓡 p).pow _
  have hlcn := isUnit_leadingCoeff_preΨ' (W𝓡 p) hun
  have hlcΛ : IsUnit Λ.leadingCoeff := by
    rw [hΛ, leadingCoeff_mul] at hlcn
    exact isUnit_of_mul_isUnit_right hlcn
  obtain ⟨u, hu⟩ := hlcΛ
  set dΛ := Λ.natDegree with hdΛ
  set d := ((W𝓡 p).preΨ' p).natDegree with hd

  set Λm : (𝓡 p)[X] := C ((u⁻¹ : (𝓡 p)ˣ) : 𝓡 p) * Λ with hΛm
  have hmonic : Λm.Monic := by
    refine monic_C_mul_of_mul_leadingCoeff_eq_one ?_
    rw [← hu, Units.inv_mul]
  have hΛm_deg : Λm.natDegree = dΛ := by
    rw [hΛm, natDegree_C_mul_of_isUnit (Units.isUnit _)]

  set N := numer (W𝓡 p) ((W𝓡 p).preΨ' p) d ((p ^ j : ℕ) : ℤ)
  set Rem := N %ₘ Λm with hRem
  have hdiv : Rem + Λm * (N /ₘ Λm) = N := modByMonic_add_div N Λm
  by_cases hd0 : dΛ = 0
  ·
    have hΛC : Λ = C Λ.leadingCoeff := by
      rw [leadingCoeff, ← hdΛ, hd0]; exact eq_C_of_natDegree_eq_zero (hdΛ ▸ hd0)
    have hΛu : IsUnit Λ := by rw [hΛC, ← hu]; exact (Units.isUnit u).map C
    exact hΛu.dvd
  have hΛm1 : Λm ≠ 1 := fun h => by
    have := congrArg natDegree h
    rw [hΛm_deg, natDegree_one] at this
    exact hd0 this

  have hRem0 : Rem = 0 := by
    have hdegRem : Rem.natDegree < dΛ := by
      rw [← hΛm_deg]
      exact natDegree_modByMonic_lt N hmonic hΛm1
    apply Polynomial.map_injective (ι𝓛 p) (ι𝓛_injective p)
    rw [Polynomial.map_zero]
    set W' := (W𝓡 p).map (ι𝓛 p)
    have hp𝓛 := natCast_𝓛_ne_zero p
    have hΛ' : W'.preΨ' (p ^ (j + 1)) = W'.preΨ' (p ^ j) * Λ.map (ι𝓛 p) := by
      simp only [W', map_preΨ', hΛ, Polynomial.map_mul]
    have hdegmap : (Λ.map (ι𝓛 p)).natDegree = dΛ :=
      natDegree_map_eq_of_injective (ι𝓛_injective p) Λ
    have hsep : (Λ.map (ι𝓛 p)).Separable := by
      have hn𝓛 : ((p ^ (j + 1) : ℕ) : 𝓛 p) ≠ 0 := by
        rw [Nat.cast_pow]; exact pow_ne_zero _ hp𝓛
      have hs := separable_preΨ' W'
        (isUnit_iff_ne_zero.mpr (mul_ne_zero hn𝓛 W'.isUnit_Δ.ne_zero))
      rw [hΛ'] at hs
      exact hs.of_mul_right
    have hcard : Fintype.card ((Λ.map (ι𝓛 p)).rootSet (𝓛 p)) = dΛ := by
      rw [card_rootSet_eq_natDegree hsep (IsAlgClosed.splits _), hdegmap]
    have hdG : (W'.preΨ' p).natDegree ≤ d := by
      simp only [W', map_preΨ', hd]; exact natDegree_map_le
    refine eq_zero_of_natDegree_lt_card_of_eval_eq_zero _
      (ι := (Λ.map (ι𝓛 p)).rootSet (𝓛 p)) (f := ((↑) : (Λ.map (ι𝓛 p)).rootSet (𝓛 p) → 𝓛 p))
      Subtype.val_injective (fun ξ => ?_) ?_
    ·
      obtain ⟨ξ, hξ⟩ := ξ
      have hξroot : (Λ.map (ι𝓛 p)).eval ξ = 0 := by
        have := (mem_rootSet.mp hξ).2
        rwa [aeval_def, eval₂_eq_eval_map, Algebra.algebraMap_self, Polynomial.map_id] at this
      obtain ⟨y, hy⟩ := exists_equation W' ξ
      have hN : (N.map (ι𝓛 p)).eval ξ = 0 := by
        rw [numer_map, ← map_preΨ']
        exact eval_numer_eq_zero_field hp𝓛 hp2 j hΛ' hdG hy hξroot
      have hΛmξ : (Λm.map (ι𝓛 p)).eval ξ = 0 := by
        rw [hΛm, Polynomial.map_mul, map_C, eval_mul, eval_C, hξroot, mul_zero]
      have e := congrArg (fun q : (𝓡 p)[X] => (q.map (ι𝓛 p)).eval ξ) hdiv
      simp only [Polynomial.map_add, Polynomial.map_mul, eval_add, eval_mul, hN, hΛmξ,
        zero_mul, add_zero] at e
      exact e
    · calc (Rem.map (ι𝓛 p)).natDegree ≤ Rem.natDegree := natDegree_map_le
        _ < dΛ := hdegRem
        _ = _ := hcard.symm
  rw [hRem0, zero_add] at hdiv
  refine ⟨C ((u⁻¹ : (𝓡 p)ˣ) : 𝓡 p) * (N /ₘ Λm), ?_⟩
  set Q := N /ₘ Λm
  rw [← hdiv, hΛm]; ring

end Universal

section Specialise

variable {A : Type u} [CommRing A] (W : WeierstrassCurve A) {p : ℕ} [Fact p.Prime]

def classify𝓡 (hp : IsUnit (p : A)) : 𝓡 p →+* A :=
  IsLocalization.Away.lift ((p : MvPolynomial (Fin 5) ℤ))
    (g := (Generic.classify ℤ W : MvPolynomial (Fin 5) ℤ →+* A)) (by rwa [map_natCast])

omit [Fact p.Prime] in
theorem W𝓡_map_classify𝓡 (hp : IsUnit (p : A)) : (W𝓡 p).map (classify𝓡 W hp) = W := by
  rw [W𝓡, WeierstrassCurve.map_map, classify𝓡, IsLocalization.Away.lift_comp]
  exact Generic.poly_map_classify W

theorem Λ_dvd_numer_of_isUnit [Nontrivial A] (hp : IsUnit (p : A)) (hp2 : p ≠ 2) (j : ℕ) {Λ : A[X]}
    (hΛ : W.preΨ' (p ^ (j + 1)) = W.preΨ' (p ^ j) * Λ) :
    ∃ d, (W.preΨ' p).natDegree ≤ d ∧ Λ ∣ numer W (W.preΨ' p) d ((p ^ j : ℕ) : ℤ) := by
  obtain ⟨Λu, hΛu⟩ := exists_Λ𝓡 (p := p) j
  have hmapn : ((W𝓡 p).preΨ' (p ^ (j + 1))).map (classify𝓡 W hp) = W.preΨ' (p ^ (j + 1)) := by
    rw [← map_preΨ', W𝓡_map_classify𝓡]
  have hmapm : ((W𝓡 p).preΨ' (p ^ j)).map (classify𝓡 W hp) = W.preΨ' (p ^ j) := by
    rw [← map_preΨ', W𝓡_map_classify𝓡]
  have hmapp : ((W𝓡 p).preΨ' p).map (classify𝓡 W hp) = W.preΨ' p := by
    rw [← map_preΨ', W𝓡_map_classify𝓡]
  have hrel : W.preΨ' (p ^ j) * Λ = W.preΨ' (p ^ j) * Λu.map (classify𝓡 W hp) := by
    rw [← hΛ, ← hmapn, hΛu, Polynomial.map_mul, hmapm]
  have hlc : IsUnit (W.preΨ' (p ^ j)).leadingCoeff :=
    isUnit_leadingCoeff_preΨ' W (by rw [Nat.cast_pow]; exact hp.pow _)
  have hΛeq : Λ = Λu.map (classify𝓡 W hp) := by
    have h0 : W.preΨ' (p ^ j) * (Λ - Λu.map (classify𝓡 W hp)) = 0 := by
      rw [mul_sub, hrel, sub_self]
    rwa [isUnit_leadingCoeff_mul_right_eq_zero_iff hlc, sub_eq_zero] at h0
  refine ⟨((W𝓡 p).preΨ' p).natDegree, ?_, ?_⟩
  · rw [← hmapp]; exact natDegree_map_le
  · have h := Polynomial.map_dvd (classify𝓡 W hp) (Λ_dvd_numer hp2 j hΛu)
    rw [numer_map, W𝓡_map_classify𝓡 W hp, ← hΛeq] at h
    rw [← hmapp]
    exact h

theorem eval_preΨ'_eq_zero_of_isUnit (hp : IsUnit (p : A)) (hp2 : p ≠ 2) (j : ℕ) {Λ : A[X]}
    (hΛ : W.preΨ' (p ^ (j + 1)) = W.preΨ' (p ^ j) * Λ) {x : A} (hx : Λ.eval x = 0)
    (hu : IsUnit ((W.ΨSq ((p ^ j : ℕ) : ℤ)).eval x)) :
    (W.preΨ' p).eval ((W.Φ ((p ^ j : ℕ) : ℤ)).eval x * Ring.inverse ((W.ΨSq ((p ^ j : ℕ) : ℤ)).eval x)) = 0 := by
  nontriviality A
  obtain ⟨d, hd, Q, hQ⟩ := Λ_dvd_numer_of_isUnit W hp hp2 j hΛ
  have h0 : (numer W (W.preΨ' p) d ((p ^ j : ℕ) : ℤ)).eval x = 0 := by rw [hQ, eval_mul, hx, zero_mul]
  rw [eval_numer_of_isUnit W hd _ hu] at h0
  exact (hu.pow _).mul_right_eq_zero.mp h0

theorem isUnit_eval_ΨSq (hpΔ : IsUnit ((p : A) * W.Δ)) (hp2 : p ≠ 2) (j : ℕ) {Λ : A[X]}
    (hΛ : W.preΨ' (p ^ (j + 1)) = W.preΨ' (p ^ j) * Λ) {x : A} (hx : Λ.eval x = 0) :
    IsUnit ((W.ΨSq ((p ^ j : ℕ) : ℤ)).eval x) := by
  classical
  by_contra hnu

  obtain ⟨𝔪, h𝔪, hs𝔪⟩ := exists_max_ideal_of_mem_nonunits (mem_nonunits_iff.mpr hnu)
  let k := A ⧸ 𝔪
  letI : Field k := Ideal.Quotient.field 𝔪
  let L := AlgebraicClosure k
  let π : A →+* L := (algebraMap k L).comp (Ideal.Quotient.mk 𝔪)

  have hpL : IsUnit ((p : L) * (W.map π).Δ) := by
    have h := hpΔ.map π
    rwa [map_mul, map_natCast, ← map_Δ] at h
  haveI : (W.map π).IsElliptic := ⟨isUnit_of_mul_isUnit_right hpL⟩
  have hpL0 : (p : L) ≠ 0 := (isUnit_of_mul_isUnit_left hpL).ne_zero
  have hΛ' : (W.map π).preΨ' (p ^ (j + 1)) = (W.map π).preΨ' (p ^ j) * Λ.map π := by
    rw [map_preΨ', map_preΨ', hΛ, Polynomial.map_mul]
  have hξ : (Λ.map π).eval (π x) = 0 := by
    rw [eval_map, eval₂_at_apply, hx, map_zero]
  obtain ⟨y, hy⟩ := exists_equation (W.map π) (π x)
  have hne := (field_facts_mul (W := W.map π) hpL0 hp2 j hΛ' hy hξ).1
  apply hne
  rw [map_ΨSq, eval_map, eval₂_at_apply]
  show π _ = 0
  simp only [π, RingHom.comp_apply]
  rw [Ideal.Quotient.eq_zero_iff_mem.mpr hs𝔪, map_zero]

end Specialise

theorem main {A : Type u} [CommRing A] (W : WeierstrassCurve A) (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2) (k : ℕ) (hk : 1 ≤ k)
    (hpΔ : IsUnit ((p : A) * W.Δ)) {Λ : Polynomial A}
    (hΛ : W.preΨ (p ^ k) = W.preΨ (p ^ (k - 1)) * Λ)
    {x : A} (hx : Λ.eval x = 0) :
    IsUnit ((W.ΨSq (p ^ (k - 1) : ℕ)).eval x) ∧
      (W.preΨ p).eval ((W.Φ (p ^ (k - 1) : ℕ)).eval x * Ring.inverse ((W.ΨSq (p ^ (k - 1) : ℕ)).eval x)) = 0 := by
  rw [preΨ_pow_eq_preΨ', preΨ_pow_eq_preΨ'] at hΛ
  rw [WeierstrassCurve.preΨ_ofNat]
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  simp only [Nat.add_sub_cancel] at hΛ ⊢
  have hp : IsUnit (p : A) := isUnit_of_mul_isUnit_left hpΔ
  have hu := isUnit_eval_ΨSq W hpΔ hp2 j hΛ hx
  exact ⟨hu, eval_preΨ'_eq_zero_of_isUnit W hp hp2 j hΛ hx hu⟩

end WeierstrassCurve.E24MulByPrimePower
p2m_reactivate "P2MW.S_WeierstrassCurve_isUnit_eval_PsiSq_and_eval_prePsi_smul_abscissa_eq_zero_of_eval_primitive_eq_zero.WeierstrassCurve P2MW.S_WeierstrassCurve_isUnit_eval_PsiSq_and_eval_prePsi_smul_abscissa_eq_zero_of_eval_primitive_eq_zero.WeierstrassCurve.E24MulByPrimePower"
p2m_reactivate "P2MW.S_WeierstrassCurve_isUnit_eval_PsiSq_and_eval_prePsi_smul_abscissa_eq_zero_of_eval_primitive_eq_zero.WeierstrassCurve"

end
p2m_reactivate "P2MW.S_WeierstrassCurve_isUnit_eval_PsiSq_and_eval_prePsi_smul_abscissa_eq_zero_of_eval_primitive_eq_zero.WeierstrassCurve P2MW.S_WeierstrassCurve_isUnit_eval_PsiSq_and_eval_prePsi_smul_abscissa_eq_zero_of_eval_primitive_eq_zero.WeierstrassCurve.E24MulByPrimePower"

p2m_open "WeierstrassCurve~evalEval_ψ_sq~evalEval_φ" in open _root_.P2MW.S_WeierstrassCurve_isUnit_eval_PsiSq_and_eval_prePsi_smul_abscissa_eq_zero_of_eval_primitive_eq_zero.WeierstrassCurve WeierstrassCurve.E24MulByPrimePower in
theorem solution
    {T : Type u} [CommRing T] (W : WeierstrassCurve T) (ℓ : ℕ) [Fact ℓ.Prime] (hℓ2 : ℓ ≠ 2) (k : ℕ) (hk : 1 ≤ k)
    (hℓΔ : IsUnit ((ℓ : T) * W.Δ)) {Λ : Polynomial T}
    (hΛ : W.preΨ (ℓ ^ k) = W.preΨ (ℓ ^ (k - 1)) * Λ) (x y : T) (he : W.toAffine.Equation x y) (hx : Λ.eval x = 0) :
    IsUnit ((W.ΨSq (ℓ ^ (k - 1) : ℕ)).eval x) ∧
      (W.preΨ ℓ).eval ((W.Φ (ℓ ^ (k - 1) : ℕ)).eval x * Ring.inverse ((W.ΨSq (ℓ ^ (k - 1) : ℕ)).eval x)) = 0 :=
  main W ℓ hℓ2 k hk hℓΔ hΛ hx

end S_WeierstrassCurve_isUnit_eval_PsiSq_and_eval_prePsi_smul_abscissa_eq_zero_of_eval_primitive_eq_zero
end P2MW
export P2MW.S_WeierstrassCurve_isUnit_eval_PsiSq_and_eval_prePsi_smul_abscissa_eq_zero_of_eval_primitive_eq_zero (solution)
