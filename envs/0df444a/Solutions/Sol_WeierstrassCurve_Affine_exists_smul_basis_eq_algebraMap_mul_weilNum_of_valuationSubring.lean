-- Prove2me | solution 1 for WeierstrassCurve.Affine.exists_smul_basis_eq_algebraMap_mul_weilNum_of_valuationSubring
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.503601+00:00
-- url     : https://prove2.me/submissions/5fd40780-710b-5157-ad86-1b25fbb28fb6

import Mathlib
import Definitions.Def_EllipticCurve_DivisionPolynomialOmega
import Definitions.Def_EllipticCurve_WeilPairingFun
import Theorems.Thm_WeierstrassCurve_Affine_Point_zsmul_x_mul_psi_sq
import Theorems.Thm_WeierstrassCurve_Affine_Point_zsmul_y_mul_psi_cube
import Theorems.Thm_WeierstrassCurve_Affine_Point_zsmul_some_eq_some_div
import Theorems.Thm_WeierstrassCurve_isCoprime_Phi_PsiSq
import Theorems.Thm_WeierstrassCurve_Affine_evalEval_psi_sq
import Theorems.Thm_WeierstrassCurve_Affine_Point_smul_some_eq_zero_iff
import Theorems.Thm_WeierstrassCurve_Affine_CoordinateRing_isDedekindDomain
import Theorems.Thm_WeierstrassCurve_Affine_CoordinateRing_natDegree_norm_eq_finsum_count
import Theorems.Thm_WeierstrassCurve_Affine_valuation_weilNum
import Theorems.Thm_WeierstrassCurve_Affine_weilNum_ne_zero
import Theorems.Thm_WeierstrassCurve_Affine_fibSet_finite
import Theorems.Thm_WeierstrassCurve_Affine_ncard_fibSet
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_WeierstrassCurve_Affine_exists_smul_basis_eq_algebraMap_mul_weilNum_of_valuationSubring
p2m_attr_erase "instance" "WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv"
p2m_attr_erase "simp" "compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two"

set_option autoImplicit false

open Polynomial
open scoped Polynomial.Bivariate nonZeroDivisors
p2m_open "WeierstrassCurve~specialize~evalEval_φ WeierstrassCurve.Affine IsDedekindDomain IsDedekindDomain.HeightOneSpectrum WithZero"

namespace P2M
namespace WeilRed

p2m_open "WeierstrassCurve~specialize~evalEval_φ"

p2m_open "WeierstrassCurve~specialize~evalEval_φ"

theorem specialize_map {R S : Type*} [CommRing R] [CommRing S] (W : WeierstrassCurve R) (f : R →+* S) :
    Universal.specialize (W.map f) = f.comp (Universal.specialize W) := by
  refine MvPolynomial.ringHom_ext (fun z => by simp [Universal.specialize]) (fun i => ?_)
  fin_cases i <;>
    simp [Universal.specialize, WeierstrassCurve.map, Fin.isValue]

theorem map_ω {R S : Type*} [CommRing R] [CommRing S] (W : WeierstrassCurve R) (f : R →+* S) (n : ℤ) :
    (W.map f).ω n = (W.ω n).map (mapRingHom f) := by
  rw [WeierstrassCurve.ω, WeierstrassCurve.ω, specialize_map, ← Polynomial.mapRingHom_comp, Polynomial.map_map]

theorem evalEval_eq_of_mk_eq {R : Type*} [CommRing R] (W : WeierstrassCurve R) {x y : R} (h : W.toAffine.Equation x y)
    {p q : R[X][Y]} (hpq : Affine.CoordinateRing.mk W.toAffine p = Affine.CoordinateRing.mk W.toAffine q) :
    p.evalEval x y = q.evalEval x y := by
  obtain ⟨r, hr⟩ := AdjoinRoot.mk_eq_mk.mp hpq
  have h0 : W.toAffine.polynomial.evalEval x y = 0 := h
  have : (p - q).evalEval x y = 0 := by
    rw [hr, Polynomial.evalEval, Polynomial.eval_mul, Polynomial.eval_mul]
    change W.toAffine.polynomial.evalEval x y * r.evalEval x y = 0
    rw [h0, zero_mul]
  rwa [Polynomial.evalEval, Polynomial.eval_sub, Polynomial.eval_sub, sub_eq_zero] at this

theorem evalEval_φ {R : Type*} [CommRing R] (W : WeierstrassCurve R) {x y : R} (h : W.toAffine.Equation x y) (n : ℤ) :
    (W.φ n).evalEval x y = (W.Φ n).eval x := by
  rw [evalEval_eq_of_mk_eq W h (Affine.CoordinateRing.mk_φ W n), Polynomial.evalEval_C]

theorem not_common_root {F : Type*} [Field F] {p q : F[X]} (h : IsCoprime p q) {a : F} (hp : p.eval a = 0)
    (hq : q.eval a = 0) : False := by
  obtain ⟨u, v, huv⟩ := h
  have := congrArg (Polynomial.eval a) huv
  rw [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_mul, hp, hq, mul_zero, mul_zero, add_zero,
    Polynomial.eval_one] at this
  exact zero_ne_one this

theorem identities_of_zsmul_eq {A K : Type*} [CommRing A] [Field K] [DecidableEq K] (ι : A →+* K)
    (hι : Function.Injective ι) (W : WeierstrassCurve A) {WK : WeierstrassCurve K} (hWK : WK = W.map ι) [WK.IsElliptic]
    (n : ℤ) {x y x' y' : A}
    (hP : WK.toAffine.Nonsingular (ι x) (ι y)) (hQ : WK.toAffine.Nonsingular (ι x') (ι y'))
    (h : n • WeierstrassCurve.Affine.Point.some _ _ hP = WeierstrassCurve.Affine.Point.some _ _ hQ) :
    x' * (W.ψ n).evalEval x y ^ 2 = (W.φ n).evalEval x y ∧ y' * (W.ψ n).evalEval x y ^ 3 = (W.ω n).evalEval x y := by
  subst hWK
  have hx := WeierstrassCurve.Affine.Point.zsmul_x_mul_psi_sq (W.map ι) n hP hQ h
  have hy := WeierstrassCurve.Affine.Point.zsmul_y_mul_psi_cube (W.map ι) n hP hQ h
  rw [WeierstrassCurve.map_ψ, WeierstrassCurve.map_φ, Polynomial.map_mapRingHom_evalEval,
    Polynomial.map_mapRingHom_evalEval, ← map_pow, ← map_mul] at hx
  rw [WeierstrassCurve.map_ψ, map_ω, Polynomial.map_mapRingHom_evalEval, Polynomial.map_mapRingHom_evalEval, ← map_pow,
    ← map_mul] at hy
  exact ⟨hι hx, hι hy⟩

theorem zsmul_some_eq_some_of_specialisation {A K Ω : Type*} [CommRing A] [Field K] [Field Ω] [DecidableEq K] [DecidableEq Ω]
    (ι : A →+* K) (hι : Function.Injective ι) (ψ : A →+* Ω) (W : WeierstrassCurve A)
    {WK : WeierstrassCurve K} (hWK : WK = W.map ι) [WK.IsElliptic]
    {WΩ : WeierstrassCurve Ω} (hWΩ : WΩ = W.map ψ) [WΩ.IsElliptic]
    (n : ℤ) {x y x' y' : A}
    (hP : WK.toAffine.Nonsingular (ι x) (ι y)) (hQ : WK.toAffine.Nonsingular (ι x') (ι y'))
    (hP' : WΩ.toAffine.Nonsingular (ψ x) (ψ y)) (hQ' : WΩ.toAffine.Nonsingular (ψ x') (ψ y'))
    (h : n • WeierstrassCurve.Affine.Point.some _ _ hP = WeierstrassCurve.Affine.Point.some _ _ hQ) :
    n • WeierstrassCurve.Affine.Point.some _ _ hP' = WeierstrassCurve.Affine.Point.some _ _ hQ' := by
  obtain ⟨hx, hy⟩ := identities_of_zsmul_eq ι hι W hWK n hP hQ h
  subst hWΩ

  have hxΩ : ψ x' * ((W.map ψ).ψ n).evalEval (ψ x) (ψ y) ^ 2 = ((W.map ψ).φ n).evalEval (ψ x) (ψ y) := by
    rw [WeierstrassCurve.map_ψ, WeierstrassCurve.map_φ, Polynomial.map_mapRingHom_evalEval,
      Polynomial.map_mapRingHom_evalEval, ← map_pow, ← map_mul, hx]
  have hyΩ : ψ y' * ((W.map ψ).ψ n).evalEval (ψ x) (ψ y) ^ 3 = ((W.map ψ).ω n).evalEval (ψ x) (ψ y) := by
    rw [WeierstrassCurve.map_ψ, map_ω, Polynomial.map_mapRingHom_evalEval, Polynomial.map_mapRingHom_evalEval, ← map_pow,
      ← map_mul, hy]
  have heq : (W.map ψ).toAffine.Equation (ψ x) (ψ y) := hP'.1
  have hφΦ := evalEval_φ (W.map ψ) heq n
  have hψΨ := WeierstrassCurve.Affine.evalEval_psi_sq (W.map ψ) heq n

  have hψn : ((W.map ψ).ψ n).evalEval (ψ x) (ψ y) ≠ 0 := by
    intro h0
    apply not_common_root (WeierstrassCurve.isCoprime_Phi_PsiSq (W.map ψ) n) (a := ψ x)
    · rw [← hφΦ, ← hxΩ, h0]; ring
    · rw [← hψΨ, h0]; ring

  obtain ⟨y'', h'', hmul⟩ := WeierstrassCurve.Affine.Point.zsmul_some_eq_some_div (W.map ψ) hP' hψn
  rw [hmul]
  have hx'' : ((W.map ψ).Φ n).eval (ψ x) / ((W.map ψ).ΨSq n).eval (ψ x) = ψ x' := by
    rw [← hφΦ, ← hψΨ, ← hxΩ, mul_div_assoc, div_self (pow_ne_zero 2 hψn), mul_one]
  have hy'' : y'' = ψ y' := by
    have h3 := WeierstrassCurve.Affine.Point.zsmul_y_mul_psi_cube (W.map ψ) n hP' h'' hmul
    have : y'' * ((W.map ψ).ψ n).evalEval (ψ x) (ψ y) ^ 3 = ψ y' * ((W.map ψ).ψ n).evalEval (ψ x) (ψ y) ^ 3 := by
      rw [h3, hyΩ]
    exact mul_right_cancel₀ (pow_ne_zero 3 hψn) this
  subst hy''
  simp only [hx'']

theorem monic_Phi_sub {R : Type*} [CommRing R] [Nontrivial R] (W : WeierstrassCurve R) {n : ℤ} (hn : n ≠ 0) (c : R) :
    (W.Φ n - Polynomial.C c * W.ΨSq n).Monic := by
  have hlt : (Polynomial.C c * W.ΨSq n).natDegree < (W.Φ n).natDegree := by
    rw [WeierstrassCurve.natDegree_Φ]
    refine lt_of_le_of_lt (Polynomial.natDegree_C_mul_le _ _) (lt_of_le_of_lt (WeierstrassCurve.natDegree_ΨSq_le W n) ?_)
    have : 0 < n.natAbs ^ 2 := pow_pos (Int.natAbs_pos.mpr hn) 2
    omega
  rw [Polynomial.Monic, Polynomial.leadingCoeff_sub_of_degree_lt (Polynomial.degree_lt_degree hlt),
    WeierstrassCurve.leadingCoeff_Φ]

theorem mem_of_root_monic {K : Type*} [Field K] (𝒪 : ValuationSubring K) {p : Polynomial 𝒪} (hp : p.Monic) {a : K}
    (ha : (p.map (algebraMap 𝒪 K)).eval a = 0) : a ∈ 𝒪 := by
  have hint : IsIntegral 𝒪 a := ⟨p, hp, by rwa [Polynomial.eval_map] at ha⟩
  obtain ⟨b, hb⟩ := (IsIntegrallyClosed.isIntegral_iff (R := 𝒪) (K := K)).mp hint
  rw [← hb]
  exact b.2

theorem yc_mem_of_xc_mem {K : Type*} [Field K] (𝒪 : ValuationSubring K) (W : WeierstrassCurve 𝒪) {xR yR : K}
    (heq : (W.map (algebraMap 𝒪 K)).toAffine.Equation xR yR) (hx : xR ∈ 𝒪) : yR ∈ 𝒪 := by
  obtain ⟨x₀, rfl⟩ : ∃ x₀ : 𝒪, algebraMap 𝒪 K x₀ = xR := ⟨⟨xR, hx⟩, rfl⟩
  let r : Polynomial 𝒪 := Polynomial.C (W.a₁ * x₀ + W.a₃) * Polynomial.X -
    Polynomial.C (x₀ ^ 3 + W.a₂ * x₀ ^ 2 + W.a₄ * x₀ + W.a₆)
  have hr : r.degree < (2 : ℕ) := by
    refine lt_of_le_of_lt (Polynomial.degree_sub_le _ _) (max_lt ?_ ?_)
    · exact lt_of_le_of_lt (Polynomial.degree_C_mul_X_le _) (by exact_mod_cast Nat.one_lt_two)
    · exact lt_of_le_of_lt Polynomial.degree_C_le (by exact_mod_cast Nat.zero_lt_two)
  have hq : (Polynomial.X ^ 2 + r).Monic := Polynomial.monic_X_pow_add hr
  refine mem_of_root_monic 𝒪 hq ?_
  have he : (W.map (algebraMap 𝒪 K)).toAffine.polynomial.evalEval (algebraMap 𝒪 K x₀) yR = 0 := heq
  rw [WeierstrassCurve.Affine.evalEval_polynomial, WeierstrassCurve.map_a₁, WeierstrassCurve.map_a₂,
    WeierstrassCurve.map_a₃, WeierstrassCurve.map_a₄, WeierstrassCurve.map_a₆] at he
  have hev : ((Polynomial.X ^ 2 + r).map (algebraMap 𝒪 K)).eval yR =
      yR ^ 2 + (algebraMap 𝒪 K W.a₁ * algebraMap 𝒪 K x₀ + algebraMap 𝒪 K W.a₃) * yR -
        (algebraMap 𝒪 K x₀ ^ 3 + algebraMap 𝒪 K W.a₂ * algebraMap 𝒪 K x₀ ^ 2 + algebraMap 𝒪 K W.a₄ * algebraMap 𝒪 K x₀ +
          algebraMap 𝒪 K W.a₆) := by
    simp only [r, Polynomial.map_add, Polynomial.map_pow, Polynomial.map_X, Polynomial.map_sub, Polynomial.map_mul,
      Polynomial.map_C, Polynomial.eval_add, Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_sub,
      Polynomial.eval_mul, Polynomial.eval_C, map_add, map_mul, map_pow]
    ring
  rw [hev]
  linear_combination he

section Surj

variable {K : Type*} [Field K] [IsAlgClosed K] [DecidableEq K] (𝒪 : ValuationSubring K)

omit [DecidableEq K] in

theorem exists_multiset_prod_eq (F : Polynomial 𝒪) (hF : F.Monic) :
    ∃ t : Multiset 𝒪, F = (t.map fun ξ => Polynomial.X - Polynomial.C ξ).prod := by
  induction hd : F.natDegree using Nat.strong_induction_on generalizing F with
  | _ d ih =>
    rcases Nat.eq_zero_or_pos d with rfl | hdpos
    · refine ⟨0, ?_⟩
      rw [Multiset.map_zero, Multiset.prod_zero]
      exact Polynomial.eq_one_of_monic_natDegree_zero hF hd
    ·
      have hdeg : (F.map (algebraMap 𝒪 K)).degree ≠ 0 := by
        rw [hF.degree_map, Polynomial.degree_eq_natDegree hF.ne_zero, hd]
        exact_mod_cast hdpos.ne'
      obtain ⟨ξ, hξ⟩ := IsAlgClosed.exists_root (F.map (algebraMap 𝒪 K)) hdeg
      have hξmem : ξ ∈ 𝒪 := mem_of_root_monic 𝒪 hF hξ
      obtain ⟨ξ₀, rfl⟩ : ∃ ξ₀ : 𝒪, algebraMap 𝒪 K ξ₀ = ξ := ⟨⟨ξ, hξmem⟩, rfl⟩
      have hroot : F.IsRoot ξ₀ := by
        have h1 : algebraMap 𝒪 K (F.eval ξ₀) = 0 := by
          rw [← Polynomial.eval₂_at_apply, ← Polynomial.eval_map]; exact hξ
        exact (map_eq_zero_iff _ (IsFractionRing.injective 𝒪 K)).mp h1
      have hfac : (Polynomial.X - Polynomial.C ξ₀) * (F /ₘ (Polynomial.X - Polynomial.C ξ₀)) = F :=
        Polynomial.mul_divByMonic_eq_iff_isRoot.mpr hroot
      have hG : (F /ₘ (Polynomial.X - Polynomial.C ξ₀)).Monic :=
        Polynomial.Monic.of_mul_monic_left (Polynomial.monic_X_sub_C ξ₀) (hfac.symm ▸ hF)
      have hGdeg : (F /ₘ (Polynomial.X - Polynomial.C ξ₀)).natDegree = d - 1 := by
        have := congrArg Polynomial.natDegree hfac
        rw [(Polynomial.monic_X_sub_C ξ₀).natDegree_mul hG, Polynomial.natDegree_X_sub_C, hd] at this
        omega
      obtain ⟨t, ht⟩ := ih (d - 1) (by omega) _ hG hGdeg
      refine ⟨ξ₀ ::ₘ t, ?_⟩
      rw [Multiset.map_cons, Multiset.prod_cons, ← ht, hfac]

omit [DecidableEq K] in

theorem exists_root_of_eval_map_eq_zero {Ω : Type*} [Field Ω] (ψ : 𝒪 →+* Ω) (F : Polynomial 𝒪) (hF : F.Monic) {a : Ω}
    (ha : (F.map ψ).eval a = 0) : ∃ ξ : 𝒪, F.eval ξ = 0 ∧ ψ ξ = a := by
  obtain ⟨t, rfl⟩ := exists_multiset_prod_eq 𝒪 F hF
  rw [Polynomial.map_multiset_prod, Multiset.map_map, Polynomial.eval_multiset_prod, Multiset.map_map,
    Multiset.prod_eq_zero_iff, Multiset.mem_map] at ha
  obtain ⟨ξ, hξt, hξ⟩ := ha
  simp only [Function.comp_apply, Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C, Polynomial.eval_sub,
    Polynomial.eval_X, Polynomial.eval_C, sub_eq_zero] at hξ
  refine ⟨ξ, ?_, hξ.symm⟩
  rw [Polynomial.eval_multiset_prod, Multiset.map_map, Multiset.prod_eq_zero_iff, Multiset.mem_map]
  exact ⟨ξ, hξt, by simp⟩

theorem eq_or_eq_neg_of_xc_eq {F : Type*} [Field F] [DecidableEq F] (W : WeierstrassCurve F) {x y₁ y₂ : F}
    (h₁ : W.toAffine.Nonsingular x y₁) (h₂ : W.toAffine.Nonsingular x y₂) :
    WeierstrassCurve.Affine.Point.some _ _ h₂ = WeierstrassCurve.Affine.Point.some _ _ h₁ ∨
      WeierstrassCurve.Affine.Point.some _ _ h₂ = -WeierstrassCurve.Affine.Point.some _ _ h₁ := by
  rcases WeierstrassCurve.Affine.Y_eq_of_X_eq h₂.1 h₁.1 rfl with h | h
  · left; subst h; rfl
  · right
    rw [WeierstrassCurve.Affine.Point.neg_some]
    subst h; rfl

omit [IsAlgClosed K] in

theorem xc_mem_of_zsmul_eq_zero (W : WeierstrassCurve 𝒪) [(W.map (algebraMap 𝒪 K)).IsElliptic]
    {n : ℕ} (hn : IsUnit ((n : ℕ) : (𝒪 : Type _))) {xR yR : K} (hR : (W.map (algebraMap 𝒪 K)).toAffine.Nonsingular xR yR)
    (h : (n : ℤ) • WeierstrassCurve.Affine.Point.some _ _ hR = 0) : xR ∈ 𝒪 := by
  have hn0 : ((n : ℤ) : (𝒪 : Type _)) ≠ 0 := by rw [Int.cast_natCast]; exact hn.ne_zero
  have hψ := (WeierstrassCurve.Affine.Point.smul_some_eq_zero_iff (W.map (algebraMap 𝒪 K)) hR (n : ℤ)).mp h
  have hΨ : ((W.map (algebraMap 𝒪 K)).ΨSq n).eval xR = 0 := by
    rw [← WeierstrassCurve.Affine.evalEval_psi_sq (W.map (algebraMap 𝒪 K)) hR.1 n, hψ]; ring
  obtain ⟨u, hu⟩ := hn

  let a : (𝒪 : Type _) := ((u⁻¹ ^ 2 : (𝒪 : Type _)ˣ) : (𝒪 : Type _))
  have hlc : (W.ΨSq n).leadingCoeff = (u : (𝒪 : Type _)) ^ 2 := by
    rw [WeierstrassCurve.leadingCoeff_ΨSq W hn0, Int.cast_natCast, hu]
  have hG : (Polynomial.C a * W.ΨSq n).Monic := by
    refine Polynomial.monic_C_mul_of_mul_leadingCoeff_eq_one ?_
    rw [hlc, ← Units.val_pow_eq_pow_val, ← Units.val_mul, ← mul_pow, inv_mul_cancel, one_pow, Units.val_one]
  refine mem_of_root_monic 𝒪 hG ?_
  rw [Polynomial.map_mul, Polynomial.map_C, ← WeierstrassCurve.map_ΨSq, Polynomial.eval_mul, Polynomial.eval_C, hΨ, mul_zero]

theorem exists_nonsingular {F : Type*} [Field F] [IsAlgClosed F] (W : WeierstrassCurve F) [W.IsElliptic] (x : F) :
    ∃ y : F, W.toAffine.Nonsingular x y := by
  let q : Polynomial F := Polynomial.X ^ 2 + (Polynomial.C (W.a₁ * x + W.a₃) * Polynomial.X -
    Polynomial.C (x ^ 3 + W.a₂ * x ^ 2 + W.a₄ * x + W.a₆))
  have hq : q.degree ≠ 0 := by
    have hr : (Polynomial.C (W.a₁ * x + W.a₃) * Polynomial.X -
        Polynomial.C (x ^ 3 + W.a₂ * x ^ 2 + W.a₄ * x + W.a₆)).degree < ((2 : ℕ) : WithBot ℕ) := by
      refine lt_of_le_of_lt (Polynomial.degree_sub_le _ _) (max_lt ?_ ?_)
      · exact lt_of_le_of_lt (Polynomial.degree_C_mul_X_le _) (by exact_mod_cast Nat.one_lt_two)
      · exact lt_of_le_of_lt Polynomial.degree_C_le (by exact_mod_cast Nat.zero_lt_two)
    have h2 : q.degree = ((2 : ℕ) : WithBot ℕ) := by
      have hX : (Polynomial.X ^ 2 : Polynomial F).degree = ((2 : ℕ) : WithBot ℕ) := Polynomial.degree_X_pow 2
      rw [← hX] at hr
      rw [← hX]
      exact Polynomial.degree_add_eq_left_of_degree_lt hr
    rw [h2]; exact ne_of_beq_false rfl
  obtain ⟨y, hy⟩ := IsAlgClosed.exists_root q hq
  refine ⟨y, WeierstrassCurve.Affine.equation_iff_nonsingular.mp ?_⟩
  rw [WeierstrassCurve.Affine.Equation, WeierstrassCurve.Affine.evalEval_polynomial]
  simp only [q, Polynomial.IsRoot.def, Polynomial.eval_add, Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_sub,
    Polynomial.eval_mul, Polynomial.eval_C] at hy
  linear_combination hy

theorem exists_integral_lift_of_zsmul_eq {Ω : Type*} [Field Ω] [IsAlgClosed Ω] [DecidableEq Ω] (ψ : 𝒪 →+* Ω)
    (W : WeierstrassCurve 𝒪) {WK : WeierstrassCurve K} (hWK : WK = W.map (algebraMap 𝒪 K)) [WK.IsElliptic]
    {WΩ : WeierstrassCurve Ω} (hWΩ : WΩ = W.map ψ) [WΩ.IsElliptic]
    {n : ℕ} (hn : IsUnit ((n : ℕ) : (𝒪 : Type _))) {xT yT : 𝒪}
    (hTK : WK.toAffine.Nonsingular (algebraMap 𝒪 K xT) (algebraMap 𝒪 K yT)) (hTΩ : WΩ.toAffine.Nonsingular (ψ xT) (ψ yT))
    (hTn : (n : ℤ) • WeierstrassCurve.Affine.Point.some _ _ hTK = 0)
    (R' : WΩ.toAffine.Point) (hR' : (n : ℤ) • R' = WeierstrassCurve.Affine.Point.some _ _ hTΩ) :
    ∃ (xR yR : 𝒪) (hR : WK.toAffine.Nonsingular (algebraMap 𝒪 K xR) (algebraMap 𝒪 K yR))
      (hRΩ : WΩ.toAffine.Nonsingular (ψ xR) (ψ yR)),
      (n : ℤ) • WeierstrassCurve.Affine.Point.some _ _ hR = WeierstrassCurve.Affine.Point.some _ _ hTK ∧
        R' = WeierstrassCurve.Affine.Point.some _ _ hRΩ := by
  set ι := algebraMap 𝒪 K with hιdef
  have hι : Function.Injective ι := IsFractionRing.injective 𝒪 K
  have hn0 : n ≠ 0 := by rintro rfl; exact hn.ne_zero (by simp)
  have hnz : (n : ℤ) ≠ 0 := by exact_mod_cast hn0
  have hnK : ((n : ℤ) : K) ≠ 0 := by
    rw [Int.cast_natCast]; simpa using (hn.map ι).ne_zero
  have hnΩ : ((n : ℤ) : Ω) ≠ 0 := by
    rw [Int.cast_natCast]; simpa using (hn.map ψ).ne_zero

  rcases R' with _ | ⟨x', y', h'⟩
  · exfalso
    have h0 : (n : ℤ) • (0 : WΩ.toAffine.Point) = WeierstrassCurve.Affine.Point.some _ _ hTΩ := hR'
    rw [smul_zero] at h0
    exact WeierstrassCurve.Affine.Point.some_ne_zero _ h0.symm

  subst hWΩ
  have hxid := WeierstrassCurve.Affine.Point.zsmul_x_mul_psi_sq (W.map ψ) n h' hTΩ hR'
  rw [WeierstrassCurve.Affine.evalEval_psi_sq (W.map ψ) h'.1 n, evalEval_φ (W.map ψ) h'.1 n] at hxid
  let F : Polynomial 𝒪 := W.Φ n - Polynomial.C xT * W.ΨSq n
  have hF : F.Monic := monic_Phi_sub W hnz xT
  have hFx' : (F.map ψ).eval x' = 0 := by
    simp only [F, Polynomial.map_sub, Polynomial.map_mul, Polynomial.map_C, ← WeierstrassCurve.map_Φ,
      ← WeierstrassCurve.map_ΨSq, Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_C, ← hxid, sub_self]
  obtain ⟨ξ, hξ, hξx'⟩ := exists_root_of_eval_map_eq_zero 𝒪 ψ F hF hFx'

  subst hWK
  obtain ⟨η, hη⟩ := exists_nonsingular (W.map ι) (ι ξ)
  have hηmem : η ∈ 𝒪 := yc_mem_of_xc_mem 𝒪 W hη.1 ξ.2
  obtain ⟨η₀, rfl⟩ : ∃ η₀ : 𝒪, ι η₀ = η := ⟨⟨η, hηmem⟩, rfl⟩

  have hdesc : ∀ {a b : 𝒪}, (W.map ι).toAffine.Equation (ι a) (ι b) → (W.map ψ).toAffine.Nonsingular (ψ a) (ψ b) := by
    intro a b hab
    have h𝒪 : W.toAffine.Equation a b := by
      have h1 : ι (W.toAffine.polynomial.evalEval a b) = 0 := by
        rw [← Polynomial.map_mapRingHom_evalEval, ← WeierstrassCurve.Affine.map_polynomial]; exact hab
      exact (map_eq_zero_iff ι hι).mp h1
    exact WeierstrassCurve.Affine.equation_iff_nonsingular.mp (h𝒪.map ψ)

  have hΦK : ((W.map ι).Φ n).eval (ι ξ) = ι xT * ((W.map ι).ΨSq n).eval (ι ξ) := by
    have h1 := congrArg ι hξ
    simp only [F, Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_C, map_sub, map_mul, map_zero,
      sub_eq_zero] at h1
    rw [WeierstrassCurve.map_Φ, WeierstrassCurve.map_ΨSq, Polynomial.eval_map, Polynomial.eval_map,
      Polynomial.eval₂_at_apply, Polynomial.eval₂_at_apply]
    exact h1
  have hΨK : ((W.map ι).ΨSq n).eval (ι ξ) ≠ 0 := by
    intro h0
    refine not_common_root (WeierstrassCurve.isCoprime_Phi_PsiSq (W.map ι) n) (a := ι ξ) ?_ h0
    rw [hΦK, h0, mul_zero]
  have hψR₀ : ((W.map ι).ψ n).evalEval (ι ξ) (ι η₀) ≠ 0 := by
    intro h0
    apply hΨK
    rw [← WeierstrassCurve.Affine.evalEval_psi_sq (W.map ι) hη.1 n, h0]; ring

  obtain ⟨y'', h'', hmul⟩ := WeierstrassCurve.Affine.Point.zsmul_some_eq_some_div (W.map ι) hη hψR₀ (n := n)
  have hxT : ((W.map ι).Φ n).eval (ι ξ) / ((W.map ι).ΨSq n).eval (ι ξ) = ι xT := by
    rw [div_eq_iff hΨK, hΦK]
  simp only [hxT] at h'' hmul

  let ν₀ : 𝒪 := -η₀ - W.a₁ * ξ - W.a₃
  have hν₀ : ι ν₀ = (W.map ι).toAffine.negY (ι ξ) (ι η₀) := by
    simp only [ν₀, WeierstrassCurve.Affine.negY, map_sub, map_neg, map_mul, WeierstrassCurve.map_a₁,
      WeierstrassCurve.map_a₃]
  have hν₀ψ : ψ ν₀ = (W.map ψ).toAffine.negY (ψ ξ) (ψ η₀) := by
    simp only [ν₀, WeierstrassCurve.Affine.negY, map_sub, map_neg, map_mul, WeierstrassCurve.map_a₁,
      WeierstrassCurve.map_a₃]
  have hηneg : (W.map ι).toAffine.Nonsingular (ι ξ) (ι ν₀) := by
    rw [hν₀]; exact (WeierstrassCurve.Affine.nonsingular_neg _ _).mpr hη
  have hnegpt : WeierstrassCurve.Affine.Point.some _ _ hηneg = -WeierstrassCurve.Affine.Point.some _ _ hη := by
    rw [WeierstrassCurve.Affine.Point.neg_some]
    simp only [hν₀]

  obtain ⟨yR, hR, hRn⟩ : ∃ (yR : 𝒪) (hR : (W.map ι).toAffine.Nonsingular (ι ξ) (ι yR)),
      (n : ℤ) • WeierstrassCurve.Affine.Point.some _ _ hR = WeierstrassCurve.Affine.Point.some _ _ hTK := by
    rcases eq_or_eq_neg_of_xc_eq (W.map ι) hTK h'' with hc | hc
    · exact ⟨η₀, hη, hmul.trans hc⟩
    · refine ⟨ν₀, hηneg, ?_⟩
      rw [hnegpt, smul_neg, hmul, hc, neg_neg]

  have hRΩ : (W.map ψ).toAffine.Nonsingular (ψ ξ) (ψ yR) := hdesc hR.1
  have hRΩn := zsmul_some_eq_some_of_specialisation ι hι ψ W rfl rfl (n : ℤ) hR hTK hRΩ hTΩ hRn

  subst hξx'
  rcases eq_or_eq_neg_of_xc_eq (W.map ψ) hRΩ h' with hc | hc
  · exact ⟨ξ, yR, hR, hRΩ, hRn, hc⟩
  ·
    have hTneg : WeierstrassCurve.Affine.Point.some _ _ hTΩ = -WeierstrassCurve.Affine.Point.some _ _ hTΩ := by
      have h1 := hR'
      rw [hc, smul_neg, hRΩn] at h1
      exact h1.symm

    let νR : 𝒪 := -yR - W.a₁ * ξ - W.a₃
    have hνR : ι νR = (W.map ι).toAffine.negY (ι ξ) (ι yR) := by
      simp only [νR, WeierstrassCurve.Affine.negY, map_sub, map_neg, map_mul, WeierstrassCurve.map_a₁,
        WeierstrassCurve.map_a₃]
    have hνRψ : ψ νR = (W.map ψ).toAffine.negY (ψ ξ) (ψ yR) := by
      simp only [νR, WeierstrassCurve.Affine.negY, map_sub, map_neg, map_mul, WeierstrassCurve.map_a₁,
        WeierstrassCurve.map_a₃]
    have hRneg : (W.map ι).toAffine.Nonsingular (ι ξ) (ι νR) := by
      rw [hνR]; exact (WeierstrassCurve.Affine.nonsingular_neg _ _).mpr hR
    have hRnegpt : WeierstrassCurve.Affine.Point.some _ _ hRneg = -WeierstrassCurve.Affine.Point.some _ _ hR := by
      rw [WeierstrassCurve.Affine.Point.neg_some]; simp only [hνR]
    have hRnegΩ : (W.map ψ).toAffine.Nonsingular (ψ ξ) (ψ νR) := hdesc hRneg.1
    have hRnegΩpt : WeierstrassCurve.Affine.Point.some _ _ hRnegΩ = -WeierstrassCurve.Affine.Point.some _ _ hRΩ := by
      rw [WeierstrassCurve.Affine.Point.neg_some]; simp only [hνRψ]
    by_cases hTK2 : WeierstrassCurve.Affine.Point.some _ _ hTK = -WeierstrassCurve.Affine.Point.some _ _ hTK
    ·
      refine ⟨ξ, νR, hRneg, hRnegΩ, ?_, ?_⟩
      · rw [hRnegpt, smul_neg, hRn, ← hTK2]
      · rw [hc, hRnegΩpt]
    ·
      exfalso
      have h2ne : (2 : ℤ) • WeierstrassCurve.Affine.Point.some _ _ hTK ≠ 0 := by
        rw [two_smul]
        exact fun h0 => hTK2 (eq_neg_of_add_eq_zero_left h0)
      obtain ⟨xQ, yQ, hQ, hQeq⟩ : ∃ (xQ yQ : K) (hQ : (W.map ι).toAffine.Nonsingular xQ yQ),
          (2 : ℤ) • WeierstrassCurve.Affine.Point.some _ _ hTK = WeierstrassCurve.Affine.Point.some _ _ hQ := by
        rcases hQ' : (2 : ℤ) • WeierstrassCurve.Affine.Point.some _ _ hTK with _ | ⟨xQ, yQ, hQ⟩
        · exact absurd hQ' h2ne
        · exact ⟨xQ, yQ, hQ, rfl⟩
      have hQn : (n : ℤ) • WeierstrassCurve.Affine.Point.some _ _ hQ = 0 := by
        rw [← hQeq, smul_comm, hTn, smul_zero]
      have hxQ : xQ ∈ 𝒪 := xc_mem_of_zsmul_eq_zero 𝒪 W hn hQ hQn
      obtain ⟨xQ₀, rfl⟩ : ∃ xQ₀ : 𝒪, ι xQ₀ = xQ := ⟨⟨xQ, hxQ⟩, rfl⟩
      have hyQ : yQ ∈ 𝒪 := yc_mem_of_xc_mem 𝒪 W hQ.1 xQ₀.2
      obtain ⟨yQ₀, rfl⟩ : ∃ yQ₀ : 𝒪, ι yQ₀ = yQ := ⟨⟨yQ, hyQ⟩, rfl⟩
      have hQΩ : (W.map ψ).toAffine.Nonsingular (ψ xQ₀) (ψ yQ₀) := hdesc hQ.1
      have h2Ω := zsmul_some_eq_some_of_specialisation ι hι ψ W rfl rfl (2 : ℤ) hTK hQ hTΩ hQΩ hQeq
      have h2zero : (2 : ℤ) • WeierstrassCurve.Affine.Point.some _ _ hTΩ = 0 := by
        rw [two_smul]
        nth_rewrite 2 [hTneg]
        exact add_neg_cancel _
      rw [h2zero] at h2Ω
      exact WeierstrassCurve.Affine.Point.some_ne_zero _ h2Ω.symm

end Surj

section Field

variable {F K : Type*} [Field F] [Field K] [Algebra F K] (W : WeierstrassCurve F)

scoped instance isElliptic_baseChange [W.IsElliptic] : (W.baseChange K).IsElliptic :=
  show (W.map (algebraMap F K)).IsElliptic from inferInstance

private scoped instance _root_.P2M.WeilRed.isDedekindDomain [IsAlgClosed K] [W.IsElliptic] : IsDedekindDomain (W⁄K).CoordinateRing :=
  WeierstrassCurve.Affine.CoordinateRing.isDedekindDomain (W.baseChange K)

p2m_export "P2M.WeilRed" "isDedekindDomain"

theorem evalAt_algebraMap {a b : K} (h : (W⁄K).Equation a b) (c : K) :
    CoordinateRing.evalAt W K h (algebraMap K (W⁄K).CoordinateRing c) = c := by
  change CoordinateRing.evalAt W K h (CoordinateRing.mk (W⁄K) (C (C c))) = c
  rw [CoordinateRing.evalAt_mk, evalEval_C, eval_C]

theorem evalAt_smul_basis {a b : K} (h : (W⁄K).Equation a b) (p q : K[X]) :
    CoordinateRing.evalAt W K h (p • (1 : (W⁄K).CoordinateRing) + q • CoordinateRing.mk (W⁄K) Y) =
      p.eval a + q.eval a * b := by
  rw [map_add, CoordinateRing.smul, CoordinateRing.smul, mul_one, map_mul, CoordinateRing.evalAt_mk,
    CoordinateRing.evalAt_mk, CoordinateRing.evalAt_mk, evalEval_C, evalEval_C, evalEval_X]

theorem norm_ne_zero {h : (W⁄K).CoordinateRing} (h0 : h ≠ 0) : Algebra.norm (Polynomial K) h ≠ 0 :=
  (Algebra.norm_ne_zero_iff_of_basis (CoordinateRing.basis (W⁄K))).mpr h0

theorem natDegree_norm_algebraMap_mul {c : K} (hc : c ≠ 0) (h : (W⁄K).CoordinateRing) :
    (Algebra.norm (Polynomial K) (algebraMap K (W⁄K).CoordinateRing c * h)).natDegree =
      (Algebra.norm (Polynomial K) h).natDegree := by
  rw [map_mul, IsScalarTower.algebraMap_apply K K[X] (W⁄K).CoordinateRing,
    Algebra.norm_algebraMap_of_basis (CoordinateRing.basis (W⁄K)), Fintype.card_fin, Polynomial.algebraMap_eq,
    ← C_pow, natDegree_C_mul (pow_ne_zero 2 hc)]

theorem exists_eq_algebraMap_of_natDegree_norm_eq_zero {q : (W⁄K).CoordinateRing} (hq : q ≠ 0)
    (hd : (Algebra.norm (Polynomial K) q).natDegree = 0) :
    ∃ c : K, c ≠ 0 ∧ q = algebraMap K (W⁄K).CoordinateRing c := by
  obtain ⟨p, r, rfl⟩ := CoordinateRing.exists_smul_basis_eq q
  have hdeg := CoordinateRing.degree_norm_smul_basis (W' := W⁄K) p r
  have hN0 := norm_ne_zero W hq
  have hdeg0 : (Algebra.norm (Polynomial K) (p • (1 : (W⁄K).CoordinateRing) + r • CoordinateRing.mk (W⁄K) Y)).degree = 0 := by
    rw [degree_eq_natDegree hN0, hd]; rfl
  rw [hdeg0] at hdeg
  have hr : r = 0 := by
    by_contra hr
    have h0r : (0 : WithBot ℕ) ≤ r.degree := zero_le_degree_iff.mpr hr
    have h3 : (3 : WithBot ℕ) ≤ 2 • r.degree + 3 := le_add_of_nonneg_left (nsmul_nonneg h0r 2)
    have h3' : (3 : WithBot ℕ) ≤ 0 := h3.trans (hdeg.symm ▸ le_max_right _ _)
    have h3'' : ((3 : ℕ) : WithBot ℕ) ≤ ((0 : ℕ) : WithBot ℕ) := h3'
    have := WithBot.coe_le_coe.mp h3''
    omega
  subst hr
  have hp0 : p ≠ 0 := by
    rintro rfl
    exact hq (by simp)
  have h0p : (0 : WithBot ℕ) ≤ p.degree := zero_le_degree_iff.mpr hp0
  have hp2 : p.degree ≤ 2 • p.degree := by
    rw [two_nsmul]; exact le_add_of_nonneg_left h0p
  have hple : p.degree ≤ 0 := hp2.trans (hdeg.symm ▸ le_max_left _ _)
  refine ⟨p.coeff 0, ?_, ?_⟩
  · intro hc
    apply hp0
    rw [eq_C_of_degree_le_zero hple, hc, C_0]
  · conv_lhs => rw [eq_C_of_degree_le_zero hple]
    rw [zero_smul, add_zero, CoordinateRing.smul, mul_one]
    rfl

variable [IsAlgClosed K] [W.IsElliptic]

theorem evalAt_eq_zero_iff (P : (W⁄K).Point) (hP : P ≠ 0) (b : (W⁄K).CoordinateRing) :
    CoordinateRing.evalAt W K (Point.nonsingular_xc_yc hP).left b = 0 ↔
      (placeOf W K P hP).valuation (W⁄K).FunctionField
        (algebraMap (W⁄K).CoordinateRing (W⁄K).FunctionField b) < 1 := by
  rw [valuation_lt_one_iff_mem, mem_placeOf_iff W K P hP]

variable [DecidableEq K]

theorem evalAt_weilNum_eq_zero_iff {n : ℕ} (hn : (n : K) ≠ 0) {T : (W⁄K).Point} (hT : (n : ℤ) • T = 0)
    {a b : K} (hab : (W⁄K).Nonsingular a b) :
    CoordinateRing.evalAt W K hab.left (weilNum W K n T) = 0 ↔ (n : ℤ) • Point.some a b hab = T := by
  have hP : Point.some a b hab ≠ 0 := Point.some_ne_zero _
  have := evalAt_eq_zero_iff W _ hP (weilNum W K n T)
  change CoordinateRing.evalAt W K hab.left (weilNum W K n T) = 0 ↔ _ at this
  rw [this, valuation_weilNum W hn hT _ hP]
  by_cases h : (n : ℤ) • Point.some a b hab = T
  · simp only [h, if_true, iff_true]
    rw [← exp_zero, exp_lt_exp]; norm_num
  · simp only [h, if_false, lt_self_iff_false]

theorem exists_eq_algebraMap_mul_weilNum {n : ℕ} (hn : (n : K) ≠ 0) {T : (W⁄K).Point} (hT : (n : ℤ) • T = 0)
    {h : (W⁄K).CoordinateRing} (h0 : h ≠ 0)
    (hvan : ∀ (x y : K) (hxy : (W⁄K).Nonsingular x y), (n : ℤ) • Point.some x y hxy = T →
      CoordinateRing.evalAt W K hxy.left h = 0)
    (hdeg : (Algebra.norm (Polynomial K) h).natDegree ≤ (Algebra.norm (Polynomial K) (weilNum W K n T)).natDegree) :
    ∃ c : K, c ≠ 0 ∧ h = algebraMap K (W⁄K).CoordinateRing c * weilNum W K n T := by
  have hN0 : weilNum W K n T ≠ 0 := weilNum_ne_zero W hn hT
  have hNL0 : algebraMap (W⁄K).CoordinateRing (W⁄K).FunctionField (weilNum W K n T) ≠ 0 :=
    fun e => hN0 ((map_eq_zero_iff _ (IsFractionRing.injective _ _)).mp e)
  have hval : ∀ v : HeightOneSpectrum (W⁄K).CoordinateRing, v.valuation (W⁄K).FunctionField
      (algebraMap _ (W⁄K).FunctionField h / algebraMap _ (W⁄K).FunctionField (weilNum W K n T)) ≤ 1 := by
    intro v
    obtain ⟨P, hP, rfl⟩ := placeOf_surjective W K v
    rw [map_div₀, valuation_weilNum W hn hT P hP]
    by_cases hPT : (n : ℤ) • P = T
    · rw [if_pos hPT]
      have hlt : (placeOf W K P hP).valuation (W⁄K).FunctionField (algebraMap _ (W⁄K).FunctionField h) < 1 := by
        rw [← evalAt_eq_zero_iff W P hP]
        have hPeq := Point.eq_some_xc_yc hP
        exact hvan P.xc P.yc (Point.nonsingular_xc_yc hP) (by rw [← hPeq]; exact hPT)
      rw [lt_one_iff_le_exp_neg_one] at hlt
      rwa [div_le_one₀ exp_pos]
    · rw [if_neg hPT, div_one]
      exact valuation_le_one _ _
  obtain ⟨q, hq⟩ := mem_integers_of_valuation_le_one (W⁄K).FunctionField _ hval
  have hhq : h = q * weilNum W K n T := by
    apply IsFractionRing.injective (W⁄K).CoordinateRing (W⁄K).FunctionField
    rw [map_mul, hq, div_mul_cancel₀ _ hNL0]
  have hq0 : q ≠ 0 := by
    rintro rfl; rw [zero_mul] at hhq; exact h0 hhq
  have hnat : (Algebra.norm (Polynomial K) q).natDegree = 0 := by
    have hmul : Algebra.norm (Polynomial K) h =
        Algebra.norm (Polynomial K) q * Algebra.norm (Polynomial K) (weilNum W K n T) := by
      rw [hhq, map_mul]
    have := natDegree_mul (norm_ne_zero W hq0) (norm_ne_zero W hN0)
    rw [← hmul] at this
    omega
  obtain ⟨c, hc0, hc⟩ := exists_eq_algebraMap_of_natDegree_norm_eq_zero W hq0 hnat
  exact ⟨c, hc0, by rw [hhq, hc]⟩

omit [IsAlgClosed K] [W.IsElliptic] [DecidableEq K] in

theorem count_eq_of_valuation_eq {R : Type*} [CommRing R] [IsDedekindDomain R] {L : Type*} [Field L]
    [Algebra R L] [IsFractionRing R L] (v : HeightOneSpectrum R) {a : R} (ha : a ≠ 0) (m : ℕ)
    (hv : v.valuation L (algebraMap R L a) = exp (-(m : ℤ))) :
    FractionalIdeal.count L v (FractionalIdeal.spanSingleton R⁰ (algebraMap R L a)) = m := by
  have hspan : (Ideal.span {a} : Ideal R) ≠ ⊥ := by
    rw [Ne, Ideal.span_singleton_eq_bot]; exact ha
  rw [← FractionalIdeal.coeIdeal_span_singleton, FractionalIdeal.count_coe L v hspan]
  rw [valuation_of_algebraMap, intValuation_if_neg v ha, exp_inj, neg_inj] at hv
  exact_mod_cast hv

omit [DecidableEq K] in

theorem placeOf_bijective :
    Function.Bijective (fun P : {P : (W⁄K).Point // P ≠ 0} => placeOf W K P.1 P.2) := by
  constructor
  · rintro ⟨P, hP⟩ ⟨Q, hQ⟩ h
    exact Subtype.ext (placeOf_injective W K hP hQ h)
  · intro v
    obtain ⟨P, hP, h⟩ := placeOf_surjective W K v
    exact ⟨⟨P, hP⟩, h⟩

theorem natDegree_norm_weilNum {n : ℕ} (hn : (n : K) ≠ 0) {T : (W⁄K).Point} (hT : (n : ℤ) • T = 0) :
    (Algebra.norm (Polynomial K) (weilNum W K n T)).natDegree = if T = 0 then n ^ 2 - 1 else n ^ 2 := by
  classical
  have h0 : weilNum W K n T ≠ 0 := weilNum_ne_zero W hn hT
  have hZ := WeierstrassCurve.Affine.CoordinateRing.natDegree_norm_eq_finsum_count (W.baseChange K) h0
  have hcount : ∀ P : {P : (W⁄K).Point // P ≠ 0},
      FractionalIdeal.count (W⁄K).FunctionField (placeOf W K P.1 P.2)
        (FractionalIdeal.spanSingleton (W⁄K).CoordinateRing⁰
          (algebraMap (W⁄K).CoordinateRing (W⁄K).FunctionField (weilNum W K n T))) =
        if (n : ℤ) • P.1 = T then (1 : ℤ) else 0 := by
    rintro ⟨P, hP⟩
    have hv := valuation_weilNum W hn hT P hP
    by_cases hPT : (n : ℤ) • P = T
    · rw [if_pos hPT] at hv ⊢
      have := count_eq_of_valuation_eq (L := (W⁄K).FunctionField) (placeOf W K P hP) h0 1
        (by rw [hv, Nat.cast_one])
      rw [this, Nat.cast_one]
    · rw [if_neg hPT] at hv ⊢
      have := count_eq_of_valuation_eq (L := (W⁄K).FunctionField) (placeOf W K P hP) h0 0
        (by rw [hv, Nat.cast_zero, neg_zero, exp_zero])
      rw [this, Nat.cast_zero]
  rw [← finsum_comp _ (placeOf_bijective W)] at hZ
  simp only [hcount] at hZ
  have hfin : (fibSet W K n T).Finite := fibSet_finite W hn T
  set g : {P : (W⁄K).Point // P ≠ 0} → ℤ := fun P => if (n : ℤ) • P.1 = T then 1 else 0 with hg
  have hsupp : Function.support g ⊆
      ((hfin.toFinset.subtype fun P : (W⁄K).Point => P ≠ 0 : Finset _) : Set _) := by
    intro P hP
    rw [Function.mem_support] at hP
    simp only [hg, ne_eq, ite_eq_right_iff, one_ne_zero, imp_false, not_not] at hP
    rw [Finset.mem_coe, Finset.mem_subtype, Set.Finite.mem_toFinset, mem_fibSet]
    exact hP
  rw [finsum_eq_sum_of_support_subset g hsupp] at hZ
  simp only [hg, Finset.sum_boole] at hZ
  have hfilter : ((hfin.toFinset.subtype fun P : (W⁄K).Point => P ≠ 0).filter
      fun P : {P : (W⁄K).Point // P ≠ 0} => (n : ℤ) • P.1 = T) =
      hfin.toFinset.subtype fun P : (W⁄K).Point => P ≠ 0 := by
    apply Finset.filter_true_of_mem
    intro P hP
    simpa only [Finset.mem_subtype, Set.Finite.mem_toFinset, mem_fibSet] using hP
  rw [hfilter, Finset.card_subtype] at hZ
  have hcard : (hfin.toFinset.filter fun P : (W⁄K).Point => P ≠ 0).card = (fibSet W K n T \ {0}).ncard := by
    rw [Set.ncard_eq_toFinset_card _ (hfin.diff)]
    congr 1
    ext P
    simp only [Finset.mem_filter, Set.Finite.mem_toFinset, Set.mem_diff, Set.mem_singleton_iff]
  rw [hcard] at hZ
  have hncard := ncard_fibSet W hn T
  have hres : (fibSet W K n T \ {0}).ncard = if T = 0 then n ^ 2 - 1 else n ^ 2 := by
    by_cases hT0 : T = 0
    · rw [if_pos hT0]
      have hmem : (0 : (W⁄K).Point) ∈ fibSet W K n T := by rw [mem_fibSet, smul_zero, hT0]
      rw [Set.ncard_diff_singleton_of_mem hmem, hncard]
    · rw [if_neg hT0]
      have hnot : (0 : (W⁄K).Point) ∉ fibSet W K n T := by
        rw [mem_fibSet, smul_zero]; exact fun h => hT0 h.symm
      rw [Set.diff_singleton_eq_self hnot, hncard]
  rw [hres] at hZ
  exact_mod_cast hZ

end Field

section Reduction

variable {K : Type*} [Field K] [IsAlgClosed K] [DecidableEq K] (𝒪 : ValuationSubring K)
  {Ω : Type*} [Field Ω] [IsAlgClosed Ω] [DecidableEq Ω] (ψ : 𝒪 →+* Ω)

omit [IsAlgClosed K] [DecidableEq K] in

theorem exists_scaling {V : Affine K} (h : V.CoordinateRing) (h0 : h ≠ 0) :
    ∃ (c : K) (p q : Polynomial 𝒪) (i : ℕ), c ≠ 0 ∧
      algebraMap K V.CoordinateRing c * h =
        (p.map (algebraMap 𝒪 K)) • (1 : V.CoordinateRing) + (q.map (algebraMap 𝒪 K)) • CoordinateRing.mk V Y ∧
      (p.coeff i = 1 ∨ q.coeff i = 1) := by
  classical
  obtain ⟨p', q', rfl⟩ := CoordinateRing.exists_smul_basis_eq h
  set s : Finset K := p'.coeffs ∪ q'.coeffs with hs_def
  have hs : s.Nonempty := by
    by_contra hs
    rw [Finset.not_nonempty_iff_eq_empty, hs_def, Finset.union_eq_empty, coeffs_empty_iff, coeffs_empty_iff] at hs
    apply h0
    rw [hs.1, hs.2, zero_smul, zero_smul, add_zero]
  obtain ⟨d, hd, hmax⟩ := s.exists_max_image 𝒪.valuation hs
  have hd' : ∃ i, (d = p'.coeff i ∧ p'.coeff i ≠ 0) ∨ (d = q'.coeff i ∧ q'.coeff i ≠ 0) := by
    rcases Finset.mem_union.mp hd with hd | hd
    · obtain ⟨i, hi, rfl⟩ := mem_coeffs_iff.mp hd
      exact ⟨i, Or.inl ⟨rfl, mem_support_iff.mp hi⟩⟩
    · obtain ⟨i, hi, rfl⟩ := mem_coeffs_iff.mp hd
      exact ⟨i, Or.inr ⟨rfl, mem_support_iff.mp hi⟩⟩
  obtain ⟨i, hi⟩ := hd'
  have hd0 : d ≠ 0 := by
    rcases hi with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> exact h1 ▸ h2
  have hvd : 0 < 𝒪.valuation d := (Valuation.pos_iff _).mpr hd0

  have hmem : ∀ a : K, (a = 0 ∨ a ∈ s) → d⁻¹ * a ∈ 𝒪 := by
    rintro a (rfl | ha)
    · rw [mul_zero]; exact zero_mem _
    · apply (𝒪.valuation_le_one_iff _).mp
      rw [map_mul, map_inv₀, mul_comm, ← div_eq_mul_inv, div_le_one₀ hvd]
      exact hmax a ha
  have hlift : ∀ r : K[X], (∀ m, r.coeff m = 0 ∨ r.coeff m ∈ s) →
      ∃ r₀ : Polynomial 𝒪, r₀.map (algebraMap 𝒪 K) = C d⁻¹ * r := by
    intro r hr
    have : C d⁻¹ * r ∈ Polynomial.lifts (algebraMap 𝒪 K) := by
      rw [lifts_iff_coeff_lifts]
      intro m
      rw [coeff_C_mul]
      exact ⟨⟨_, hmem _ (hr m)⟩, rfl⟩
    exact (mem_lifts _).mp this
  have hp' : ∀ m, p'.coeff m = 0 ∨ p'.coeff m ∈ s := by
    intro m
    by_cases hm : p'.coeff m = 0
    · exact Or.inl hm
    · exact Or.inr (Finset.mem_union_left _ (coeff_mem_coeffs hm))
  have hq' : ∀ m, q'.coeff m = 0 ∨ q'.coeff m ∈ s := by
    intro m
    by_cases hm : q'.coeff m = 0
    · exact Or.inl hm
    · exact Or.inr (Finset.mem_union_right _ (coeff_mem_coeffs hm))
  obtain ⟨p, hp⟩ := hlift p' hp'
  obtain ⟨q, hq⟩ := hlift q' hq'
  refine ⟨d⁻¹, p, q, i, inv_ne_zero hd0, ?_, ?_⟩
  · rw [hp, hq, mul_add, CoordinateRing.smul, CoordinateRing.smul, CoordinateRing.smul,
      CoordinateRing.smul, C_mul, C_mul, map_mul, map_mul]
    simp only [mul_assoc]
    rfl
  · have hinj : Function.Injective (algebraMap 𝒪 K) := IsFractionRing.injective 𝒪 K
    rcases hi with ⟨h1, -⟩ | ⟨h1, -⟩
    · left
      apply (map_eq_one_iff (algebraMap 𝒪 K) hinj).mp
      rw [← coeff_map, hp, coeff_C_mul, ← h1, inv_mul_cancel₀ hd0]
    · right
      apply (map_eq_one_iff (algebraMap 𝒪 K) hinj).mp
      rw [← coeff_map, hq, coeff_C_mul, ← h1, inv_mul_cancel₀ hd0]

omit [IsAlgClosed K] [DecidableEq K] [IsAlgClosed Ω] [DecidableEq Ω] in

theorem natDegree_norm_map_le {V₁ : Affine K} {V₂ : Affine Ω} (p q : Polynomial 𝒪) :
    (Algebra.norm (Polynomial Ω) ((p.map ψ) • (1 : V₂.CoordinateRing) + (q.map ψ) • CoordinateRing.mk V₂ Y)).natDegree ≤
      (Algebra.norm (Polynomial K) ((p.map (algebraMap 𝒪 K)) • (1 : V₁.CoordinateRing) +
        (q.map (algebraMap 𝒪 K)) • CoordinateRing.mk V₁ Y)).natDegree := by
  have hinj : Function.Injective (algebraMap 𝒪 K) := IsFractionRing.injective 𝒪 K
  rw [natDegree_le_iff_degree_le]
  refine le_trans ?_ (degree_le_natDegree)
  rw [CoordinateRing.degree_norm_smul_basis, CoordinateRing.degree_norm_smul_basis,
    degree_map_eq_of_injective hinj, degree_map_eq_of_injective hinj]
  have hp : (p.map ψ).degree ≤ p.degree := degree_map_le
  have hq : (q.map ψ).degree ≤ q.degree := degree_map_le
  refine max_le_max ?_ ?_
  · rw [two_nsmul, two_nsmul]; exact add_le_add hp hp
  · rw [two_nsmul, two_nsmul]; exact add_le_add (add_le_add hq hq) le_rfl

omit [IsAlgClosed K] [DecidableEq K] [IsAlgClosed Ω] [DecidableEq Ω] in

theorem smul_basis_map_ne_zero {V₂ : Affine Ω} {p q : Polynomial 𝒪} {i : ℕ} (hi : p.coeff i = 1 ∨ q.coeff i = 1) :
    (p.map ψ) • (1 : V₂.CoordinateRing) + (q.map ψ) • CoordinateRing.mk V₂ Y ≠ 0 := by
  intro h
  obtain ⟨hp, hq⟩ := CoordinateRing.smul_basis_eq_zero h
  rcases hi with hi | hi
  · have := congrArg (fun r => Polynomial.coeff r i) hp
    simp only [coeff_map, hi, map_one, coeff_zero] at this
    exact one_ne_zero this
  · have := congrArg (fun r => Polynomial.coeff r i) hq
    simp only [coeff_map, hi, map_one, coeff_zero] at this
    exact one_ne_zero this

scoped instance isElliptic_baseChange_map (W : WeierstrassCurve 𝒪) [W.IsElliptic] {A : Type*} [CommRing A] (f : 𝒪 →+* A)
    (B : Type*) [CommRing B] [Algebra A B] : ((W.map f).baseChange B).IsElliptic :=
  show ((W.map f).map (algebraMap A B)).IsElliptic from inferInstance

theorem reduce (W : WeierstrassCurve 𝒪) [W.IsElliptic] {n : ℕ} (hnK : (n : K) ≠ 0) (hnΩ : (n : Ω) ≠ 0)
    (TK : ((W.map (algebraMap 𝒪 K))⁄K).Point) (TΩ : ((W.map ψ)⁄Ω).Point)
    (hTK : (n : ℤ) • TK = 0) (hTΩ : (n : ℤ) • TΩ = 0)
    (hdeg : (Algebra.norm (Polynomial K) (weilNum (W.map (algebraMap 𝒪 K)) K n TK)).natDegree =
      (Algebra.norm (Polynomial Ω) (weilNum (W.map ψ) Ω n TΩ)).natDegree)
    (hlift : ∀ (x' y' : Ω) (h' : ((W.map ψ)⁄Ω).Nonsingular x' y'), (n : ℤ) • Point.some x' y' h' = TΩ →
      ∃ (xR yR : 𝒪) (hR : ((W.map (algebraMap 𝒪 K))⁄K).Nonsingular (algebraMap 𝒪 K xR) (algebraMap 𝒪 K yR)),
        (n : ℤ) • Point.some _ _ hR = TK ∧ ψ xR = x' ∧ ψ yR = y') :
    ∃ (p q : Polynomial 𝒪) (c : K) (c' : Ω), c ≠ 0 ∧ c' ≠ 0 ∧
      (p.map (algebraMap 𝒪 K)) • (1 : ((W.map (algebraMap 𝒪 K))⁄K).CoordinateRing) +
          (q.map (algebraMap 𝒪 K)) • CoordinateRing.mk ((W.map (algebraMap 𝒪 K))⁄K) Y =
        algebraMap K _ c * weilNum (W.map (algebraMap 𝒪 K)) K n TK ∧
      (p.map ψ) • (1 : ((W.map ψ)⁄Ω).CoordinateRing) + (q.map ψ) • CoordinateRing.mk ((W.map ψ)⁄Ω) Y =
        algebraMap Ω _ c' * weilNum (W.map ψ) Ω n TΩ := by
  have hinj : Function.Injective (algebraMap 𝒪 K) := IsFractionRing.injective 𝒪 K
  have hN0 : weilNum (W.map (algebraMap 𝒪 K)) K n TK ≠ 0 := weilNum_ne_zero _ hnK hTK
  obtain ⟨c, p, q, i, hc0, hscale, hi⟩ := exists_scaling 𝒪 _ hN0
  have hbar0 := smul_basis_map_ne_zero 𝒪 ψ (V₂ := (W.map ψ)⁄Ω) hi

  have hvan : ∀ (x' y' : Ω) (h' : ((W.map ψ)⁄Ω).Nonsingular x' y'), (n : ℤ) • Point.some x' y' h' = TΩ →
      CoordinateRing.evalAt (W.map ψ) Ω h'.left
        ((p.map ψ) • (1 : ((W.map ψ)⁄Ω).CoordinateRing) + (q.map ψ) • CoordinateRing.mk ((W.map ψ)⁄Ω) Y) = 0 := by
    intro x' y' h' hn'
    obtain ⟨xR, yR, hR, hRn, rfl, rfl⟩ := hlift x' y' h' hn'
    rw [evalAt_smul_basis, eval_map, eval_map, eval₂_at_apply, eval₂_at_apply, ← map_mul, ← map_add]
    have hK : algebraMap 𝒪 K (p.eval xR + q.eval xR * yR) = 0 := by
      have := congrArg (CoordinateRing.evalAt (W.map (algebraMap 𝒪 K)) K hR.left) hscale
      rw [map_mul, evalAt_algebraMap, (evalAt_weilNum_eq_zero_iff _ hnK hTK hR).mpr hRn, mul_zero,
        evalAt_smul_basis, eval_map, eval_map, eval₂_at_apply, eval₂_at_apply, ← map_mul, ← map_add] at this
      exact this.symm
    rw [(map_eq_zero_iff _ hinj).mp hK, map_zero]

  have hdeg' : (Algebra.norm (Polynomial Ω)
      ((p.map ψ) • (1 : ((W.map ψ)⁄Ω).CoordinateRing) + (q.map ψ) • CoordinateRing.mk ((W.map ψ)⁄Ω) Y)).natDegree ≤
      (Algebra.norm (Polynomial Ω) (weilNum (W.map ψ) Ω n TΩ)).natDegree := by
    refine (natDegree_norm_map_le 𝒪 ψ (V₁ := (W.map (algebraMap 𝒪 K))⁄K) p q).trans ?_
    rw [← hscale, natDegree_norm_algebraMap_mul _ hc0, hdeg]
  obtain ⟨c', hc'0, hc'⟩ := exists_eq_algebraMap_mul_weilNum (W.map ψ) hnΩ hTΩ hbar0 hvan hdeg'
  exact ⟨p, q, c, c', hc0, hc'0, hscale.symm, hc'⟩

omit [IsAlgClosed Ω] in

theorem exists_integral_lift_of_zsmul_eq_zero (W : WeierstrassCurve 𝒪) {WK : WeierstrassCurve K}
    (hWK : WK = W.map (algebraMap 𝒪 K)) [WK.IsElliptic]
    {WΩ : WeierstrassCurve Ω} (hWΩ : WΩ = W.map ψ) [WΩ.IsElliptic]
    {n : ℕ} (hn : IsUnit ((n : ℕ) : (𝒪 : Type _)))
    {x' y' : Ω} (h' : WΩ.toAffine.Nonsingular x' y')
    (hR' : (n : ℤ) • WeierstrassCurve.Affine.Point.some _ _ h' = 0) :
    ∃ (xR yR : 𝒪) (hR : WK.toAffine.Nonsingular (algebraMap 𝒪 K xR) (algebraMap 𝒪 K yR)),
      (n : ℤ) • WeierstrassCurve.Affine.Point.some _ _ hR = 0 ∧ ψ xR = x' ∧ ψ yR = y' := by
  set ι := algebraMap 𝒪 K with hιdef
  have hι : Function.Injective ι := IsFractionRing.injective 𝒪 K
  have hn0 : ((n : ℤ) : (𝒪 : Type _)) ≠ 0 := by rw [Int.cast_natCast]; exact hn.ne_zero
  subst hWΩ
  subst hWK

  have hψ' := (WeierstrassCurve.Affine.Point.smul_some_eq_zero_iff (W.map ψ) h' (n : ℤ)).mp hR'
  have hΨ' : ((W.map ψ).ΨSq n).eval x' = 0 := by
    rw [← WeierstrassCurve.Affine.evalEval_psi_sq (W.map ψ) h'.1 n, hψ']; ring
  obtain ⟨u, hu⟩ := hn
  let a : (𝒪 : Type _) := ((u⁻¹ ^ 2 : (𝒪 : Type _)ˣ) : (𝒪 : Type _))
  have hlc : (W.ΨSq n).leadingCoeff = (u : (𝒪 : Type _)) ^ 2 := by
    rw [WeierstrassCurve.leadingCoeff_ΨSq W hn0, Int.cast_natCast, hu]
  have hG : (Polynomial.C a * W.ΨSq n).Monic := by
    refine Polynomial.monic_C_mul_of_mul_leadingCoeff_eq_one ?_
    rw [hlc, ← Units.val_pow_eq_pow_val, ← Units.val_mul, ← mul_pow, inv_mul_cancel, one_pow, Units.val_one]
  have hGx' : ((Polynomial.C a * W.ΨSq n).map ψ).eval x' = 0 := by
    rw [Polynomial.map_mul, Polynomial.map_C, ← WeierstrassCurve.map_ΨSq, Polynomial.eval_mul, hΨ', mul_zero]
  obtain ⟨ξ, hξ, hξx'⟩ := exists_root_of_eval_map_eq_zero 𝒪 ψ _ hG hGx'
  have hΨξ : (W.ΨSq n).eval ξ = 0 := by
    rw [Polynomial.eval_mul, Polynomial.eval_C] at hξ
    rcases mul_eq_zero.mp hξ with h | h
    · exact absurd h (Units.ne_zero _)
    · exact h

  obtain ⟨η, hη⟩ := exists_nonsingular (W.map ι) (ι ξ)
  have hηmem : η ∈ 𝒪 := yc_mem_of_xc_mem 𝒪 W hη.1 ξ.2
  obtain ⟨η₀, rfl⟩ : ∃ η₀ : 𝒪, ι η₀ = η := ⟨⟨η, hηmem⟩, rfl⟩
  have hdesc : ∀ {a b : 𝒪}, (W.map ι).toAffine.Equation (ι a) (ι b) → (W.map ψ).toAffine.Nonsingular (ψ a) (ψ b) := by
    intro a b hab
    have h𝒪 : W.toAffine.Equation a b := by
      have h1 : ι (W.toAffine.polynomial.evalEval a b) = 0 := by
        rw [← Polynomial.map_mapRingHom_evalEval, ← WeierstrassCurve.Affine.map_polynomial]; exact hab
      exact (map_eq_zero_iff ι hι).mp h1
    exact WeierstrassCurve.Affine.equation_iff_nonsingular.mp (h𝒪.map ψ)
  have htors : ∀ {b : 𝒪} (hb : (W.map ι).toAffine.Nonsingular (ι ξ) (ι b)),
      (n : ℤ) • WeierstrassCurve.Affine.Point.some _ _ hb = 0 := by
    intro b hb
    apply (WeierstrassCurve.Affine.Point.smul_some_eq_zero_iff (W.map ι) hb (n : ℤ)).mpr
    have h2 : ((W.map ι).ψ n).evalEval (ι ξ) (ι b) ^ 2 = 0 := by
      rw [WeierstrassCurve.Affine.evalEval_psi_sq (W.map ι) hb.1 n, WeierstrassCurve.map_ΨSq, Polynomial.eval_map,
        Polynomial.eval₂_at_apply, hΨξ, map_zero]
    exact pow_eq_zero_iff (two_ne_zero) |>.mp h2

  let ν₀ : 𝒪 := -η₀ - W.a₁ * ξ - W.a₃
  have hν₀ : ι ν₀ = (W.map ι).toAffine.negY (ι ξ) (ι η₀) := by
    simp only [ν₀, WeierstrassCurve.Affine.negY, map_sub, map_neg, map_mul, WeierstrassCurve.map_a₁,
      WeierstrassCurve.map_a₃]
  have hν₀ψ : ψ ν₀ = (W.map ψ).toAffine.negY (ψ ξ) (ψ η₀) := by
    simp only [ν₀, WeierstrassCurve.Affine.negY, map_sub, map_neg, map_mul, WeierstrassCurve.map_a₁,
      WeierstrassCurve.map_a₃]
  have hηneg : (W.map ι).toAffine.Nonsingular (ι ξ) (ι ν₀) := by
    rw [hν₀]; exact (WeierstrassCurve.Affine.nonsingular_neg _ _).mpr hη
  have hRΩ : (W.map ψ).toAffine.Nonsingular (ψ ξ) (ψ η₀) := hdesc hη.1
  have hRnegΩ : (W.map ψ).toAffine.Nonsingular (ψ ξ) (ψ ν₀) := hdesc hηneg.1
  have hRnegΩpt : WeierstrassCurve.Affine.Point.some _ _ hRnegΩ = -WeierstrassCurve.Affine.Point.some _ _ hRΩ := by
    rw [WeierstrassCurve.Affine.Point.neg_some]; simp only [hν₀ψ]
  subst hξx'
  rcases eq_or_eq_neg_of_xc_eq (W.map ψ) hRΩ h' with hc | hc
  · exact ⟨ξ, η₀, hη, htors hη, rfl, by
      have := (WeierstrassCurve.Affine.Point.some.injEq _ _ _ _ _ _).mp hc; exact this.2.symm⟩
  · refine ⟨ξ, ν₀, hηneg, htors hηneg, rfl, ?_⟩
    rw [← hRnegΩpt] at hc
    have := (WeierstrassCurve.Affine.Point.some.injEq _ _ _ _ _ _).mp hc
    exact this.2.symm

omit [IsAlgClosed K] [DecidableEq K] in

theorem natCast_ne_zero_of_isUnit {n : ℕ} (hn : IsUnit ((n : ℕ) : (𝒪 : Type _))) {A : Type*} [CommRing A] [Nontrivial A]
    (f : 𝒪 →+* A) : (n : A) ≠ 0 := by
  have := (hn.map f).ne_zero
  rwa [map_natCast] at this

theorem main (W : WeierstrassCurve 𝒪) [W.IsElliptic] {n : ℕ} (hn : IsUnit ((n : ℕ) : (𝒪 : Type _)))
    (TK : ((W.map (algebraMap 𝒪 K))⁄K).Point) (TΩ : ((W.map ψ)⁄Ω).Point)
    (hT : (TK = 0 ∧ TΩ = 0) ∨ ∃ (xT yT : 𝒪)
      (hK : ((W.map (algebraMap 𝒪 K))⁄K).Nonsingular (algebraMap 𝒪 K xT) (algebraMap 𝒪 K yT))
      (hΩ : ((W.map ψ)⁄Ω).Nonsingular (ψ xT) (ψ yT)), TK = Point.some _ _ hK ∧ TΩ = Point.some _ _ hΩ)
    (hTKn : (n : ℤ) • TK = 0) (hTΩn : (n : ℤ) • TΩ = 0) :
    ∃ (p q : Polynomial 𝒪) (c : K) (c' : Ω), c ≠ 0 ∧ c' ≠ 0 ∧
      (p.map (algebraMap 𝒪 K)) • (1 : ((W.map (algebraMap 𝒪 K))⁄K).CoordinateRing) +
          (q.map (algebraMap 𝒪 K)) • CoordinateRing.mk ((W.map (algebraMap 𝒪 K))⁄K) Y =
        algebraMap K _ c * weilNum (W.map (algebraMap 𝒪 K)) K n TK ∧
      (p.map ψ) • (1 : ((W.map ψ)⁄Ω).CoordinateRing) + (q.map ψ) • CoordinateRing.mk ((W.map ψ)⁄Ω) Y =
        algebraMap Ω _ c' * weilNum (W.map ψ) Ω n TΩ := by
  have hnK : (n : K) ≠ 0 := natCast_ne_zero_of_isUnit 𝒪 hn (algebraMap 𝒪 K)
  have hnΩ : (n : Ω) ≠ 0 := natCast_ne_zero_of_isUnit 𝒪 hn ψ
  refine reduce 𝒪 ψ W hnK hnΩ TK TΩ hTKn hTΩn ?_ ?_
  ·
    rw [natDegree_norm_weilNum _ hnK hTKn, natDegree_norm_weilNum _ hnΩ hTΩn]
    rcases hT with ⟨rfl, rfl⟩ | ⟨xT, yT, hK, hΩ, rfl, rfl⟩
    · simp only [if_true]
    · rw [if_neg (Point.some_ne_zero _), if_neg (Point.some_ne_zero _)]
  ·
    intro x' y' h' hn'
    rcases hT with ⟨rfl, rfl⟩ | ⟨xT, yT, hK, hΩ, rfl, rfl⟩
    · obtain ⟨xR, yR, hR, hRn, hx, hy⟩ :=
        exists_integral_lift_of_zsmul_eq_zero 𝒪 ψ W (WK := (W.map (algebraMap 𝒪 K)).baseChange K) rfl
          (WΩ := (W.map ψ).baseChange Ω) rfl hn h' hn'
      exact ⟨xR, yR, hR, hRn, hx, hy⟩
    · obtain ⟨xR, yR, hR, hRΩ, hRn, hR'⟩ :=
        exists_integral_lift_of_zsmul_eq 𝒪 ψ W (WK := (W.map (algebraMap 𝒪 K)).baseChange K) rfl
          (WΩ := (W.map ψ).baseChange Ω) rfl hn hK hΩ hTKn (Point.some x' y' h') hn'
      have := (WeierstrassCurve.Affine.Point.some.injEq _ _ _ _ _ _).mp hR'
      exact ⟨xR, yR, hR, hRn, this.1.symm, this.2.symm⟩

end Reduction

end P2M.WeilRed
p2m_reactivate "P2MW.S_WeierstrassCurve_Affine_exists_smul_basis_eq_algebraMap_mul_weilNum_of_valuationSubring.P2M P2MW.S_WeierstrassCurve_Affine_exists_smul_basis_eq_algebraMap_mul_weilNum_of_valuationSubring.P2M.WeilRed"
p2m_reactivate "P2MW.S_WeierstrassCurve_Affine_exists_smul_basis_eq_algebraMap_mul_weilNum_of_valuationSubring.P2M"

universe u v

open P2M.WeilRed in
theorem solution
    {K : Type u} [Field K] [IsAlgClosed K] [DecidableEq K] (𝒪 : ValuationSubring K)
    {Ω : Type v} [Field Ω] [IsAlgClosed Ω] [DecidableEq Ω] (ψ : 𝒪 →+* Ω)
    (W : WeierstrassCurve 𝒪) [W.IsElliptic] (n : ℕ) (hn : IsUnit ((n : ℕ) : (𝒪 : Type u)))
    (TK : ((W.map (algebraMap 𝒪 K)).baseChange K).toAffine.Point) (TΩ : ((W.map ψ).baseChange Ω).toAffine.Point)
    (hT : (TK = 0 ∧ TΩ = 0) ∨ ∃ (xT yT : 𝒪)
      (hTK : ((W.map (algebraMap 𝒪 K)).baseChange K).toAffine.Nonsingular (algebraMap 𝒪 K xT) (algebraMap 𝒪 K yT))
      (hTΩ : ((W.map ψ).baseChange Ω).toAffine.Nonsingular (ψ xT) (ψ yT)),
      TK = WeierstrassCurve.Affine.Point.some _ _ hTK ∧ TΩ = WeierstrassCurve.Affine.Point.some _ _ hTΩ)
    (hTKn : (n : ℤ) • TK = 0) (hTΩn : (n : ℤ) • TΩ = 0) :
    ∃ (p q : Polynomial 𝒪) (c : K) (c' : Ω), c ≠ 0 ∧ c' ≠ 0 ∧
      Polynomial.map (algebraMap 𝒪 K) p • (1 : ((W.map (algebraMap 𝒪 K)).baseChange K).toAffine.CoordinateRing) +
          Polynomial.map (algebraMap 𝒪 K) q •
            WeierstrassCurve.Affine.CoordinateRing.mk ((W.map (algebraMap 𝒪 K)).baseChange K).toAffine Y =
        algebraMap K _ c * weilNum (W.map (algebraMap 𝒪 K)) K n TK ∧
      Polynomial.map ψ p • (1 : ((W.map ψ).baseChange Ω).toAffine.CoordinateRing) +
          Polynomial.map ψ q • WeierstrassCurve.Affine.CoordinateRing.mk ((W.map ψ).baseChange Ω).toAffine Y =
        algebraMap Ω _ c' * weilNum (W.map ψ) Ω n TΩ :=
  P2M.WeilRed.main 𝒪 ψ W hn TK TΩ hT hTKn hTΩn

end S_WeierstrassCurve_Affine_exists_smul_basis_eq_algebraMap_mul_weilNum_of_valuationSubring
end P2MW
export P2MW.S_WeierstrassCurve_Affine_exists_smul_basis_eq_algebraMap_mul_weilNum_of_valuationSubring (solution)
