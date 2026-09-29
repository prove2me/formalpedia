-- Prove2me | solution 1 for WeierstrassCurve.Affine.weilPairing0_toPoint_variableChange
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.503601+00:00
-- url     : https://prove2.me/submissions/a7b4b559-5f02-5338-8614-4f95b8d5cdd3

import Mathlib
import Definitions.Def_ModularCurve_KatzLevelP
import Definitions.Def_ModularCurve_LevelRelabelling
import Definitions.Def_EllipticCurve_WeilPairingFun
import Definitions.Def_WeierstrassCurve_VariableChangePointEquiv
import Theorems.Thm_WeierstrassCurve_Affine_Point_vcInvFun_add
import Theorems.Thm_WeierstrassCurve_Affine_CoordinateRing_isUnit_iff_eq_algebraMap
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_WeierstrassCurve_Affine_weilPairing0_toPoint_variableChange

set_option autoImplicit false

universe u

open Polynomial WeierstrassCurve WeierstrassCurve.Affine
open scoped Polynomial.Bivariate

noncomputable section

namespace WeilIsoInvSol

section Eval

variable {K : Type u} [Field K] (W : WeierstrassCurve K) (L : Type*) [Field L] [Algebra K L]

theorem evalEval_baseChange_polynomial (x y : L) :
    (W⁄L).polynomial.evalEval x y = (W⁄K).polynomial.eval₂ (aeval (R := K) x).toRingHom y := by
  have hb : (W⁄L) = (W⁄K).map (Algebra.ofId K L) := by
    show W.map (algebraMap K L) = (W.map (algebraMap K K)).map (algebraMap K L)
    rw [WeierstrassCurve.map_map]
    rfl
  rw [hb, map_polynomial, evalEval, eval_map]
  have h := hom_eval₂ (W⁄K).polynomial (mapRingHom (Algebra.ofId K L : K →+* L)) (evalRingHom x) (Polynomial.C y)
  simp only [coe_evalRingHom, eval_C] at h
  rw [h]
  congr 1
  apply Polynomial.ringHom_ext
  · intro c
    simp only [RingHom.coe_comp, Function.comp_apply, coe_mapRingHom, map_C, coe_evalRingHom,
      eval_C, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, aeval_C]
    rfl
  · simp only [RingHom.coe_comp, Function.comp_apply, coe_mapRingHom, map_X, coe_evalRingHom,
      eval_X, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, aeval_X]

end Eval

section CoordIso

variable {K : Type u} [Field K] (W : WeierstrassCurve K) (cv : VariableChange K)

def ui : K := ((cv.u⁻¹ : Kˣ) : K)

theorem ui_mul_u : ui cv * (cv.u : K) = 1 := by
  simp [ui]

def xImg : (W⁄K).CoordinateRing :=
  algebraMap K _ (ui cv) ^ 2 * (CoordinateRing.mk (W⁄K) (Polynomial.C X) - algebraMap K _ cv.r)

def yImg : (W⁄K).CoordinateRing :=
  algebraMap K _ (ui cv) ^ 3 * (CoordinateRing.mk (W⁄K) Y -
    algebraMap K _ cv.s * (CoordinateRing.mk (W⁄K) (Polynomial.C X) - algebraMap K _ cv.r) - algebraMap K _ cv.t)

def xImg' : ((cv • W)⁄K).CoordinateRing :=
  algebraMap K _ (cv.u : K) ^ 2 * CoordinateRing.mk ((cv • W)⁄K) (Polynomial.C X) + algebraMap K _ cv.r

def yImg' : ((cv • W)⁄K).CoordinateRing :=
  algebraMap K _ (cv.u : K) ^ 3 * CoordinateRing.mk ((cv • W)⁄K) Y +
    algebraMap K _ (cv.u : K) ^ 2 * algebraMap K _ cv.s * CoordinateRing.mk ((cv • W)⁄K) (Polynomial.C X) +
      algebraMap K _ cv.t

theorem equation_img :
    ((cv • W)⁄(W⁄K).FunctionField).Equation
      (algebraMap _ (W⁄K).FunctionField (xImg W cv)) (algebraMap _ (W⁄K).FunctionField (yImg W cv)) := by
  set L := (W⁄K).FunctionField
  set φ : K →+* L := algebraMap K L
  have hgen := generic_equation W K
  have h := ModularCurve.IsLevelPStructure.equation_variableChange_aux (W := (W⁄L : WeierstrassCurve L))
    (cv.map φ) hgen
  have hcurve : cv.map φ • (W⁄L) = ((cv • W)⁄L) := by
    show cv.map φ • W.map φ = (cv • W).map φ
    rw [map_variableChange]
  rw [hcurve] at h
  have hu : (((cv.map φ).u⁻¹ : Lˣ) : L) = φ (ui cv) := by
    show (((Units.map (φ : K →* L) cv.u)⁻¹ : Lˣ) : L) = φ (ui cv)
    rw [Units.coe_map_inv]; rfl
  have hr : (cv.map φ).r = φ cv.r := rfl
  have hs : (cv.map φ).s = φ cv.s := rfl
  have ht : (cv.map φ).t = φ cv.t := rfl
  rw [hu, hr, hs, ht] at h
  have hx : algebraMap _ L (xImg W cv) = φ (ui cv) ^ 2 * (genericX W K - φ cv.r) := by
    simp only [xImg, map_mul, map_pow, map_sub, genericX]
    repeat rw [← IsScalarTower.algebraMap_apply]
  have hy : algebraMap _ L (yImg W cv) =
      φ (ui cv) ^ 3 * (genericY W K - φ cv.s * (genericX W K - φ cv.r) - φ cv.t) := by
    simp only [yImg, map_mul, map_pow, map_sub, genericX, genericY]
    repeat rw [← IsScalarTower.algebraMap_apply]
  rw [hx, hy]
  exact h

theorem equation_img' :
    (W⁄((cv • W)⁄K).FunctionField).Equation
      (algebraMap _ ((cv • W)⁄K).FunctionField (xImg' W cv))
      (algebraMap _ ((cv • W)⁄K).FunctionField (yImg' W cv)) := by
  set L := ((cv • W)⁄K).FunctionField
  set φ : K →+* L := algebraMap K L
  have hgen := generic_equation (cv • W) K
  have hcurve : ((cv • W)⁄L) = (cv.map φ) • (W⁄L) := by
    show (cv • W).map φ = cv.map φ • W.map φ
    rw [map_variableChange]
  rw [hcurve] at hgen
  have h := (equation_variableChange_iff (C := cv.map φ) (W := (W⁄L)) _ _).mp hgen
  have hu : (((cv.map φ).u : Lˣ) : L) = φ (cv.u : K) := rfl
  have hr : (cv.map φ).r = φ cv.r := rfl
  have hs : (cv.map φ).s = φ cv.s := rfl
  have ht : (cv.map φ).t = φ cv.t := rfl
  simp only [vcX, vcY, hu, hr, hs, ht] at h
  have hx : algebraMap _ L (xImg' W cv) = φ (cv.u : K) ^ 2 * genericX (cv • W) K + φ cv.r := by
    simp only [xImg', map_mul, map_pow, map_add, genericX]
    repeat rw [← IsScalarTower.algebraMap_apply]
  have hy : algebraMap _ L (yImg' W cv) =
      φ (cv.u : K) ^ 3 * genericY (cv • W) K + φ (cv.u : K) ^ 2 * φ cv.s * genericX (cv • W) K + φ cv.t := by
    simp only [yImg', map_mul, map_pow, map_add, genericX, genericY]
    repeat rw [← IsScalarTower.algebraMap_apply]
  rw [hx, hy]
  exact h

theorem cert :
    ((cv • W)⁄K).polynomial.eval₂ (aeval (R := K) (xImg W cv)).toRingHom (yImg W cv) = 0 := by
  apply IsFractionRing.injective (W⁄K).CoordinateRing (W⁄K).FunctionField
  rw [map_zero, hom_eval₂]
  have hcomp : (algebraMap (W⁄K).CoordinateRing (W⁄K).FunctionField).comp (aeval (R := K) (xImg W cv)).toRingHom =
      (aeval (R := K) (algebraMap _ (W⁄K).FunctionField (xImg W cv))).toRingHom := by
    apply Polynomial.ringHom_ext
    · intro c
      simp only [RingHom.coe_comp, Function.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, aeval_C]
      exact (IsScalarTower.algebraMap_apply K _ _ c).symm
    · simp only [RingHom.coe_comp, Function.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, aeval_X]
  rw [hcomp, ← evalEval_baseChange_polynomial]
  exact equation_img W cv

theorem cert' :
    (W⁄K).polynomial.eval₂ (aeval (R := K) (xImg' W cv)).toRingHom (yImg' W cv) = 0 := by
  apply IsFractionRing.injective ((cv • W)⁄K).CoordinateRing ((cv • W)⁄K).FunctionField
  rw [map_zero, hom_eval₂]
  have hcomp : (algebraMap ((cv • W)⁄K).CoordinateRing ((cv • W)⁄K).FunctionField).comp
        (aeval (R := K) (xImg' W cv)).toRingHom =
      (aeval (R := K) (algebraMap _ ((cv • W)⁄K).FunctionField (xImg' W cv))).toRingHom := by
    apply Polynomial.ringHom_ext
    · intro c
      simp only [RingHom.coe_comp, Function.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, aeval_C]
      exact (IsScalarTower.algebraMap_apply K _ _ c).symm
    · simp only [RingHom.coe_comp, Function.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, aeval_X]
  rw [hcomp, ← evalEval_baseChange_polynomial]
  exact equation_img' W cv

noncomputable def coordHom : ((cv • W)⁄K).CoordinateRing →ₐ[K] (W⁄K).CoordinateRing :=
  { AdjoinRoot.lift (aeval (R := K) (xImg W cv)).toRingHom (yImg W cv) (cert W cv) with
    commutes' := fun c => by
      simp only [RingHom.toMonoidHom_eq_coe, OneHom.toFun_eq_coe, MonoidHom.toOneHom_coe, MonoidHom.coe_coe]
      rw [IsScalarTower.algebraMap_apply K (Polynomial K) ((cv • W)⁄K).CoordinateRing,
        AdjoinRoot.algebraMap_eq, AdjoinRoot.lift_of, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
        Polynomial.algebraMap_apply, aeval_C, Algebra.algebraMap_self, RingHom.id_apply] }

noncomputable def coordHom' : (W⁄K).CoordinateRing →ₐ[K] ((cv • W)⁄K).CoordinateRing :=
  { AdjoinRoot.lift (aeval (R := K) (xImg' W cv)).toRingHom (yImg' W cv) (cert' W cv) with
    commutes' := fun c => by
      simp only [RingHom.toMonoidHom_eq_coe, OneHom.toFun_eq_coe, MonoidHom.toOneHom_coe, MonoidHom.coe_coe]
      rw [IsScalarTower.algebraMap_apply K (Polynomial K) (W⁄K).CoordinateRing,
        AdjoinRoot.algebraMap_eq, AdjoinRoot.lift_of, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
        Polynomial.algebraMap_apply, aeval_C, Algebra.algebraMap_self, RingHom.id_apply] }

theorem coordHom_mk (g : K[X][Y]) :
    coordHom W cv (CoordinateRing.mk ((cv • W)⁄K) g) = g.eval₂ (aeval (R := K) (xImg W cv)).toRingHom (yImg W cv) :=
  AdjoinRoot.lift_mk (cert W cv) g

theorem coordHom'_mk (g : K[X][Y]) :
    coordHom' W cv (CoordinateRing.mk (W⁄K) g) = g.eval₂ (aeval (R := K) (xImg' W cv)).toRingHom (yImg' W cv) :=
  AdjoinRoot.lift_mk (cert' W cv) g

@[scoped simp] theorem coordHom_X : coordHom W cv (CoordinateRing.mk ((cv • W)⁄K) (Polynomial.C X)) = xImg W cv := by
  rw [coordHom_mk, eval₂_C, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, aeval_X]

@[scoped simp] theorem coordHom_Y : coordHom W cv (CoordinateRing.mk ((cv • W)⁄K) Y) = yImg W cv := by
  rw [coordHom_mk, eval₂_X]

@[scoped simp] theorem coordHom'_X : coordHom' W cv (CoordinateRing.mk (W⁄K) (Polynomial.C X)) = xImg' W cv := by
  rw [coordHom'_mk, eval₂_C, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, aeval_X]

@[scoped simp] theorem coordHom'_Y : coordHom' W cv (CoordinateRing.mk (W⁄K) Y) = yImg' W cv := by
  rw [coordHom'_mk, eval₂_X]

theorem coordHom'_comp_coordHom : (coordHom' W cv).comp (coordHom W cv) = AlgHom.id K _ := by
  have hu : algebraMap K ((cv • W)⁄K).CoordinateRing (ui cv) * algebraMap K _ (cv.u : K) = 1 := by
    rw [← map_mul, ui_mul_u, map_one]
  apply CoordinateRing.algHom_ext'
  · rw [AlgHom.comp_apply, coordHom_X, AlgHom.id_apply, xImg]
    simp only [map_mul, map_pow, map_sub, AlgHom.commutes, coordHom'_X, xImg']
    linear_combination (algebraMap K ((cv • W)⁄K).CoordinateRing (ui cv) * algebraMap K _ (cv.u : K) + 1) *
      CoordinateRing.mk ((cv • W)⁄K) (Polynomial.C X) * hu
  · rw [AlgHom.comp_apply, coordHom_Y, AlgHom.id_apply, yImg]
    simp only [map_mul, map_pow, map_sub, AlgHom.commutes, coordHom'_X, coordHom'_Y, xImg', yImg']
    linear_combination
      ((algebraMap K ((cv • W)⁄K).CoordinateRing (ui cv)) ^ 2 * (algebraMap K _ (cv.u : K)) ^ 2 +
          algebraMap K ((cv • W)⁄K).CoordinateRing (ui cv) * algebraMap K _ (cv.u : K) + 1) *
        CoordinateRing.mk ((cv • W)⁄K) Y * hu

theorem coordHom_comp_coordHom' : (coordHom W cv).comp (coordHom' W cv) = AlgHom.id K _ := by
  have hu : algebraMap K (W⁄K).CoordinateRing (ui cv) * algebraMap K _ (cv.u : K) = 1 := by
    rw [← map_mul, ui_mul_u, map_one]
  apply CoordinateRing.algHom_ext'
  · rw [AlgHom.comp_apply, coordHom'_X, AlgHom.id_apply, xImg']
    simp only [map_mul, map_pow, map_add, AlgHom.commutes, coordHom_X, xImg]
    linear_combination (algebraMap K (W⁄K).CoordinateRing (ui cv) * algebraMap K _ (cv.u : K) + 1) *
      (CoordinateRing.mk (W⁄K) (Polynomial.C X) - algebraMap K _ cv.r) * hu
  · rw [AlgHom.comp_apply, coordHom'_Y, AlgHom.id_apply, yImg']
    simp only [map_mul, map_pow, map_add, AlgHom.commutes, coordHom_X, coordHom_Y, xImg, yImg]
    linear_combination
      (((algebraMap K (W⁄K).CoordinateRing (ui cv)) ^ 2 * (algebraMap K _ (cv.u : K)) ^ 2 +
          algebraMap K (W⁄K).CoordinateRing (ui cv) * algebraMap K _ (cv.u : K) + 1) *
        (CoordinateRing.mk (W⁄K) Y - algebraMap K _ cv.s * (CoordinateRing.mk (W⁄K) (Polynomial.C X) -
          algebraMap K _ cv.r) - algebraMap K _ cv.t) +
        (algebraMap K (W⁄K).CoordinateRing (ui cv) * algebraMap K _ (cv.u : K) + 1) * algebraMap K _ cv.s *
          (CoordinateRing.mk (W⁄K) (Polynomial.C X) - algebraMap K _ cv.r)) * hu

noncomputable def coordIso : ((cv • W)⁄K).CoordinateRing ≃ₐ[K] (W⁄K).CoordinateRing :=
  AlgEquiv.ofAlgHom (coordHom W cv) (coordHom' W cv) (coordHom_comp_coordHom' W cv) (coordHom'_comp_coordHom W cv)

theorem coordIso_apply (a : ((cv • W)⁄K).CoordinateRing) : coordIso W cv a = coordHom W cv a := rfl

end CoordIso

section Transport

variable {K : Type u} [Field K] [DecidableEq K] (W : WeierstrassCurve K) (cv : VariableChange K)

def ψ : (W⁄K).Point → ((cv • W)⁄K).Point := fun P => Point.vcInvFun cv (W⁄K) P

def ψE : (W⁄K).Point ≃+ ((cv • W)⁄K).Point :=
  { (Point.variableChangeEquiv cv (W⁄K)).symm with
    toFun := ψ W cv
    map_add' := fun P Q => Point.vcInvFun_add cv (W⁄K) P Q }

theorem ψE_apply (P : (W⁄K).Point) : ψE W cv P = ψ W cv P := rfl

omit [DecidableEq K] in
@[scoped simp] theorem ψ_zero : ψ W cv 0 = 0 := rfl

omit [DecidableEq K] in
theorem ψ_some {x y : K} (h : (W⁄K).Nonsingular x y) :
    ∃ h' : ((cv • W)⁄K).Nonsingular (vcXInv cv x) (vcYInv cv x y),
      ψ W cv (Point.some x y h) = (Point.some (vcXInv cv x) (vcYInv cv x y) h' : ((cv • W)⁄K).Point) :=
  ⟨(nonsingular_variableChange_iff (vcXInv cv x) (vcYInv cv x y)).mpr (by rwa [vcX_vcXInv, vcY_vcYInv]), rfl⟩

theorem ψ_add (P Q : (W⁄K).Point) : ψ W cv (P + Q) = ψ W cv P + ψ W cv Q := (ψE W cv).map_add P Q

theorem ψ_zsmul (n : ℤ) (P : (W⁄K).Point) : ψ W cv (n • P) = n • ψ W cv P := map_zsmul (ψE W cv) n P

theorem ψ_injective : Function.Injective (ψ W cv) := (ψE W cv).injective

theorem ψ_bijective : Function.Bijective (ψ W cv) := (ψE W cv).bijective

theorem ψ_ne_zero {P : (W⁄K).Point} (hP : P ≠ 0) : ψ W cv P ≠ 0 := by
  intro h
  exact hP ((ψE W cv).injective (by rw [ψE_apply, h, ψE_apply, ψ_zero]))

theorem ψ_eq_zero_iff {P : (W⁄K).Point} : ψ W cv P = 0 ↔ P = 0 :=
  ⟨fun h => by_contra fun hP => ψ_ne_zero W cv hP h, fun h => by rw [h, ψ_zero]⟩

omit [DecidableEq K] in
theorem mk_C_C (V : WeierstrassCurve K) (c : K) :
    CoordinateRing.mk (V⁄K) (Polynomial.C (Polynomial.C c)) = algebraMap K (V⁄K).CoordinateRing c := rfl

omit [DecidableEq K] in
theorem coordIso_XClass (x : K) :
    coordIso W cv (CoordinateRing.XClass ((cv • W)⁄K) (vcXInv cv x)) =
      algebraMap K _ (ui cv) ^ 2 * CoordinateRing.XClass (W⁄K) x := by
  simp only [coordIso_apply, CoordinateRing.XClass, map_sub, coordHom_X, mk_C_C, AlgHom.commutes, xImg, vcXInv, ui,
    map_mul, map_pow]
  ring

omit [DecidableEq K] in
theorem coordIso_YClass (x y : K) :
    coordIso W cv (CoordinateRing.YClass ((cv • W)⁄K) (Polynomial.C (vcYInv cv x y))) =
      algebraMap K _ (ui cv) ^ 3 * (CoordinateRing.YClass (W⁄K) (Polynomial.C y) -
        algebraMap K _ cv.s * CoordinateRing.XClass (W⁄K) x) := by
  simp only [coordIso_apply, CoordinateRing.YClass, CoordinateRing.XClass, map_sub, coordHom_Y, mk_C_C,
    AlgHom.commutes, yImg, vcYInv, ui, map_mul, map_pow]
  ring

omit [DecidableEq K] in
theorem map_XYIdeal (x y : K) :
    (CoordinateRing.XYIdeal ((cv • W)⁄K) (vcXInv cv x) (Polynomial.C (vcYInv cv x y))).map (coordIso W cv) =
      CoordinateRing.XYIdeal (W⁄K) x (Polynomial.C y) := by
  have hu : algebraMap K (W⁄K).CoordinateRing (ui cv) * algebraMap K _ (cv.u : K) = 1 := by
    rw [← map_mul, ui_mul_u, map_one]
  rw [CoordinateRing.XYIdeal, CoordinateRing.XYIdeal, Ideal.map_span, Set.image_pair, coordIso_XClass, coordIso_YClass]
  set α := algebraMap K (W⁄K).CoordinateRing (ui cv) with hα
  set β := algebraMap K (W⁄K).CoordinateRing (cv.u : K) with hβ
  set σ := algebraMap K (W⁄K).CoordinateRing cv.s with hσ
  set Xc := CoordinateRing.XClass (W⁄K) x with hXc
  set Yc := CoordinateRing.YClass (W⁄K) (Polynomial.C y) with hYc
  apply le_antisymm
  · rw [Ideal.span_le]
    rintro z (rfl | rfl)
    · exact Ideal.mem_span_pair.mpr ⟨α ^ 2, 0, by ring⟩
    · exact Ideal.mem_span_pair.mpr ⟨-(α ^ 3 * σ), α ^ 3, by ring⟩
  · rw [Ideal.span_le]
    rintro z (rfl | rfl)
    · exact Ideal.mem_span_pair.mpr ⟨β ^ 2, 0, by linear_combination (α * β + 1) * Xc * hu⟩
    · exact Ideal.mem_span_pair.mpr ⟨β ^ 2 * σ, β ^ 3, by
        linear_combination ((α * β + 1) * σ * Xc + (α ^ 2 * β ^ 2 + α * β + 1) * (Yc - σ * Xc)) * hu⟩

theorem map_placeIdeal (P : (W⁄K).Point) :
    (placeIdeal (cv • W) K (ψ W cv P)).map (coordIso W cv) = placeIdeal W K P := by
  rcases P with _ | ⟨x, y, h⟩
  · rw [← Point.zero_def, ψ_zero, placeIdeal_zero, placeIdeal_zero, Ideal.map_top]
  · obtain ⟨h', hh⟩ := ψ_some W cv h
    rw [placeIdeal_of_ne_zero (cv • W) K (ψ_ne_zero W cv (Point.some_ne_zero h)),
      placeIdeal_of_ne_zero W K (Point.some_ne_zero h), placeOf_asIdeal, placeOf_asIdeal, hh]
    exact map_XYIdeal W cv x y

theorem fibSet_ψ (n : ℤ) (T : (W⁄K).Point) : fibSet (cv • W) K n (ψ W cv T) = ψ W cv '' fibSet W K n T := by
  ext P'
  simp only [mem_fibSet, Set.mem_image]
  constructor
  · intro h
    obtain ⟨P, rfl⟩ := (ψ_bijective W cv).2 P'
    refine ⟨P, ?_, rfl⟩
    rw [← ψ_zsmul] at h
    exact ψ_injective W cv h
  · rintro ⟨P, hP, rfl⟩
    rw [← ψ_zsmul, hP]

theorem map_fibIdeal (n : ℤ) (T : (W⁄K).Point) :
    (fibIdeal (cv • W) K n (ψ W cv T)).map (coordIso W cv) = fibIdeal W K n T := by
  classical
  by_cases hfin : (fibSet W K n T).Finite
  · have hfin' : (fibSet (cv • W) K n (ψ W cv T)).Finite := by
      rw [fibSet_ψ]; exact hfin.image _
    rw [fibIdeal_eq (cv • W) K hfin', fibIdeal_eq W K hfin]
    have key : ∀ (s : Set ((cv • W)⁄K).Point) (hs : s.Finite), s = ψ W cv '' fibSet W K n T →
        (∏ P' ∈ hs.toFinset, placeIdeal (cv • W) K P').map (coordIso W cv) = ∏ P ∈ hfin.toFinset, placeIdeal W K P := by
      rintro s hs rfl
      rw [Set.Finite.toFinset_image (ψ W cv) hfin hs, Finset.prod_image (fun a _ b _ hab => ψ_injective W cv hab)]
      rw [← Ideal.mapHom_apply, map_prod]
      refine Finset.prod_congr rfl fun P _ => ?_
      rw [Ideal.mapHom_apply]
      exact map_placeIdeal W cv P
    exact key _ hfin' (fibSet_ψ W cv n T)
  · have hfin' : ¬ (fibSet (cv • W) K n (ψ W cv T)).Finite := by
      rw [fibSet_ψ]
      intro h
      exact hfin (Set.Finite.of_finite_image h (ψ_injective W cv).injOn)
    rw [fibIdeal, dif_neg hfin', fibIdeal, dif_neg hfin, Ideal.map_top]

omit [DecidableEq K] in
theorem isPrincipal_map_iff (I : Ideal ((cv • W)⁄K).CoordinateRing) :
    (I.map (coordIso W cv)).IsPrincipal ↔ I.IsPrincipal := by
  have hsurj : Function.Surjective (coordIso W cv) := (coordIso W cv).surjective
  constructor
  · rintro ⟨g, hg⟩
    have hgmem : g ∈ I.map (coordIso W cv) := by rw [hg]; exact Submodule.mem_span_singleton_self g
    obtain ⟨y, hyI, hy⟩ := (Ideal.mem_map_iff_of_surjective (coordIso W cv) hsurj).mp hgmem
    refine ⟨⟨y, le_antisymm ?_ ?_⟩⟩
    · intro x hx
      have hex : coordIso W cv x ∈ I.map (coordIso W cv) := Ideal.mem_map_of_mem _ hx
      rw [hg, Ideal.submodule_span_eq, Ideal.mem_span_singleton'] at hex
      obtain ⟨a, ha⟩ := hex
      rw [Ideal.submodule_span_eq, Ideal.mem_span_singleton']
      refine ⟨(coordIso W cv).symm a, (coordIso W cv).injective ?_⟩
      rw [map_mul, AlgEquiv.apply_symm_apply, hy, ha]
    · rw [Ideal.submodule_span_eq, Ideal.span_singleton_le_iff_mem]
      exact hyI
  · rintro ⟨g, hg⟩
    rw [hg, Ideal.submodule_span_eq, Ideal.map_span, Set.image_singleton]
    exact ⟨⟨_, (Ideal.submodule_span_eq).symm⟩⟩

theorem exists_coordIso_weilNum (n : ℤ) (T : (W⁄K).Point) :
    ∃ c : K, c ≠ 0 ∧ coordIso W cv (weilNum (cv • W) K n (ψ W cv T)) = algebraMap K _ c * weilNum W K n T := by
  have hI := map_fibIdeal W cv n T
  by_cases hp : (fibIdeal (cv • W) K n (ψ W cv T)).IsPrincipal
  · have hp' : (fibIdeal W K n T).IsPrincipal := by rw [← hI]; exact (isPrincipal_map_iff W cv _).mpr hp
    have hgen : Ideal.span {coordIso W cv (weilNum (cv • W) K n (ψ W cv T))} = Ideal.span {weilNum W K n T} := by
      rw [span_weilNum W K hp', ← hI, ← span_weilNum (cv • W) K hp, Ideal.map_span, Set.image_singleton]
    rw [Ideal.span_singleton_eq_span_singleton] at hgen
    obtain ⟨w, hw⟩ := hgen
    obtain ⟨c, hc, hcw⟩ := (CoordinateRing.isUnit_iff_eq_algebraMap (W := W.baseChange K)
      ((w⁻¹ : (W⁄K).CoordinateRingˣ) : (W⁄K).CoordinateRing)).mp (Units.isUnit _)
    refine ⟨c, hc, ?_⟩
    rw [← hcw, ← hw, mul_comm _ (w : (W⁄K).CoordinateRing), ← mul_assoc, Units.inv_mul, one_mul]
  · have hp' : ¬ (fibIdeal W K n T).IsPrincipal := by rw [← hI]; exact fun h => hp ((isPrincipal_map_iff W cv _).mp h)
    refine ⟨1, one_ne_zero, ?_⟩
    rw [weilNum, dif_neg hp, weilNum, dif_neg hp', map_one, map_one, one_mul]

omit [DecidableEq K] in
theorem coordIso_comp_injective :
    Function.Injective ((IsScalarTower.toAlgHom K (W⁄K).CoordinateRing (W⁄K).FunctionField).comp
      (coordIso W cv).toAlgHom) := by
  intro a b h
  exact (coordIso W cv).injective (IsFractionRing.injective (W⁄K).CoordinateRing (W⁄K).FunctionField h)

def ffHom : ((cv • W)⁄K).FunctionField →ₐ[K] (W⁄K).FunctionField :=
  IsFractionRing.liftAlgHom (coordIso_comp_injective W cv)

omit [DecidableEq K] in
theorem ffHom_algebraMap (a : ((cv • W)⁄K).CoordinateRing) :
    ffHom W cv (algebraMap _ ((cv • W)⁄K).FunctionField a) = algebraMap _ (W⁄K).FunctionField (coordIso W cv a) := by
  rw [ffHom, IsFractionRing.liftAlgHom_apply, IsFractionRing.lift_algebraMap]
  rfl

omit [DecidableEq K] in
theorem ffHom_injective : Function.Injective (ffHom W cv) := (ffHom W cv).toRingHom.injective

theorem exists_ffHom_weilFun (n : ℤ) (T : (W⁄K).Point) :
    ∃ κ : K, κ ≠ 0 ∧ ffHom W cv (weilFun (cv • W) K n (ψ W cv T)) =
      algebraMap K (W⁄K).FunctionField κ * weilFun W K n T := by
  obtain ⟨c, hc, hcT⟩ := exists_coordIso_weilNum W cv n T
  obtain ⟨c₀, hc₀, hc₀T⟩ := exists_coordIso_weilNum W cv n 0
  rw [ψ_zero] at hc₀T
  refine ⟨c / c₀, div_ne_zero hc hc₀, ?_⟩
  rw [weilFun, weilFun, map_div₀, ffHom_algebraMap, ffHom_algebraMap, hcT, hc₀T, map_mul, map_mul,
    ← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply, map_div₀, mul_div_mul_comm]

end Transport

section Cast

variable {L : Type*} [Field L] [DecidableEq L]

def castPt {V₁ V₂ : Affine L} (e : V₁ = V₂) (P : V₁.Point) : V₂.Point := e ▸ P

omit [DecidableEq L] in
theorem castPt_zero {V₁ V₂ : Affine L} (e : V₁ = V₂) : castPt e (0 : V₁.Point) = 0 := by subst e; rfl

omit [DecidableEq L] in
theorem castPt_some {V₁ V₂ : Affine L} (e : V₁ = V₂) (x y : L) (h : V₁.Nonsingular x y) :
    castPt e (Point.some x y h) = Point.some x y (e ▸ h) := by subst e; rfl

theorem castPt_add {V₁ V₂ : Affine L} (e : V₁ = V₂) (P Q : V₁.Point) :
    castPt e (P + Q) = castPt e P + castPt e Q := by subst e; rfl

omit [DecidableEq L] in
theorem some_ext {V : Affine L} {x₁ y₁ x₂ y₂ : L} (hx : x₁ = x₂) (hy : y₁ = y₂)
    {h₁ : V.Nonsingular x₁ y₁} {h₂ : V.Nonsingular x₂ y₂} : Point.some x₁ y₁ h₁ = Point.some x₂ y₂ h₂ := by
  subst hx hy; rfl

end Cast

section Translation

variable {K : Type u} [Field K] [DecidableEq K] (W : WeierstrassCurve K) (cv : VariableChange K)

def cvL : VariableChange (W⁄K).FunctionField := cv.map (algebraMap K (W⁄K).FunctionField)

omit [DecidableEq K] in
theorem cvL_smul : cvL W cv • (W⁄(W⁄K).FunctionField) = ((cv • W)⁄(W⁄K).FunctionField) := by
  show cv.map _ • W.map _ = (cv • W).map _
  rw [map_variableChange]

omit [DecidableEq K] in
theorem cvL_uinv : (((cvL W cv).u⁻¹ : ((W⁄K).FunctionField)ˣ) : (W⁄K).FunctionField) =
    algebraMap K (W⁄K).FunctionField (ui cv) := by
  show (((Units.map (algebraMap K (W⁄K).FunctionField : K →* (W⁄K).FunctionField) cv.u)⁻¹ :
    ((W⁄K).FunctionField)ˣ) : (W⁄K).FunctionField) = _
  rw [Units.coe_map_inv]; rfl

omit [DecidableEq K] in
theorem vcXInv_cvL (x : (W⁄K).FunctionField) :
    vcXInv (cvL W cv) x = algebraMap K _ (ui cv) ^ 2 * (x - algebraMap K _ cv.r) := by
  rw [vcXInv, cvL_uinv]; rfl

omit [DecidableEq K] in
theorem vcYInv_cvL (x y : (W⁄K).FunctionField) :
    vcYInv (cvL W cv) x y =
      algebraMap K _ (ui cv) ^ 3 * (y - algebraMap K _ cv.t - algebraMap K _ cv.s * (x - algebraMap K _ cv.r)) := by
  rw [vcYInv, cvL_uinv]; rfl

def Θ : (W⁄(W⁄K).FunctionField).Point → ((cv • W)⁄(W⁄K).FunctionField).Point :=
  fun P => castPt (cvL_smul W cv) (Point.vcInvFun (cvL W cv) (W⁄(W⁄K).FunctionField) P)

omit [DecidableEq K] in
theorem Θ_zero : Θ W cv 0 = 0 := castPt_zero _

omit [DecidableEq K] in
theorem Θ_add (P Q : (W⁄(W⁄K).FunctionField).Point) : Θ W cv (P + Q) = Θ W cv P + Θ W cv Q := by
  show castPt _ (Point.vcInvFun (cvL W cv) (W⁄(W⁄K).FunctionField) (P + Q)) = _
  rw [Point.vcInvFun_add, castPt_add]
  rfl

omit [DecidableEq K] in
theorem Θ_some {x y : (W⁄K).FunctionField} (h : (W⁄(W⁄K).FunctionField).Nonsingular x y) :
    ∃ h', Θ W cv (Point.some x y h) =
      Point.some (algebraMap K _ (ui cv) ^ 2 * (x - algebraMap K _ cv.r))
        (algebraMap K _ (ui cv) ^ 3 * (y - algebraMap K _ cv.t - algebraMap K _ cv.s * (x - algebraMap K _ cv.r))) h' := by
  refine ⟨?_, ?_⟩
  · rw [← vcXInv_cvL, ← vcYInv_cvL, ← cvL_smul]
    exact (nonsingular_variableChange_iff (vcXInv (cvL W cv) x) (vcYInv (cvL W cv) x y)).mpr
      (by rwa [vcX_vcXInv, vcY_vcYInv])
  · show castPt _ (Point.some (vcXInv (cvL W cv) x) (vcYInv (cvL W cv) x y) _) = _
    rw [castPt_some]
    exact some_ext (vcXInv_cvL W cv x) (vcYInv_cvL W cv x y)

omit [DecidableEq K] in
theorem Θ_xc {P : (W⁄(W⁄K).FunctionField).Point} (hP : P ≠ 0) :
    (Θ W cv P).xc = algebraMap K _ (ui cv) ^ 2 * (P.xc - algebraMap K _ cv.r) := by
  conv_lhs => rw [Point.eq_some_xc_yc hP]
  obtain ⟨h', hh⟩ := Θ_some W cv (Point.nonsingular_xc_yc hP)
  rw [hh, Point.xc_some]

omit [DecidableEq K] in
theorem Θ_yc {P : (W⁄(W⁄K).FunctionField).Point} (hP : P ≠ 0) :
    (Θ W cv P).yc =
      algebraMap K _ (ui cv) ^ 3 * (P.yc - algebraMap K _ cv.t - algebraMap K _ cv.s * (P.xc - algebraMap K _ cv.r)) := by
  conv_lhs => rw [Point.eq_some_xc_yc hP]
  obtain ⟨h', hh⟩ := Θ_some W cv (Point.nonsingular_xc_yc hP)
  rw [hh, Point.yc_some]

omit [DecidableEq K] in
theorem algebraMap_xImg :
    algebraMap _ (W⁄K).FunctionField (xImg W cv) =
      algebraMap K _ (ui cv) ^ 2 * (genericX W K - algebraMap K _ cv.r) := by
  simp only [xImg, map_mul, map_pow, map_sub, genericX]
  repeat rw [← IsScalarTower.algebraMap_apply]

omit [DecidableEq K] in
theorem algebraMap_yImg :
    algebraMap _ (W⁄K).FunctionField (yImg W cv) =
      algebraMap K _ (ui cv) ^ 3 * (genericY W K - algebraMap K _ cv.s * (genericX W K - algebraMap K _ cv.r) -
        algebraMap K _ cv.t) := by
  simp only [yImg, map_mul, map_pow, map_sub, genericX, genericY]
  repeat rw [← IsScalarTower.algebraMap_apply]

variable [W.IsElliptic] [(cv • W).IsElliptic]

omit [DecidableEq K] in

theorem map_ffHom_genericPoint : Point.map (ffHom W cv) (genericPoint (cv • W) K) = Θ W cv (genericPoint W K) := by
  obtain ⟨h', hh⟩ := Θ_some W cv (generic_nonsingular W K)
  show Point.map (ffHom W cv) (Point.some _ _ (generic_nonsingular (cv • W) K)) =
    Θ W cv (Point.some _ _ (generic_nonsingular W K))
  rw [Point.map_some, hh]
  refine some_ext ?_ ?_
  · show ffHom W cv (algebraMap _ _ (CoordinateRing.mk ((cv • W)⁄K) (Polynomial.C X))) = _
    rw [ffHom_algebraMap, coordIso_apply, coordHom_X, algebraMap_xImg, genericX]
  · show ffHom W cv (algebraMap _ _ (CoordinateRing.mk ((cv • W)⁄K) Y)) = _
    rw [ffHom_algebraMap, coordIso_apply, coordHom_Y, algebraMap_yImg, genericX, genericY]
    ring

omit [W.IsElliptic] [(cv • W).IsElliptic] in

theorem baseChange_ψ (S : (W⁄K).Point) :
    Point.baseChange K (W⁄K).FunctionField (ψ W cv S) = Θ W cv (Point.baseChange K (W⁄K).FunctionField S) := by
  rcases S with _ | ⟨x, y, h⟩
  · rw [← Point.zero_def, ψ_zero, map_zero, map_zero, Θ_zero]
  · obtain ⟨h₀, hh₀⟩ := ψ_some W cv h
    rw [hh₀, Point.baseChange, Point.map_some, Point.map_some]
    have hK : (W⁄(W⁄K).FunctionField).Nonsingular (Algebra.ofId K (W⁄K).FunctionField x)
        (Algebra.ofId K (W⁄K).FunctionField y) :=
      (baseChange_nonsingular (W := W) (A := K) (B := (W⁄K).FunctionField)
        (f := Algebra.ofId K (W⁄K).FunctionField) (RingHom.injective _) x y).mpr h
    obtain ⟨h', hh⟩ := Θ_some W cv hK
    rw [hh]
    refine some_ext ?_ ?_
    · show algebraMap K (W⁄K).FunctionField (vcXInv cv x) = _
      simp only [vcXInv, ui, map_mul, map_pow, map_sub]
      rfl
    · show algebraMap K (W⁄K).FunctionField (vcYInv cv x y) = _
      simp only [vcYInv, ui, map_mul, map_pow, map_sub]
      rfl

variable [IsAlgClosed K]

theorem ffHom_transEquiv (S : (W⁄K).Point) (f : ((cv • W)⁄K).FunctionField) :
    ffHom W cv (transEquiv (cv • W) K (ψ W cv S) f) = transEquiv W K S (ffHom W cv f) := by
  have hne := genericPoint_add_baseChange_ne_zero W K S
  set G₁ : ((cv • W)⁄K).CoordinateRing →ₐ[K] (W⁄K).FunctionField :=
    (ffHom W cv).comp (((transEquiv (cv • W) K (ψ W cv S) : _ ≃ₐ[K] _) : _ →ₐ[K] _).comp
      (IsScalarTower.toAlgHom K ((cv • W)⁄K).CoordinateRing ((cv • W)⁄K).FunctionField)) with hG₁
  set G₂ : ((cv • W)⁄K).CoordinateRing →ₐ[K] (W⁄K).FunctionField :=
    (((transEquiv W K S : _ ≃ₐ[K] _) : _ →ₐ[K] _).comp (ffHom W cv)).comp
      (IsScalarTower.toAlgHom K ((cv • W)⁄K).CoordinateRing ((cv • W)⁄K).FunctionField) with hG₂
  have hpt : Point.map (ffHom W cv) (genericPoint (cv • W) K + Point.baseChange K _ (ψ W cv S)) =
      Θ W cv (genericPoint W K + Point.baseChange K _ S) := by
    rw [map_add, map_ffHom_genericPoint, Point.map_baseChange, baseChange_ψ, Θ_add]
  have hG : G₁ = G₂ := by
    apply CoordinateRing.algHom_ext'
    · simp only [hG₁, hG₂, AlgHom.comp_apply, IsScalarTower.coe_toAlgHom', AlgEquiv.coe_algHom]
      rw [transEquiv_algebraMap, pointHom_mk_C_X, ← Point.xc_map (W := cv • W) (ffHom W cv), hpt, Θ_xc W cv hne,
        ffHom_algebraMap, coordIso_apply, coordHom_X, algebraMap_xImg]
      simp only [map_mul, map_pow, map_sub, AlgEquiv.commutes, transEquiv_genericX]
    · simp only [hG₁, hG₂, AlgHom.comp_apply, IsScalarTower.coe_toAlgHom', AlgEquiv.coe_algHom]
      rw [transEquiv_algebraMap, pointHom_mk_Y, ← Point.yc_map (W := cv • W) (ffHom W cv), hpt, Θ_yc W cv hne,
        ffHom_algebraMap, coordIso_apply, coordHom_Y, algebraMap_yImg]
      simp only [map_mul, map_pow, map_sub, AlgEquiv.commutes, transEquiv_genericX, transEquiv_genericY]
      ring
  have hR : (ffHom W cv).toRingHom.comp (transEquiv (cv • W) K (ψ W cv S)).toAlgHom.toRingHom =
      (transEquiv W K S).toAlgHom.toRingHom.comp (ffHom W cv).toRingHom := by
    apply IsLocalization.ringHom_ext (nonZeroDivisors ((cv • W)⁄K).CoordinateRing)
    exact RingHom.ext fun a => AlgHom.congr_fun hG a
  exact RingHom.congr_fun hR f

end Translation

section PairingTransport

theorem dite_choose_congr {α : Type*} {p q : α → Prop} (hpq : ∀ a, p a ↔ q a)
    {dp : Decidable (∃ a, p a)} {dq : Decidable (∃ a, q a)} (d : α) :
    (@dite α (∃ a, p a) dp (fun h => h.choose) (fun _ => d)) = @dite α (∃ a, q a) dq (fun h => h.choose) (fun _ => d) := by
  obtain rfl : p = q := funext fun a => propext (hpq a)
  obtain rfl : dp = dq := Subsingleton.elim _ _
  rfl

variable {K : Type u} [Field K] [DecidableEq K] [IsAlgClosed K] (W : WeierstrassCurve K) [W.IsElliptic]
  (cv : VariableChange K) [(cv • W).IsElliptic]

theorem weilPairing0_ψ (n : ℤ) (S T : (W⁄K).Point) :
    weilPairing0 (cv • W) K n (ψ W cv S) (ψ W cv T) = weilPairing0 W K n S T := by
  obtain ⟨κ, hκ, hg⟩ := exists_ffHom_weilFun W cv n T
  have hκ' : algebraMap K (W⁄K).FunctionField κ ≠ 0 := (_root_.map_ne_zero _).mpr hκ
  have key : ∀ c : Kˣ,
      transEquiv (cv • W) K (ψ W cv S) (weilFun (cv • W) K n (ψ W cv T)) =
          algebraMap K _ (c : K) * weilFun (cv • W) K n (ψ W cv T) ↔
        transEquiv W K S (weilFun W K n T) = algebraMap K _ (c : K) * weilFun W K n T := by
    intro c
    constructor
    · intro h
      have h1 := congrArg (ffHom W cv) h
      simp only [ffHom_transEquiv, map_mul, AlgHom.commutes, AlgEquiv.commutes, hg] at h1
      rw [mul_left_comm] at h1
      exact mul_left_cancel₀ hκ' h1
    · intro h
      apply ffHom_injective W cv
      simp only [ffHom_transEquiv, map_mul, AlgHom.commutes, AlgEquiv.commutes, hg, h]
      ring
  unfold weilPairing0
  exact dite_choose_congr key 1

end PairingTransport

end WeilIsoInvSol
p2m_reactivate "P2MW.S_WeierstrassCurve_Affine_weilPairing0_toPoint_variableChange.WeilIsoInvSol"

end
p2m_reactivate "P2MW.S_WeierstrassCurve_Affine_weilPairing0_toPoint_variableChange.WeilIsoInvSol"

open WeilIsoInvSol ModularCurve ModularCurve.LevelRelabelling WeierstrassCurve.Affine

theorem solution
    {K : Type u} [Field K] [IsAlgClosed K] [DecidableEq K]
    (W : WeierstrassCurve K) [W.IsElliptic] (C : WeierstrassCurve.VariableChange K) [(C • W).IsElliptic]
    (ℓ : ℕ) [Fact ℓ.Prime] (hℓ3 : 3 ≤ ℓ) (hℓK : (ℓ : K) ≠ 0)
    (D : ModularCurve.LevelPData K) (hD : ModularCurve.IsLevelPStructure W ℓ D) :
    weilPairing0 (C • W) K (ℓ : ℤ)
        (toPoint ((C • W).baseChange K) (D.variableChange C).xP (D.variableChange C).yP)
        (toPoint ((C • W).baseChange K) (D.variableChange C).xQ (D.variableChange C).yQ) =
      weilPairing0 W K (ℓ : ℤ) (toPoint (W.baseChange K) D.xP D.yP) (toPoint (W.baseChange K) D.xQ D.yQ) := by

  have nP : (W⁄K).Nonsingular D.xP D.yP := (equation_iff_nonsingular (W := W.toAffine)).mp hD.equation_P
  have nQ : (W⁄K).Nonsingular D.xQ D.yQ := (equation_iff_nonsingular (W := W.toAffine)).mp hD.equation_Q
  have htP : toPoint (W.baseChange K) D.xP D.yP = Point.some D.xP D.yP nP := by
    unfold toPoint; rw [dif_pos nP]
  have htQ : toPoint (W.baseChange K) D.xQ D.yQ = Point.some D.xQ D.yQ nQ := by
    unfold toPoint; rw [dif_pos nQ]

  obtain ⟨nP', hψP⟩ := ψ_some W C nP
  obtain ⟨nQ', hψQ⟩ := ψ_some W C nQ
  have hyP : (D.variableChange C).yP = vcYInv C D.xP D.yP := by
    rw [LevelPData.variableChange_yP, vcYInv]; ring
  have hyQ : (D.variableChange C).yQ = vcYInv C D.xQ D.yQ := by
    rw [LevelPData.variableChange_yQ, vcYInv]; ring
  have hxP : (D.variableChange C).xP = vcXInv C D.xP := rfl
  have hxQ : (D.variableChange C).xQ = vcXInv C D.xQ := rfl
  have nP'' : ((C • W)⁄K).Nonsingular (D.variableChange C).xP (D.variableChange C).yP := by
    rw [hyP]; exact nP'
  have nQ'' : ((C • W)⁄K).Nonsingular (D.variableChange C).xQ (D.variableChange C).yQ := by
    rw [hyQ]; exact nQ'
  have htP' : toPoint ((C • W).baseChange K) (D.variableChange C).xP (D.variableChange C).yP =
      ψ W C (Point.some D.xP D.yP nP) := by
    rw [hψP]
    show toPoint ((C • W).baseChange K) _ _ = (Point.some (D.variableChange C).xP (vcYInv C D.xP D.yP) (hyP ▸ nP'') :
      ((C • W)⁄K).Point)
    unfold toPoint; rw [dif_pos nP'']
    exact WeilIsoInvSol.some_ext rfl hyP
  have htQ' : toPoint ((C • W).baseChange K) (D.variableChange C).xQ (D.variableChange C).yQ =
      ψ W C (Point.some D.xQ D.yQ nQ) := by
    rw [hψQ]
    show toPoint ((C • W).baseChange K) _ _ = (Point.some (D.variableChange C).xQ (vcYInv C D.xQ D.yQ) (hyQ ▸ nQ'') :
      ((C • W)⁄K).Point)
    unfold toPoint; rw [dif_pos nQ'']
    exact WeilIsoInvSol.some_ext rfl hyQ
  rw [htP, htQ, htP', htQ']
  exact weilPairing0_ψ W C (ℓ : ℤ) _ _

end S_WeierstrassCurve_Affine_weilPairing0_toPoint_variableChange
end P2MW
export P2MW.S_WeierstrassCurve_Affine_weilPairing0_toPoint_variableChange (solution)
