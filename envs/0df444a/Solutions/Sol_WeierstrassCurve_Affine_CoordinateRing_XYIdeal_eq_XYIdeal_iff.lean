-- Prove2me | solution 1 for WeierstrassCurve.Affine.CoordinateRing.XYIdeal_eq_XYIdeal_iff
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.503601+00:00
-- url     : https://prove2.me/submissions/167f3628-0cf7-58a1-9a98-1ac1c13d4c8a

import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_WeierstrassCurve_Affine_CoordinateRing_XYIdeal_eq_XYIdeal_iff

p2m_open "Polynomial WeierstrassCurve P2MW.S_WeierstrassCurve_Affine_CoordinateRing_XYIdeal_eq_XYIdeal_iff.WeierstrassCurve WeierstrassCurve.Affine P2MW.S_WeierstrassCurve_Affine_CoordinateRing_XYIdeal_eq_XYIdeal_iff.WeierstrassCurve.Affine WeierstrassCurve.Affine.CoordinateRing P2MW.S_WeierstrassCurve_Affine_CoordinateRing_XYIdeal_eq_XYIdeal_iff.WeierstrassCurve.Affine.CoordinateRing"
open scoped Polynomial.Bivariate

namespace WeierstrassCurve
p2m_export "WeierstrassCurve" "Affine map Affine.CoordinateRing mk Affine.Point"
namespace Affine
p2m_export "WeierstrassCurve.Affine" "Equation CoordinateRing map Point polynomial"
namespace CoordinateRing
p2m_export "WeierstrassCurve.Affine.CoordinateRing" "XYIdeal YClass mk map XClass"
namespace DetInfra
p2m_open "WeierstrassCurve.Affine.CoordinateRing WeierstrassCurve.Affine WeierstrassCurve"

variable {F : Type*} [Field F] {W : Affine F}

lemma XYIdeal_eq_map (x : F) (y : F[X]) :
    XYIdeal W x y = Ideal.map (mk W) (Ideal.span {C (X - C x), Y - C y}) := by
  simp only [XYIdeal, XClass, YClass, ← Set.image_pair, ← Ideal.map_span]

lemma mk_mem_XYIdeal_of_evalEval_eq_zero (x y : F) {p : F[X][Y]} (hp : p.evalEval x y = 0) :
    mk W p ∈ XYIdeal W x (C y) := by
  rw [XYIdeal_eq_map]
  exact Ideal.mem_map_of_mem _ (mem_span_C_X_sub_C_X_sub_C_iff_eval_eval_eq_zero.mpr hp)

lemma mk_mem_XYIdeal_iff' {x y : F} (h : W.Equation x y) (p : F[X][Y]) :
    mk W p ∈ XYIdeal W x (C y) ↔ p.evalEval x y = 0 := by
  refine ⟨fun hp => ?_, mk_mem_XYIdeal_of_evalEval_eq_zero x y⟩
  rw [XYIdeal_eq_map, Ideal.mem_map_iff_of_surjective _ AdjoinRoot.mk_surjective] at hp
  obtain ⟨q, hq, hqp⟩ := hp
  obtain ⟨r, hr⟩ := AdjoinRoot.mk_eq_mk.mp hqp
  have hW : W.polynomial ∈ Ideal.span {C (X - C x), Y - C (C y)} :=
    mem_span_C_X_sub_C_X_sub_C_iff_eval_eval_eq_zero.mpr h
  have : p = q - W.polynomial * r := by rw [← hr]; ring
  rw [this]
  exact mem_span_C_X_sub_C_X_sub_C_iff_eval_eval_eq_zero.mp
    (Ideal.sub_mem _ hq (Ideal.mul_mem_right _ _ hW))

end WeierstrassCurve.Affine.CoordinateRing.DetInfra

open WeierstrassCurve.Affine.CoordinateRing.DetInfra

theorem solution {F : Type*} [Field F] {W : Affine F} {x₁ y₁ : F} (h : W.Equation x₁ y₁) (x₂ y₂ : F) : XYIdeal W x₁ (C y₁) = XYIdeal W x₂ (C y₂) ↔ x₁ = x₂ ∧ y₁ = y₂ := by
  refine ⟨fun he => ?_, by rintro ⟨rfl, rfl⟩; rfl⟩
  have hx : XClass W x₂ ∈ XYIdeal W x₁ (C y₁) := he ▸ Ideal.subset_span (by simp)
  have hy : YClass W (C y₂) ∈ XYIdeal W x₁ (C y₁) := he ▸ Ideal.subset_span (by simp)
  rw [XClass, mk_mem_XYIdeal_iff' h] at hx
  rw [YClass, mk_mem_XYIdeal_iff' h] at hy
  simp only [evalEval_C, eval_sub, eval_X, eval_C] at hx
  simp only [evalEval_sub, evalEval_X, evalEval_CC] at hy
  exact ⟨sub_eq_zero.mp hx, sub_eq_zero.mp hy⟩

end S_WeierstrassCurve_Affine_CoordinateRing_XYIdeal_eq_XYIdeal_iff
end P2MW
export P2MW.S_WeierstrassCurve_Affine_CoordinateRing_XYIdeal_eq_XYIdeal_iff (solution)
