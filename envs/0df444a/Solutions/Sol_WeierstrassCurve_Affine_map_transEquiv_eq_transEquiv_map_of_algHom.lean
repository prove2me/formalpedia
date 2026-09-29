-- Prove2me | solution 1 for WeierstrassCurve.Affine.map_transEquiv_eq_transEquiv_map_of_algHom
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.503601+00:00
-- url     : https://prove2.me/submissions/adec1ffc-7f95-5234-8117-38599f645cab

import Mathlib
import Definitions.Def_EllipticCurve_WeilPairingFun
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_WeierstrassCurve_Affine_map_transEquiv_eq_transEquiv_map_of_algHom

set_option autoImplicit false

p2m_open "WeierstrassCurve P2MW.S_WeierstrassCurve_Affine_map_transEquiv_eq_transEquiv_map_of_algHom.WeierstrassCurve WeierstrassCurve.Affine P2MW.S_WeierstrassCurve_Affine_map_transEquiv_eq_transEquiv_map_of_algHom.WeierstrassCurve.Affine IsDedekindDomain WithZero"
open Polynomial
open scoped Polynomial.Bivariate

namespace WeierstrassCurve
p2m_export "WeierstrassCurve" "Affine map mk Affine.Point Affine.Point.map baseChange"
namespace Affine
p2m_export "WeierstrassCurve.Affine" "CoordinateRing Point.baseChange map baseChange FunctionField Point CoordinateRing.mk Point.map Point.map_some genericX genericY genericPoint pointHom_mk Point.xc_map Point.yc_map transEquiv transEquiv_algebraMap"
namespace TransEquivBaseChangeAux
p2m_open "WeierstrassCurve.Affine WeierstrassCurve"

variable {F K K' : Type*} [Field F] [Field K] [Field K'] [Algebra F K] [Algebra F K']
  (W : WeierstrassCurve F) (f : K →ₐ[F] K')
  (Φ : (W⁄K).FunctionField →+* (W⁄K').FunctionField)
  (hΦ : ∀ p : K[X][Y], Φ (algebraMap (W⁄K).CoordinateRing (W⁄K).FunctionField (CoordinateRing.mk (W⁄K) p)) =
    algebraMap (W⁄K').CoordinateRing (W⁄K').FunctionField (CoordinateRing.mk (W⁄K') (p.map (mapRingHom (f : K →+* K')))))

include hΦ

theorem bc_algebraMap (c : K) :
    Φ (algebraMap K (W⁄K).FunctionField c) = algebraMap K' (W⁄K').FunctionField (f c) := by
  have h := hΦ (C (C c))
  rw [Polynomial.map_C, coe_mapRingHom, Polynomial.map_C, RingHom.coe_coe] at h
  rw [IsScalarTower.algebraMap_apply K (W⁄K).CoordinateRing (W⁄K).FunctionField c,
    IsScalarTower.algebraMap_apply K' (W⁄K').CoordinateRing (W⁄K').FunctionField (f c)]
  exact h

theorem bc_algebraMap_base (c : F) :
    Φ (algebraMap F (W⁄K).FunctionField c) = algebraMap F (W⁄K').FunctionField c := by
  rw [IsScalarTower.algebraMap_apply F K (W⁄K).FunctionField c, bc_algebraMap W f Φ hΦ,
    AlgHom.commutes, IsScalarTower.algebraMap_apply F K' (W⁄K').FunctionField c]

theorem bc_genericX : Φ (genericX W K) = genericX W K' := by
  have h := hΦ (C X)
  rwa [Polynomial.map_C, coe_mapRingHom, Polynomial.map_X] at h

theorem bc_genericY : Φ (genericY W K) = genericY W K' := by
  have h := hΦ Y
  rwa [Polynomial.map_X] at h

noncomputable def bcAlgHom : (W⁄K).FunctionField →ₐ[F] (W⁄K').FunctionField :=
  { Φ with commutes' := bc_algebraMap_base W f Φ hΦ }

@[scoped simp] theorem bcAlgHom_apply (h : (W⁄K).FunctionField) : bcAlgHom W f Φ hΦ h = Φ h := rfl

variable [DecidableEq K] [DecidableEq K']

omit [DecidableEq K] [DecidableEq K'] in

theorem map_bcAlgHom_genericPoint [W.IsElliptic] :
    Point.map (bcAlgHom W f Φ hΦ) (genericPoint W K) = genericPoint W K' := by
  unfold genericPoint
  rw [Point.map_some]
  congr 1
  · exact bc_genericX W f Φ hΦ
  · exact bc_genericY W f Φ hΦ

theorem map_bcAlgHom_baseChange (S : (W⁄K).Point) :
    Point.map (bcAlgHom W f Φ hΦ) (Point.baseChange K (W⁄K).FunctionField S) =
      Point.baseChange K' (W⁄K').FunctionField (Point.map f S) := by
  rcases S with _ | ⟨x, y, hxy⟩
  · rfl
  · simp only [Point.baseChange, Point.map_some]
    congr 1
    · exact bc_algebraMap W f Φ hΦ x
    · exact bc_algebraMap W f Φ hΦ y

theorem main [IsAlgClosed K] [IsAlgClosed K'] [W.IsElliptic] (S : (W⁄K).Point)
    (h : (W⁄K).FunctionField) :
    Φ (transEquiv W K S h) = transEquiv W K' (Point.map f S) (Φ h) := by

  have hQ : Point.map (bcAlgHom W f Φ hΦ)
      (genericPoint W K + Point.baseChange K (W⁄K).FunctionField S) =
      genericPoint W K' + Point.baseChange K' (W⁄K').FunctionField (Point.map f S) := by
    rw [map_add, map_bcAlgHom_genericPoint, map_bcAlgHom_baseChange]
  have hx : Φ (genericPoint W K + Point.baseChange K (W⁄K).FunctionField S).xc =
      (genericPoint W K' + Point.baseChange K' (W⁄K').FunctionField (Point.map f S)).xc := by
    rw [← hQ, Point.xc_map (R := F) (K := F) (W := W)]
    rfl
  have hy : Φ (genericPoint W K + Point.baseChange K (W⁄K).FunctionField S).yc =
      (genericPoint W K' + Point.baseChange K' (W⁄K').FunctionField (Point.map f S)).yc := by
    rw [← hQ, Point.yc_map (R := F) (K := F) (W := W)]
    rfl

  suffices H : Φ.comp (transEquiv W K S : (W⁄K).FunctionField →ₐ[K] (W⁄K).FunctionField).toRingHom =
      (transEquiv W K' (Point.map f S) :
        (W⁄K').FunctionField →ₐ[K'] (W⁄K').FunctionField).toRingHom.comp Φ from
    RingHom.congr_fun H h
  apply IsLocalization.ringHom_ext (nonZeroDivisors (W⁄K).CoordinateRing)
  refine RingHom.ext fun a => ?_
  induction a using AdjoinRoot.induction_on with
  | ih g =>
    change Φ (transEquiv W K S (algebraMap _ (W⁄K).FunctionField (CoordinateRing.mk (W⁄K) g))) =
      transEquiv W K' (Point.map f S)
        (Φ (algebraMap _ (W⁄K).FunctionField (CoordinateRing.mk (W⁄K) g)))
    rw [transEquiv_algebraMap, pointHom_mk, hΦ, transEquiv_algebraMap, pointHom_mk,
      Polynomial.hom_eval₂, Polynomial.eval₂_map, hy]
    congr 1
    apply Polynomial.ringHom_ext
    · intro c
      rw [RingHom.comp_apply, RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
        aeval_C, bc_algebraMap W f Φ hΦ, coe_mapRingHom, Polynomial.map_C, AlgHom.toRingHom_eq_coe,
        RingHom.coe_coe, aeval_C]
      rfl
    · rw [RingHom.comp_apply, RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, aeval_X,
        hx, coe_mapRingHom, Polynomial.map_X, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, aeval_X]

end WeierstrassCurve.Affine.TransEquivBaseChangeAux
p2m_reactivate "P2MW.S_WeierstrassCurve_Affine_map_transEquiv_eq_transEquiv_map_of_algHom.WeierstrassCurve P2MW.S_WeierstrassCurve_Affine_map_transEquiv_eq_transEquiv_map_of_algHom.WeierstrassCurve.Affine P2MW.S_WeierstrassCurve_Affine_map_transEquiv_eq_transEquiv_map_of_algHom.WeierstrassCurve.Affine.TransEquivBaseChangeAux"
p2m_reactivate "P2MW.S_WeierstrassCurve_Affine_map_transEquiv_eq_transEquiv_map_of_algHom.WeierstrassCurve P2MW.S_WeierstrassCurve_Affine_map_transEquiv_eq_transEquiv_map_of_algHom.WeierstrassCurve.Affine"
p2m_reactivate "P2MW.S_WeierstrassCurve_Affine_map_transEquiv_eq_transEquiv_map_of_algHom.WeierstrassCurve"

theorem solution
    {F K K' : Type*} [Field F] [Field K] [Field K'] [Algebra F K] [Algebra F K'] [DecidableEq K] [DecidableEq K']
    [IsAlgClosed K] [IsAlgClosed K'] (W : WeierstrassCurve F) [W.IsElliptic] (f : K →ₐ[F] K')
    (Φ : (W⁄K).FunctionField →+* (W⁄K').FunctionField)
    (hΦ : ∀ p : K[X][Y], Φ (algebraMap (W⁄K).CoordinateRing (W⁄K).FunctionField (CoordinateRing.mk (W⁄K) p)) =
      algebraMap (W⁄K').CoordinateRing (W⁄K').FunctionField (CoordinateRing.mk (W⁄K') (p.map (mapRingHom (f : K →+* K')))))
    (S : (W⁄K).Point) (h : (W⁄K).FunctionField) :
    Φ (transEquiv W K S h) = transEquiv W K' (WeierstrassCurve.Affine.Point.map f S) (Φ h) :=
  WeierstrassCurve.Affine.TransEquivBaseChangeAux.main W f Φ hΦ S h

end S_WeierstrassCurve_Affine_map_transEquiv_eq_transEquiv_map_of_algHom
end P2MW
export P2MW.S_WeierstrassCurve_Affine_map_transEquiv_eq_transEquiv_map_of_algHom (solution)
