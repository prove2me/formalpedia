-- Prove2me | solution 1 for WeierstrassCurve.Affine.valuation_transEquiv_le
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.503601+00:00
-- url     : https://prove2.me/submissions/e783caec-da40-5dbd-9034-6f16cd704ad1

import Definitions.Def_EllipticCurve_FunctionFieldPullback
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_WeierstrassCurve_Affine_valuation_transEquiv_le

namespace WeierstrassCurve
p2m_export "WeierstrassCurve" "Affine a₃ a₁ mk a₄ a₂ a₆ baseChange"
namespace Affine
p2m_export "WeierstrassCurve.Affine" "negY slope_of_X_ne CoordinateRing.XClass_ne_zero slope CoordinateRing Point.baseChange baseChange negAddY FunctionField Point CoordinateRing.mk addX CoordinateRing.XClass addY Point.add_of_X_ne Point.map_some Point.xc_some Point.yc_some genericX genericY genericPoint transPull transEquiv transEquiv_apply placeOf valuation_algebraMap_le_one valuation_algebraMap_eq_one cong_genericX cong_genericY valuation_pointPull_le"
p2m_open "WeierstrassCurve.Affine WeierstrassCurve"

open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum WithZero Polynomial

section TransportTau

variable {R : Type*} [Field R] (W : WeierstrassCurve R) (K : Type*) [Field K] [Algebra R K]
  [DecidableEq K] [IsAlgClosed K] [W.IsElliptic] [IsDedekindDomain (W⁄K).CoordinateRing]

omit [DecidableEq K] [IsAlgClosed K] [IsDedekindDomain (W⁄K).CoordinateRing] in

theorem genericX_ne_algebraMap (c : K) : genericX W K ≠ algebraMap K (W⁄K).FunctionField c := by
  intro h
  apply CoordinateRing.XClass_ne_zero (W' := W⁄K) c
  apply IsFractionRing.injective (W⁄K).CoordinateRing (W⁄K).FunctionField
  have e1 : algebraMap (W⁄K).CoordinateRing (W⁄K).FunctionField (CoordinateRing.mk (W⁄K) (C X)) =
      genericX W K := rfl
  have e2 : algebraMap (W⁄K).CoordinateRing (W⁄K).FunctionField (CoordinateRing.mk (W⁄K) (C (C c))) =
      algebraMap K _ c := (IsScalarTower.algebraMap_apply K (W⁄K).CoordinateRing (W⁄K).FunctionField c).symm
  rw [CoordinateRing.XClass, map_sub, map_sub, map_sub, _root_.map_zero, e1, e2, h, sub_self]

omit [DecidableEq K] [IsAlgClosed K] [W.IsElliptic] [IsDedekindDomain (W⁄K).CoordinateRing] in
theorem baseChange_a_eq :
    (W⁄(W⁄K).FunctionField).a₁ = algebraMap K _ (W⁄K).a₁ ∧ (W⁄(W⁄K).FunctionField).a₂ = algebraMap K _ (W⁄K).a₂ ∧
    (W⁄(W⁄K).FunctionField).a₃ = algebraMap K _ (W⁄K).a₃ ∧ (W⁄(W⁄K).FunctionField).a₄ = algebraMap K _ (W⁄K).a₄ ∧
    (W⁄(W⁄K).FunctionField).a₆ = algebraMap K _ (W⁄K).a₆ :=
  ⟨IsScalarTower.algebraMap_apply R K _ W.a₁, IsScalarTower.algebraMap_apply R K _ W.a₂,
    IsScalarTower.algebraMap_apply R K _ W.a₃, IsScalarTower.algebraMap_apply R K _ W.a₄,
    IsScalarTower.algebraMap_apply R K _ W.a₆⟩

variable {W K} in
omit [IsAlgClosed K] [W.IsElliptic] in

theorem cong_addX_addY {P : (W⁄K).Point} (hP : P ≠ 0) {x₁ x₂ y₁ ℓ : (W⁄K).FunctionField}
    {x₁' x₂' y₁' ℓ' : K}
    (h₁ : ((placeOf W K P hP).valuation _).Cong x₁ (algebraMap K _ x₁'))
    (h₂ : ((placeOf W K P hP).valuation _).Cong x₂ (algebraMap K _ x₂'))
    (h₃ : ((placeOf W K P hP).valuation _).Cong y₁ (algebraMap K _ y₁'))
    (h₄ : ((placeOf W K P hP).valuation _).Cong ℓ (algebraMap K _ ℓ')) :
    ((placeOf W K P hP).valuation _).Cong ((W⁄(W⁄K).FunctionField).addX x₁ x₂ ℓ)
        (algebraMap K _ ((W⁄K).addX x₁' x₂' ℓ')) ∧
      ((placeOf W K P hP).valuation _).Cong ((W⁄(W⁄K).FunctionField).addY x₁ x₂ y₁ ℓ)
        (algebraMap K _ ((W⁄K).addY x₁' x₂' y₁' ℓ')) := by
  set v := (placeOf W K P hP).valuation (W⁄K).FunctionField
  have hc := valuation_algebraMap_le_one W K P hP
  obtain ⟨e1, e2, e3, -, -⟩ := baseChange_a_eq W K
  have hX : v.Cong ((W⁄(W⁄K).FunctionField).addX x₁ x₂ ℓ) (algebraMap K _ ((W⁄K).addX x₁' x₂' ℓ')) := by
    simp only [addX, map_sub, map_add, map_mul, map_pow, e1, e2]
    exact ((((h₄.pow (hc _) 2).add ((Valuation.Cong.refl _).mul h₄ (hc _) (hc _))).sub
      (Valuation.Cong.refl _)).sub h₁).sub h₂
  refine ⟨hX, ?_⟩
  simp only [addY, negY, negAddY, map_sub, map_add, map_mul, map_neg, e1, e3]
  have hX' : v.Cong ((W⁄(W⁄K).FunctionField).addX x₁ x₂ ℓ - x₁)
      (algebraMap K _ ((W⁄K).addX x₁' x₂' ℓ') - algebraMap K _ x₁') := hX.sub h₁
  have hN : v.Cong (ℓ * ((W⁄(W⁄K).FunctionField).addX x₁ x₂ ℓ - x₁) + y₁)
      (algebraMap K _ ℓ' * (algebraMap K _ ((W⁄K).addX x₁' x₂' ℓ') - algebraMap K _ x₁') +
        algebraMap K _ y₁') :=
    (h₄.mul hX' (hc _) (by rw [← map_sub]; exact hc _)).add h₃
  exact ((hN.neg).sub ((Valuation.Cong.refl _).mul hX (hc _) (hc _))).sub (Valuation.Cong.refl _)

theorem valuation_transEquiv_le' {P S : (W⁄K).Point} (hP : P ≠ 0) (hS : S ≠ 0) (hx : P.xc ≠ S.xc)
    (hPS : P + S ≠ 0) (h : (W⁄K).FunctionField) (k : ℕ)
    (hh : (placeOf W K (P + S) hPS).valuation (W⁄K).FunctionField h ≤ exp (-(k : ℤ))) :
    (placeOf W K P hP).valuation (W⁄K).FunctionField (transEquiv W K S h) ≤ exp (-(k : ℤ)) := by
  set v := (placeOf W K P hP).valuation (W⁄K).FunctionField with hv
  have hc := valuation_algebraMap_le_one W K P hP

  rcases P with _ | ⟨a, b, hab⟩
  · exact absurd rfl hP
  rcases S with _ | ⟨xS, yS, hSns⟩
  · exact absurd rfl hS
  simp only [Point.xc_some] at hx
  have hγx : genericX W K ≠ algebraMap K (W⁄K).FunctionField xS := genericX_ne_algebraMap W K xS

  have hγx' : genericX W K ≠ Algebra.ofId K (W⁄K).FunctionField xS := hγx
  have hQx : (genericPoint W K + Point.baseChange K (W⁄K).FunctionField (.some xS yS hSns)).xc =
      (W⁄(W⁄K).FunctionField).addX (genericX W K) (algebraMap K (W⁄K).FunctionField xS)
        ((W⁄(W⁄K).FunctionField).slope (genericX W K) (algebraMap K (W⁄K).FunctionField xS) (genericY W K) (algebraMap K (W⁄K).FunctionField yS)) := by
    rw [genericPoint, Point.baseChange, Point.map_some, Point.add_of_X_ne hγx', Point.xc_some]; rfl
  have hQy : (genericPoint W K + Point.baseChange K (W⁄K).FunctionField (.some xS yS hSns)).yc =
      (W⁄(W⁄K).FunctionField).addY (genericX W K) (algebraMap K (W⁄K).FunctionField xS) (genericY W K)
        ((W⁄(W⁄K).FunctionField).slope (genericX W K) (algebraMap K (W⁄K).FunctionField xS) (genericY W K) (algebraMap K (W⁄K).FunctionField yS)) := by
    rw [genericPoint, Point.baseChange, Point.map_some, Point.add_of_X_ne hγx', Point.yc_some]; rfl

  have hX := cong_genericX W K (.some a b hab) hP
  have hY := cong_genericY W K (.some a b hab) hP
  simp only [Point.xc_some, Point.yc_some] at hX hY
  have hslope : v.Cong ((W⁄(W⁄K).FunctionField).slope (genericX W K) (algebraMap K (W⁄K).FunctionField xS) (genericY W K) (algebraMap K (W⁄K).FunctionField yS))
      (algebraMap K (W⁄K).FunctionField ((W⁄K).slope a xS b yS)) := by
    rw [slope_of_X_ne hγx, slope_of_X_ne hx, map_div₀, map_sub, map_sub]
    refine (hY.sub (Valuation.Cong.refl _)).div (hX.sub (Valuation.Cong.refl _))
      (by rw [← map_sub]; exact hc _) ?_
    rw [← map_sub]
    exact valuation_algebraMap_eq_one W K _ hP (sub_ne_zero.mpr hx)
  obtain ⟨hcx, hcy⟩ := cong_addX_addY (P := .some a b hab) hP (x₂' := xS) hX
    (Valuation.Cong.refl (algebraMap K (W⁄K).FunctionField xS)) hY hslope

  rw [transEquiv_apply, transPull]
  refine valuation_pointPull_le W K _ _ _ hP hPS ?_ ?_ h k hh
  · rw [hQx, Point.add_of_X_ne hx, Point.xc_some]
    exact hcx
  · rw [hQy, Point.add_of_X_ne hx, Point.yc_some]
    exact hcy

end TransportTau

end WeierstrassCurve.Affine

open _root_.WeierstrassCurve _root_.P2MW.S_WeierstrassCurve_Affine_valuation_transEquiv_le.WeierstrassCurve _root_.WeierstrassCurve.Affine _root_.P2MW.S_WeierstrassCurve_Affine_valuation_transEquiv_le.WeierstrassCurve.Affine IsDedekindDomain WithZero in
theorem solution {R : Type*} [Field R] (W : WeierstrassCurve R) (K : Type*) [Field K] [Algebra R K] [DecidableEq K] [IsAlgClosed K] [W.IsElliptic] [IsDedekindDomain (W⁄K).CoordinateRing] {P S : (W⁄K).Point} (hP : P ≠ 0) (hS : S ≠ 0) (hx : P.xc ≠ S.xc) (hPS : P + S ≠ 0) (h : (W⁄K).FunctionField) (k : ℕ) (hh : (placeOf W K (P + S) hPS).valuation (W⁄K).FunctionField h ≤ exp (-(k : ℤ))) : (placeOf W K P hP).valuation (W⁄K).FunctionField (transEquiv W K S h) ≤ exp (-(k : ℤ)) :=
  valuation_transEquiv_le' W K hP hS hx hPS h k hh

end S_WeierstrassCurve_Affine_valuation_transEquiv_le
end P2MW
export P2MW.S_WeierstrassCurve_Affine_valuation_transEquiv_le (solution)
