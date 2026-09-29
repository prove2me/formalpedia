-- Prove2me | solution 1 for WeierstrassCurve.Affine.exists_map_weilFun_eq_mul_weilFun_map_of_algHom
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.503601+00:00
-- url     : https://prove2.me/submissions/0a67a589-9217-5ab2-af3e-9eead2ee9551

import Mathlib
import Definitions.Def_EllipticCurve_WeilPairingFun
import Theorems.Thm_WeierstrassCurve_Affine_valuation_weilFun
import Theorems.Thm_WeierstrassCurve_card_torsion_of_isAlgClosed
import Theorems.Thm_WeierstrassCurve_Affine_weilFun_ne_zero
import Theorems.Thm_WeierstrassCurve_Affine_FunctionField_exists_eq_algebraMap_of_valuation_eq_one
import Theorems.Thm_WeierstrassCurve_Affine_valuation_placeOf_map_of_algHom
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_WeierstrassCurve_Affine_exists_map_weilFun_eq_mul_weilFun_map_of_algHom
p2m_attr_erase "instance" "WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly"
p2m_attr_erase "simp" "compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two"

set_option autoImplicit false

open WeierstrassCurve WeierstrassCurve.Affine IsDedekindDomain IsDedekindDomain.HeightOneSpectrum WithZero
open Polynomial
open scoped Polynomial.Bivariate

theorem solution
    {F K K' : Type*} [Field F] [Field K] [Field K'] [Algebra F K] [Algebra F K'] [DecidableEq K] [DecidableEq K']
    [IsAlgClosed K] [IsAlgClosed K'] (W : WeierstrassCurve F) [W.IsElliptic]
    [IsDedekindDomain (W⁄K).CoordinateRing] [IsDedekindDomain (W⁄K').CoordinateRing]
    {n : ℕ} (hn : (n : K) ≠ 0) (f : K →ₐ[F] K')
    (Φ : (W⁄K).FunctionField →+* (W⁄K').FunctionField)
    (hΦ : ∀ p : K[X][Y], Φ (algebraMap (W⁄K).CoordinateRing (W⁄K).FunctionField (CoordinateRing.mk (W⁄K) p)) =
      algebraMap (W⁄K').CoordinateRing (W⁄K').FunctionField (CoordinateRing.mk (W⁄K') (p.map (mapRingHom (f : K →+* K')))))
    {T : (W⁄K).Point} (hT : (n : ℤ) • T = 0) :
    ∃ c : K'ˣ, Φ (weilFun W K n T) =
      algebraMap K' (W⁄K').FunctionField (c : K') * weilFun W K' n (WeierstrassCurve.Affine.Point.map f T) := by
  classical
  have hinj : Function.Injective (WeierstrassCurve.Affine.Point.map f : (W⁄K).Point → (W⁄K').Point) :=
    Point.map_injective _
  have hn' : (n : K') ≠ 0 := by
    intro h; apply hn
    have : f (n : K) = (n : K') := map_natCast f n
    rw [← this] at h
    exact (map_eq_zero_iff f f.toRingHom.injective).mp h
  have hfT : (n : ℤ) • (WeierstrassCurve.Affine.Point.map f T) = 0 := by
    rw [← map_zsmul (WeierstrassCurve.Affine.Point.map f) (n : ℤ) T, hT, map_zero]
  have hg0 := WeierstrassCurve.Affine.weilFun_ne_zero W hn hT
  have hg0' := WeierstrassCurve.Affine.weilFun_ne_zero W hn' hfT

  have htors : ∀ (m : ℕ), (m : K) ≠ 0 → ∀ Q : (W⁄K').Point, (m : ℤ) • Q = 0 →
      ∃ P : (W⁄K).Point, WeierstrassCurve.Affine.Point.map f P = Q := by
    intro m hm Q hQ
    have hm' : (m : K') ≠ 0 := by
      intro h; apply hm
      have : f (m : K) = (m : K') := map_natCast f m
      rw [← this] at h
      exact (map_eq_zero_iff f f.toRingHom.injective).mp h
    have hc := WeierstrassCurve.card_torsion_of_isAlgClosed (K := K) W (n := m) hm
    have hc' := WeierstrassCurve.card_torsion_of_isAlgClosed (K := K') W (n := m) hm'
    have hm0 : m ≠ 0 := by rintro rfl; exact hm (by simp)
    haveI : Finite (Submodule.torsionBy ℤ (W⁄K).Point m) := Nat.finite_of_card_ne_zero (by rw [hc]; positivity)
    haveI : Finite (Submodule.torsionBy ℤ (W⁄K').Point m) := Nat.finite_of_card_ne_zero (by rw [hc']; positivity)

    let g : Submodule.torsionBy ℤ (W⁄K).Point m → Submodule.torsionBy ℤ (W⁄K').Point m := fun P =>
      ⟨WeierstrassCurve.Affine.Point.map f P.1, by
        rw [Submodule.mem_torsionBy_iff]
        have hP := (Submodule.mem_torsionBy_iff _ _).mp P.2
        show (m : ℤ) • WeierstrassCurve.Affine.Point.map f P.1 = 0
        rw [← map_zsmul (WeierstrassCurve.Affine.Point.map f), show (m : ℤ) • P.1 = 0 from hP, map_zero]⟩
    have hginj : Function.Injective g := by
      intro a b hab; apply Subtype.ext; exact hinj (congrArg Subtype.val hab)
    haveI := Fintype.ofFinite (Submodule.torsionBy ℤ (W⁄K).Point m)
    haveI := Fintype.ofFinite (Submodule.torsionBy ℤ (W⁄K').Point m)
    have hbij : Function.Bijective g := by
      rw [Fintype.bijective_iff_injective_and_card]
      refine ⟨hginj, ?_⟩
      rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, hc, hc']
    obtain ⟨⟨P, hP⟩, hPQ⟩ := hbij.2 ⟨Q, (Submodule.mem_torsionBy_iff _ _).mpr hQ⟩
    exact ⟨P, congrArg Subtype.val hPQ⟩

  suffices h : ∃ c : K', c ≠ 0 ∧ Φ (weilFun W K n T) / weilFun W K' n (WeierstrassCurve.Affine.Point.map f T) =
      algebraMap K' _ c by
    obtain ⟨c, hc0, hc⟩ := h
    exact ⟨Units.mk0 c hc0, by rw [Units.val_mk0, ← hc, div_mul_cancel₀ _ hg0']⟩
  apply WeierstrassCurve.Affine.FunctionField.exists_eq_algebraMap_of_valuation_eq_one (W := W⁄K')
  intro v
  obtain ⟨Q, hQ, rfl⟩ := placeOf_surjective W K' v
  have hT3 := WeierstrassCurve.Affine.valuation_placeOf_map_of_algHom W f Φ hΦ (weilFun W K n T)
  rw [map_div₀]
  have hne : ∀ c : Prop, ∀ [Decidable c], (if c then (exp (-1 : ℤ) : ℤᵐ⁰) else 1) ≠ 0 := by
    intro c _; split_ifs; exacts [WithZero.coe_ne_zero, one_ne_zero]
  by_cases hIm : ∃ P : (W⁄K).Point, WeierstrassCurve.Affine.Point.map f P = Q
  · obtain ⟨P, rfl⟩ := hIm
    have hP : P ≠ 0 := by rintro rfl; exact hQ (map_zero _)
    rw [hT3.1 P hP hQ, WeierstrassCurve.Affine.valuation_weilFun W hn hT P hP,
      WeierstrassCurve.Affine.valuation_weilFun W hn' hfT _ hQ]
    have e1 : ((n : ℤ) • WeierstrassCurve.Affine.Point.map f P = WeierstrassCurve.Affine.Point.map f T) =
        ((n : ℤ) • P = T) := by
      rw [← map_zsmul (WeierstrassCurve.Affine.Point.map f)]; exact propext hinj.eq_iff
    have e2 : ((n : ℤ) • WeierstrassCurve.Affine.Point.map f P = 0) = ((n : ℤ) • P = 0) := by
      rw [← map_zsmul (WeierstrassCurve.Affine.Point.map f), ← map_zero (WeierstrassCurve.Affine.Point.map f)]
      exact propext hinj.eq_iff
    simp only [e1, e2]
    exact div_self (div_ne_zero (hne _) (hne _))
  · simp only [not_exists] at hIm
    rw [hT3.2 hg0 Q hQ hIm, WeierstrassCurve.Affine.valuation_weilFun W hn' hfT _ hQ]
    have h1 : ¬ ((n : ℤ) • Q = WeierstrassCurve.Affine.Point.map f T) := by
      intro hnQ

      have hn2 : ((n ^ 2 : ℕ) : K) ≠ 0 := by push_cast; exact pow_ne_zero _ hn
      obtain ⟨P, hP⟩ := htors (n ^ 2) hn2 Q (by
        rw [show ((n ^ 2 : ℕ) : ℤ) = (n : ℤ) * (n : ℤ) by push_cast; ring, mul_smul, hnQ, hfT])
      exact hIm P hP
    have h2 : ¬ ((n : ℤ) • Q = 0) := by
      intro hnQ
      obtain ⟨P, hP⟩ := htors n hn Q hnQ
      exact hIm P hP
    simp only [h1, h2, if_false, div_one]

end S_WeierstrassCurve_Affine_exists_map_weilFun_eq_mul_weilFun_map_of_algHom
end P2MW
export P2MW.S_WeierstrassCurve_Affine_exists_map_weilFun_eq_mul_weilFun_map_of_algHom (solution)
