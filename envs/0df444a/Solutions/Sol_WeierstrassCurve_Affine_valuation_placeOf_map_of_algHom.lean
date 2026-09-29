-- Prove2me | solution 1 for WeierstrassCurve.Affine.valuation_placeOf_map_of_algHom
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.503601+00:00
-- url     : https://prove2.me/submissions/9fd4fc7c-f995-5e50-acd2-c1b36ea55eda

import Mathlib
import Definitions.Def_EllipticCurve_WeilPairingFun
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_WeierstrassCurve_Affine_valuation_placeOf_map_of_algHom

set_option autoImplicit false

open WeierstrassCurve WeierstrassCurve.Affine IsDedekindDomain IsDedekindDomain.HeightOneSpectrum WithZero
open Polynomial
open scoped Polynomial.Bivariate

namespace K8T3a

section BCRing

variable {F K K' : Type*} [Field F] [Field K] [Field K'] [Algebra F K] [Algebra F K'] (W : WeierstrassCurve F)
  (f : K →ₐ[F] K')

noncomputable def bcHom : (W⁄K).CoordinateRing →+* (W⁄K').CoordinateRing :=
  AdjoinRoot.lift ((AdjoinRoot.of _).comp <| mapRingHom (f : K →+* K'))
    (AdjoinRoot.root (W⁄K').polynomial) <| by
      rw [← eval₂_map, ← baseChange_polynomial (W := W) (f := f), AdjoinRoot.eval₂_root]

theorem bcHom_mk (p : K[X][Y]) :
    bcHom W f (CoordinateRing.mk (W⁄K) p) = CoordinateRing.mk (W⁄K') (p.map (mapRingHom (f : K →+* K'))) := by
  rw [bcHom, CoordinateRing.mk, AdjoinRoot.lift_mk, ← eval₂_map]
  exact AdjoinRoot.aeval_eq <| p.map <| mapRingHom (f : K →+* K')

theorem map_XYIdeal (x y : K) :
    (CoordinateRing.XYIdeal (W⁄K) x (C y)).map (bcHom W f) = CoordinateRing.XYIdeal (W⁄K') (f x) (C (f y)) := by
  rw [CoordinateRing.XYIdeal, Ideal.map_span, Set.image_pair, CoordinateRing.XClass,
    CoordinateRing.YClass, bcHom_mk, bcHom_mk]
  simp only [Polynomial.map_sub, Polynomial.map_C, Polynomial.map_X, coe_mapRingHom, RingHom.coe_coe]
  rfl

variable [DecidableEq K] [DecidableEq K']

theorem xc_map (P : (W⁄K).Point) : (WeierstrassCurve.Affine.Point.map f P).xc = f P.xc := by
  rcases P with _ | ⟨x, y, h⟩
  · exact (map_zero f).symm
  · rfl

theorem yc_map (P : (W⁄K).Point) : (WeierstrassCurve.Affine.Point.map f P).yc = f P.yc := by
  rcases P with _ | ⟨x, y, h⟩
  · exact (map_zero f).symm
  · rfl

variable [IsDedekindDomain (W⁄K).CoordinateRing] [IsDedekindDomain (W⁄K').CoordinateRing]

theorem map_placeOf (P : (W⁄K).Point) (hP : P ≠ 0) (hfP : WeierstrassCurve.Affine.Point.map f P ≠ 0) :
    (placeOf W K P hP).asIdeal.map (bcHom W f) = (placeOf W K' (WeierstrassCurve.Affine.Point.map f P) hfP).asIdeal := by
  rw [placeOf_asIdeal, placeOf_asIdeal, map_XYIdeal, xc_map, yc_map]

theorem comap_placeOf (P : (W⁄K).Point) (hP : P ≠ 0) (hfP : WeierstrassCurve.Affine.Point.map f P ≠ 0) :
    (placeOf W K' (WeierstrassCurve.Affine.Point.map f P) hfP).asIdeal.comap (bcHom W f) = (placeOf W K P hP).asIdeal := by
  have hmax : (placeOf W K P hP).asIdeal.IsMaximal := by
    rw [placeOf_asIdeal]
    exact CoordinateRing.XYIdeal_isMaximal (Point.nonsingular_xc_yc hP).left
  symm
  apply hmax.eq_of_le
  · exact Ideal.comap_ne_top _ (placeOf W K' _ hfP).isPrime.ne_top
  · rw [← Ideal.map_le_iff_le_comap, map_placeOf W f P hP hfP]

end BCRing

section Transfer

variable {R S : Type*} [CommRing R] [IsDedekindDomain R] [CommRing S] [IsDedekindDomain S]
  (φ : R →+* S) (v : HeightOneSpectrum R) (w : HeightOneSpectrum S)
  (hmap : v.asIdeal.map φ = w.asIdeal) (hcomap : w.asIdeal.comap φ = v.asIdeal)

include hmap in
theorem mem_pow_of_mem_pow {r : R} {n : ℕ} (h : r ∈ v.asIdeal ^ n) : φ r ∈ w.asIdeal ^ n := by
  rw [← hmap, ← Ideal.map_pow]; exact Ideal.mem_map_of_mem _ h

include hmap hcomap in
theorem mem_pow_iff (r : R) (hr : r ≠ 0) (n : ℕ) : φ r ∈ w.asIdeal ^ n ↔ r ∈ v.asIdeal ^ n := by
  classical
  refine ⟨fun h => ?_, mem_pow_of_mem_pow φ v w hmap⟩

  obtain ⟨m, hm, hm'⟩ : ∃ m : ℕ, r ∈ v.asIdeal ^ m ∧ r ∉ v.asIdeal ^ (m + 1) := by
    have hv : v.intValuation r = WithZero.exp (-((Associates.mk v.asIdeal).count (Associates.mk (Ideal.span {r})).factors : ℤ)) :=
      v.intValuation_if_neg hr
    refine ⟨_, (v.intValuation_le_pow_iff_mem r _).mp hv.le, fun h' => ?_⟩
    have := (v.intValuation_le_pow_iff_mem r _).mpr h'
    rw [hv, WithZero.exp_le_exp] at this
    push_cast at this; omega

  obtain ⟨J, hJ⟩ : v.asIdeal ^ m ∣ Ideal.span {r} := by
    rw [Ideal.dvd_iff_le, Ideal.span_singleton_le_iff_mem]; exact hm
  have hJv : ¬ J ≤ v.asIdeal := by
    intro hle; apply hm'
    rw [← Ideal.span_singleton_le_iff_mem, hJ, pow_succ]
    exact Ideal.mul_mono_right hle

  have hJw : ¬ J.map φ ≤ w.asIdeal := by
    intro hle; apply hJv
    rw [Ideal.map_le_iff_le_comap, hcomap] at hle; exact hle
  have hspan : Ideal.span {φ r} = w.asIdeal ^ m * J.map φ := by
    rw [← Set.image_singleton, ← Ideal.map_span, hJ, Ideal.map_mul, Ideal.map_pow, hmap]
  have hnot : φ r ∉ w.asIdeal ^ (m + 1) := by
    intro h'
    rw [← Ideal.span_singleton_le_iff_mem, hspan, ← Ideal.dvd_iff_le, pow_succ] at h'
    have hw0 : w.asIdeal ^ m ≠ 0 := pow_ne_zero _ w.ne_bot
    have := (mul_dvd_mul_iff_left hw0).mp h'
    rw [Ideal.dvd_iff_le] at this
    exact hJw this

  have hnm : n ≤ m := by
    by_contra hlt
    exact hnot (Ideal.pow_le_pow_right (by omega) h)
  exact Ideal.pow_le_pow_right hnm hm

include hmap hcomap in
theorem intValuation_eq (r : R) : w.intValuation (φ r) = v.intValuation r := by
  classical
  by_cases hr : r = 0
  · simp [hr]
  have hφr : φ r ≠ 0 := by
    intro h0
    obtain ⟨m, -, hm'⟩ : ∃ m : ℕ, r ∈ v.asIdeal ^ m ∧ r ∉ v.asIdeal ^ (m + 1) := by
      have hv : v.intValuation r = WithZero.exp (-((Associates.mk v.asIdeal).count (Associates.mk (Ideal.span {r})).factors : ℤ)) :=
        v.intValuation_if_neg hr
      refine ⟨_, (v.intValuation_le_pow_iff_mem r _).mp hv.le, fun h' => ?_⟩
      have := (v.intValuation_le_pow_iff_mem r _).mpr h'
      rw [hv, WithZero.exp_le_exp] at this
      push_cast at this; omega
    exact hm' ((mem_pow_iff φ v w hmap hcomap r hr _).mp (by rw [h0]; exact zero_mem _))
  obtain ⟨m₁, hm₁⟩ : ∃ m : ℕ, v.intValuation r = WithZero.exp (-(m : ℤ)) := ⟨_, v.intValuation_if_neg hr⟩
  obtain ⟨m₂, hm₂⟩ : ∃ m : ℕ, w.intValuation (φ r) = WithZero.exp (-(m : ℤ)) := ⟨_, w.intValuation_if_neg hφr⟩
  apply le_antisymm
  · rw [hm₁, intValuation_le_pow_iff_mem, mem_pow_iff φ v w hmap hcomap r hr, ← intValuation_le_pow_iff_mem, ← hm₁]
  · rw [hm₂, intValuation_le_pow_iff_mem, ← mem_pow_iff φ v w hmap hcomap r hr, ← intValuation_le_pow_iff_mem, ← hm₂]

end Transfer

end K8T3a

theorem solution
    {F K K' : Type*} [Field F] [Field K] [Field K'] [Algebra F K] [Algebra F K'] [DecidableEq K] [DecidableEq K']
    [IsAlgClosed K] (W : WeierstrassCurve F) [W.IsElliptic]
    [IsDedekindDomain (W⁄K).CoordinateRing] [IsDedekindDomain (W⁄K').CoordinateRing]
    (f : K →ₐ[F] K')
    (Φ : (W⁄K).FunctionField →+* (W⁄K').FunctionField)
    (hΦ : ∀ p : K[X][Y], Φ (algebraMap (W⁄K).CoordinateRing (W⁄K).FunctionField (CoordinateRing.mk (W⁄K) p)) =
      algebraMap (W⁄K').CoordinateRing (W⁄K').FunctionField (CoordinateRing.mk (W⁄K') (p.map (mapRingHom (f : K →+* K')))))
    (h : (W⁄K).FunctionField) :
    (∀ (P : (W⁄K).Point) (hP : P ≠ 0) (hfP : WeierstrassCurve.Affine.Point.map f P ≠ 0),
        (placeOf W K' (WeierstrassCurve.Affine.Point.map f P) hfP).valuation (W⁄K').FunctionField (Φ h) =
          (placeOf W K P hP).valuation (W⁄K).FunctionField h) ∧
    (h ≠ 0 → ∀ (P' : (W⁄K').Point) (hP' : P' ≠ 0),
        (∀ P : (W⁄K).Point, WeierstrassCurve.Affine.Point.map f P ≠ P') →
        (placeOf W K' P' hP').valuation (W⁄K').FunctionField (Φ h) = 1) := by
  classical
  let φ := K8T3a.bcHom W f
  have hΦφ : ∀ a : (W⁄K).CoordinateRing, Φ (algebraMap _ (W⁄K).FunctionField a) =
      algebraMap _ (W⁄K').FunctionField (φ a) := by
    intro a
    induction a using AdjoinRoot.induction_on with
    | ih g => exact (hΦ g).trans (congrArg _ (K8T3a.bcHom_mk W f g).symm)
  refine ⟨?_, ?_⟩
  ·
    intro P hP hfP
    obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := (W⁄K).CoordinateRing) h
    have key := K8T3a.intValuation_eq φ (placeOf W K P hP) (placeOf W K' _ hfP)
      (K8T3a.map_placeOf W f P hP hfP) (K8T3a.comap_placeOf W f P hP hfP)
    rw [map_div₀, hΦφ, hΦφ, map_div₀, map_div₀, valuation_of_algebraMap, valuation_of_algebraMap,
      valuation_of_algebraMap, valuation_of_algebraMap, key, key]
  ·
    intro hh Q hQ hnot
    obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := (W⁄K).CoordinateRing) h
    have ha : a ≠ 0 := by
      rintro rfl; apply hh; rw [map_zero, zero_div]
    have hb0 : b ≠ 0 := nonZeroDivisors.ne_zero hb

    have hone : ∀ c : (W⁄K).CoordinateRing, c ≠ 0 →
        (placeOf W K' Q hQ).intValuation (φ c) = 1 := by
      intro c hc
      by_contra hne
      have hlt : (placeOf W K' Q hQ).intValuation (φ c) < 1 :=
        lt_of_le_of_ne ((placeOf W K' Q hQ).intValuation_le_one _) hne
      rw [IsDedekindDomain.HeightOneSpectrum.intValuation_lt_one_iff_mem] at hlt

      let 𝔭 : Ideal (W⁄K).CoordinateRing := (placeOf W K' Q hQ).asIdeal.comap φ
      have h𝔭prime : 𝔭.IsPrime := Ideal.comap_isPrime φ _
      have h𝔭ne : 𝔭 ≠ ⊥ := by
        intro h0
        have : c ∈ 𝔭 := hlt
        rw [h0, Ideal.mem_bot] at this
        exact hc this
      obtain ⟨P, hP, hPv⟩ := placeOf_surjective W K ⟨𝔭, h𝔭prime, h𝔭ne⟩
      have hfP : WeierstrassCurve.Affine.Point.map f P ≠ 0 := by
        intro h0; apply hP
        exact Point.map_injective _ (by rw [h0, map_zero])
      apply hnot P
      apply placeOf_injective W K' hfP hQ
      apply IsDedekindDomain.HeightOneSpectrum.ext
      have h1 : (placeOf W K P hP).asIdeal = 𝔭 := congrArg IsDedekindDomain.HeightOneSpectrum.asIdeal hPv
      have hle : (placeOf W K' (WeierstrassCurve.Affine.Point.map f P) hfP).asIdeal ≤ (placeOf W K' Q hQ).asIdeal := by
        rw [← K8T3a.map_placeOf W f P hP hfP, Ideal.map_le_iff_le_comap, h1]
      have hmax : (placeOf W K' (WeierstrassCurve.Affine.Point.map f P) hfP).asIdeal.IsMaximal := by
        rw [placeOf_asIdeal]
        exact CoordinateRing.XYIdeal_isMaximal (Point.nonsingular_xc_yc hfP).left
      exact hmax.eq_of_le (placeOf W K' Q hQ).isPrime.ne_top hle
    rw [map_div₀, hΦφ, hΦφ, map_div₀, valuation_of_algebraMap, valuation_of_algebraMap, hone a ha, hone b hb0,
      div_one]

end S_WeierstrassCurve_Affine_valuation_placeOf_map_of_algHom
end P2MW
export P2MW.S_WeierstrassCurve_Affine_valuation_placeOf_map_of_algHom (solution)
