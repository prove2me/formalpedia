-- Prove2me | solution 1 for WeierstrassCurve.DrinfeldGlobal.mem_comap_maximalIdeal_pow_of_map_mem_maximalIdeal_pow
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.822295+00:00
-- url     : https://prove2.me/submissions/cf8eea10-77ff-583d-83f2-e382ba8d4e3d

import Mathlib
import Definitions.Def_FormalGroup_NSeries
import Definitions.Def_WeierstrassCurve_FormalGroupLaw
import Definitions.Def_WeierstrassCurve_ProjModel
import Definitions.Def_WeierstrassCurve_DrinfeldBasisGlobal
import Definitions.Def_WeierstrassCurve_SectionAtOrigin

import Theorems.Thm_WeierstrassCurve_DrinfeldGlobal_ringHom_originChartRing_ext
import Theorems.Thm_WeierstrassCurve_DrinfeldGlobal_originChart_rel
import Theorems.Thm_WeierstrassCurve_DrinfeldGlobal_originChart_rel_unique_of_mem_maximalIdeal
import Theorems.Thm_IsAdicComplete_of_isNilpotent
import Theorems.Thm_FormalGroup_exists_ringHom_evalSeries_eq
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_WeierstrassCurve_DrinfeldGlobal_mem_comap_maximalIdeal_pow_of_map_mem_maximalIdeal_pow

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory WeierstrassProjModel WeierstrassCurve.DrinfeldGlobal IsLocalRing HomogeneousLocalization

attribute [local instance] MvPolynomial.gradedAlgebra

set_option maxHeartbeats 4000000 in
theorem solution
    {T : Type} [CommRing T] [IsLocalRing T] (W : WeierstrassCurve T)
    (Φ : OriginChartRing W →+* PowerSeries T)
    (hΦsc : ∀ t : T, Φ (fromZeroRingHom (projModelGradingCR W) _ (algebraMap T ((projModelGradingCR W) 0) t)) =
      PowerSeries.C t)
    (hΦx : Φ (xOverY W) = - PowerSeries.X) (hΦz : Φ (zOverY W) = - W.formalW)
    (n : ℕ) (a : OriginChartRing W) (ha : Φ a ∈ maximalIdeal (PowerSeries T) ^ n) :
    a ∈ Ideal.comap Φ (maximalIdeal (PowerSeries T)) ^ n := by
  classical
  set 𝔑 : Ideal (PowerSeries T) := maximalIdeal (PowerSeries T) with h𝔑
  set 𝔭 : Ideal (OriginChartRing W) := Ideal.comap Φ 𝔑 with h𝔭

  rcases Nat.eq_zero_or_pos n with h0 | hn
  · subst h0; rw [pow_zero, Ideal.one_eq_top]; exact Submodule.mem_top

  let sc : T →+* OriginChartRing W :=
    (fromZeroRingHom (projModelGradingCR W) _).comp (algebraMap T ((projModelGradingCR W) 0))
  have hsc' : ∀ t : T, Φ (sc t) = PowerSeries.C t := hΦsc

  have mem𝔑 : ∀ f : PowerSeries T, f ∈ 𝔑 ↔ PowerSeries.constantCoeff f ∈ maximalIdeal T := by
    intro f
    rw [h𝔑, mem_maximalIdeal, mem_nonunits_iff, PowerSeries.isUnit_iff_constantCoeff, mem_maximalIdeal,
      mem_nonunits_iff]
  have hsc𝔭 : ∀ t : T, t ∈ maximalIdeal T → sc t ∈ 𝔭 := by
    intro t ht
    show Φ (sc t) ∈ 𝔑
    rw [hsc', mem𝔑, PowerSeries.constantCoeff_C]; exact ht
  have hx𝔭 : xOverY W ∈ 𝔭 := by
    show Φ (xOverY W) ∈ 𝔑
    rw [hΦx, mem𝔑, map_neg, PowerSeries.constantCoeff_X, neg_zero]; exact zero_mem _
  have hz𝔭 : zOverY W ∈ 𝔭 := by
    show Φ (zOverY W) ∈ 𝔑
    rw [hΦz, mem𝔑, map_neg, W.constantCoeff_formalW, neg_zero]; exact zero_mem _
  have approx : ∀ x : OriginChartRing W, x - sc (PowerSeries.constantCoeff (Φ x)) ∈ 𝔭 := by
    intro x
    show Φ (x - sc _) ∈ 𝔑
    rw [map_sub, hsc', mem𝔑, map_sub, PowerSeries.constantCoeff_C, sub_self]; exact zero_mem _
  have h1 : (1 : OriginChartRing W) ∉ 𝔭 := by
    show Φ 1 ∉ 𝔑
    rw [map_one]; exact (maximalIdeal.isMaximal _).ne_top ∘ (Ideal.eq_top_iff_one _).mpr

  have h𝔭n : 𝔭 ^ n ≠ ⊤ := fun h => h1 (Ideal.pow_le_self hn.ne' (h.symm ▸ Submodule.mem_top))
  haveI : Nontrivial (OriginChartRing W ⧸ 𝔭 ^ n) :=
    ⟨⟨0, 1, fun h => h𝔭n (Ideal.Quotient.zero_eq_one_iff.mp h)⟩⟩
  set π : OriginChartRing W →+* OriginChartRing W ⧸ 𝔭 ^ n := Ideal.Quotient.mk (𝔭 ^ n) with hπ
  have hπ0 : ∀ x ∈ 𝔭 ^ n, π x = 0 := fun x hx => Ideal.Quotient.eq_zero_iff_mem.mpr hx
  have hnil : ∀ x ∈ 𝔭, IsNilpotent (π x) := fun x hx =>
    ⟨n, by rw [← map_pow]; exact hπ0 _ (Ideal.pow_mem_pow hx n)⟩
  have hunit : ∀ x : OriginChartRing W, x ∉ 𝔭 → IsUnit (π x) := by
    intro x hx
    set t := PowerSeries.constantCoeff (Φ x)
    have ht : IsUnit t := by
      by_contra htu
      apply hx
      have : x = (x - sc t) + sc t := by ring
      rw [this]
      exact Ideal.add_mem _ (approx x) (hsc𝔭 t ((mem_maximalIdeal _).mpr (mem_nonunits_iff.mpr htu)))
    have : π x = π (sc t) + π (x - sc t) := by rw [← map_add]; congr 1; ring
    rw [this]
    exact IsNilpotent.isUnit_add_left_of_commute (hnil _ (approx x)) ((ht.map sc).map π) (Commute.all _ _)
  haveI : IsLocalRing (OriginChartRing W ⧸ 𝔭 ^ n) := by
    apply IsLocalRing.of_isUnit_or_isUnit_one_sub_self
    intro b
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective b
    change IsUnit (π x) ∨ IsUnit (1 - π x)
    by_cases hx : x ∈ 𝔭
    · right
      have : (1 : OriginChartRing W ⧸ 𝔭 ^ n) - π x = 1 + π (-x) := by rw [map_neg]; ring
      rw [this]
      have hneg : IsNilpotent (π (-x)) := by rw [map_neg]; exact (hnil x hx).neg
      exact IsNilpotent.isUnit_add_left_of_commute hneg isUnit_one (Commute.all _ _)
    · left; exact hunit x hx
  have hmemB : ∀ x ∈ 𝔭, π x ∈ maximalIdeal (OriginChartRing W ⧸ 𝔭 ^ n) := by
    intro x hx
    rw [mem_maximalIdeal, mem_nonunits_iff]
    intro hu
    obtain ⟨k, hk⟩ := hnil x hx
    have : IsUnit ((π x) ^ k) := hu.pow k
    rw [hk] at this
    exact not_isUnit_zero this

  set 𝔭b : Ideal (OriginChartRing W ⧸ 𝔭 ^ n) := 𝔭.map π with h𝔭b
  have h𝔭bn : 𝔭b ^ n = ⊥ := by
    rw [h𝔭b, ← Ideal.map_pow, hπ, Ideal.map_quotient_self]
  haveI : IsAdicComplete 𝔭b (OriginChartRing W ⧸ 𝔭 ^ n) := IsAdicComplete.of_isNilpotent ⟨n, h𝔭bn⟩

  set x₀ : OriginChartRing W ⧸ 𝔭 ^ n := - π (xOverY W) with hx₀
  have hx₀mem : x₀ ∈ 𝔭b := neg_mem (Ideal.mem_map_of_mem π hx𝔭)
  obtain ⟨e, -, hep⟩ := FormalGroup.exists_ringHom_evalSeries_eq 𝔭b x₀ hx₀mem
  let θ : PowerSeries T →+* OriginChartRing W ⧸ 𝔭 ^ n := e.comp (PowerSeries.map (π.comp sc))
  have hθX : θ PowerSeries.X = x₀ := by
    show e (PowerSeries.map (π.comp sc) PowerSeries.X) = x₀
    rw [PowerSeries.map_X, ← Polynomial.coe_X, hep, Polynomial.eval_X]
  have hθC : ∀ t : T, θ (PowerSeries.C t) = π (sc t) := by
    intro t
    show e (PowerSeries.map (π.comp sc) (PowerSeries.C t)) = π (sc t)
    rw [PowerSeries.map_C, ← Polynomial.coe_C, hep, Polynomial.eval_C]; rfl

  letI algB : Algebra T (OriginChartRing W ⧸ 𝔭 ^ n) := (π.comp sc).toAlgebra
  have halg : ∀ t : T, algebraMap T (OriginChartRing W ⧸ 𝔭 ^ n) t = π (sc t) := fun t => rfl
  have hu : π (xOverY W) ∈ maximalIdeal _ := hmemB _ hx𝔭
  have hv : π (zOverY W) ∈ maximalIdeal _ := hmemB _ hz𝔭
  have hx₀' : x₀ ∈ maximalIdeal (OriginChartRing W ⧸ 𝔭 ^ n) := by rw [hx₀]; exact neg_mem hu
  have hv' : θ (Φ (zOverY W)) ∈ maximalIdeal _ := by
    obtain ⟨w₁, hw⟩ := W.X_dvd_formalW
    rw [hΦz, map_neg, hw, map_mul, hθX]
    exact neg_mem (Ideal.mul_mem_right _ _ hx₀')
  have hxx : θ (Φ (xOverY W)) = π (xOverY W) := by rw [hΦx, map_neg, hθX, hx₀, neg_neg]
  have hrel := WeierstrassCurve.DrinfeldGlobal.originChart_rel W (B := OriginChartRing W ⧸ 𝔭 ^ n) π (fun t => rfl)
  have hrel' := WeierstrassCurve.DrinfeldGlobal.originChart_rel W (B := OriginChartRing W ⧸ 𝔭 ^ n) (θ.comp Φ)
    (fun t => by show θ (Φ (sc t)) = π (sc t); rw [hsc', hθC])
  simp only [RingHom.comp_apply] at hrel'
  rw [hxx] at hrel'
  simp only [halg] at hrel hrel'
  have hzz : θ (Φ (zOverY W)) = π (zOverY W) :=
    (WeierstrassCurve.DrinfeldGlobal.originChart_rel_unique_of_mem_maximalIdeal _ _ _ _ _ _ _ _ hu hv hv' hrel hrel').symm
  have hθΦ : θ.comp Φ = π :=
    WeierstrassCurve.DrinfeldGlobal.ringHom_originChartRing_ext W (θ.comp Φ) π
      (fun t => by show θ (Φ (sc t)) = π (sc t); rw [hsc', hθC]) hxx hzz

  have hθ𝔑 : 𝔑.map θ ≤ 𝔭b := by
    rw [Ideal.map_le_iff_le_comap]
    intro f hf
    rw [mem𝔑] at hf
    show θ f ∈ 𝔭b
    rw [PowerSeries.eq_X_mul_shift_add_const f, map_add, map_mul, hθX, hθC]
    exact Ideal.add_mem _ (Ideal.mul_mem_right _ _ hx₀mem) (Ideal.mem_map_of_mem π (hsc𝔭 _ hf))

  have hmem : θ (Φ a) ∈ 𝔭b ^ n := by
    have : θ (Φ a) ∈ (𝔑.map θ) ^ n := by
      rw [← Ideal.map_pow]; exact Ideal.mem_map_of_mem θ ha
    exact Ideal.pow_right_mono hθ𝔑 n this
  rw [h𝔭bn, Ideal.mem_bot] at hmem
  have : π a = 0 := by rw [← hθΦ]; exact hmem
  exact Ideal.Quotient.eq_zero_iff_mem.mp this

end S_WeierstrassCurve_DrinfeldGlobal_mem_comap_maximalIdeal_pow_of_map_mem_maximalIdeal_pow
end P2MW
export P2MW.S_WeierstrassCurve_DrinfeldGlobal_mem_comap_maximalIdeal_pow_of_map_mem_maximalIdeal_pow (solution)
