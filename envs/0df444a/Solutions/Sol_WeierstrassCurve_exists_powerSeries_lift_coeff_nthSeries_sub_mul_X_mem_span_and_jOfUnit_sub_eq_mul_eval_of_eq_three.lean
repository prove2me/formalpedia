-- Prove2me | solution 1 for WeierstrassCurve.exists_powerSeries_lift_coeff_nthSeries_sub_mul_X_mem_span_and_jOfUnit_sub_eq_mul_eval_of_eq_three
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.822295+00:00
-- url     : https://prove2.me/submissions/90af7b5b-16d7-5175-8fc5-f43c415b1a4d

import Mathlib
import Definitions.Def_FormalGroup_NSeries
import Definitions.Def_FormalGroup_DrinfeldBasis
import Definitions.Def_FormalGroup_PointTransport
import Definitions.Def_WeierstrassCurve_FormalGroupLaw
import Definitions.Def_WeierstrassCurve_FormalGroup
import Definitions.Def_ModularCurve_WeierstrassLevelCarrier
import Definitions.Def_WeierstrassCurve_HasseInvariant
import Theorems.Thm_FormalGroup_isDrinfeldBasisAdic_zero_zero_iff
import Theorems.Thm_WeierstrassCurve_exists_coeff_nthSeries_eq_mul_hasseInvariant
import Theorems.Thm_WeierstrassCurve_exists_powerSeries_lift_coeff_nthSeries_sub_mul_X_mem_span_and_jOfUnit_sub_eq_mul_eval_of_coeff_hasseInvariant_map
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_WeierstrassCurve_exists_powerSeries_lift_coeff_nthSeries_sub_mul_X_mem_span_and_jOfUnit_sub_eq_mul_eval_of_eq_three
p2m_attr_erase "simp" "ModularCurve.qExpand_coeff_mul ModularCurve.qExpandₐ_apply ModularCurve.jqN_one ModularCurve.qExpand_single ModularCurve.dedekindPsi_one ModularCurve.ModularPolynomialData.mk.sizeOf_spec ModularCurve.evalAtJ_X ModularCurve.ModularPolynomialData.mk.injEq ModularCurve.constantCoeff_jNum ModularCurve.constantCoeff_eisenstein4 ModularCurve.qExpand_C ModularCurve.coeff_jq_neg_one ModularCurve.constantCoeff_jNumQ"

set_option autoImplicit false

open FormalGroup IsLocalRing

namespace L3Aux
open Polynomial

theorem jOfUnit_sub_1728 {R : Type*} [CommRing R] (W : WeierstrassCurve R) (hΔ : IsUnit W.Δ) :
    W.jOfUnit hΔ - 1728 = ↑hΔ.unit⁻¹ * W.c₆ ^ 2 := by
  haveI : W.IsElliptic := ⟨hΔ⟩
  have h1 : (↑hΔ.unit⁻¹ : R) * W.Δ = 1 := hΔ.val_inv_mul
  have hj : W.jOfUnit hΔ = ↑hΔ.unit⁻¹ * W.c₄ ^ 3 := by
    rw [WeierstrassCurve.jOfUnit_eq_j]; rfl
  rw [hj]
  linear_combination 1728 * h1 - (↑hΔ.unit⁻¹ : R) * W.c_relation

theorem hasseInvariant_three {R : Type*} [CommRing R] (W : WeierstrassCurve R) : W.hasseInvariant 3 = W.b₂ := by
  rw [WeierstrassCurve.hasseInvariant]
  norm_num [WeierstrassCurve.twoTorsionPolynomial, Cubic.coeff_eq_b]

theorem hasseInvariant_eq_zero_of_isDrinfeldBasisAdic {k : Type} [Field k] (q : ℕ) [Fact q.Prime] [CharP k q]
    (hq2 : q ≠ 2) (E₀ : WeierstrassCurve k) [E₀.IsElliptic] (hE₀ : E₀.formalGroup.IsDrinfeldBasisAdic ⊥ q 0 0) :
    E₀.hasseInvariant q = 0 := by
  have hqp : q.Prime := Fact.out
  obtain ⟨u, -, hu⟩ := (FormalGroup.isDrinfeldBasisAdic_zero_zero_iff ⊥ E₀.formalGroup q).mp hE₀
  obtain ⟨c, hc0, hc⟩ := WeierstrassCurve.exists_coeff_nthSeries_eq_mul_hasseInvariant q hq2
  have h1 := hc k E₀ WeierstrassCurve.IsElliptic.isUnit E₀.formalGroup rfl
  rw [hu, PowerSeries.coeff_mul_X_pow', if_neg] at h1
  · have hck : ((c : ℤ) : k) ≠ 0 := by
      intro h
      apply hc0
      rw [ZMod.intCast_zmod_eq_zero_iff_dvd]
      exact (CharP.intCast_eq_zero_iff k q c).mp h
    exact (mul_eq_zero.mp h1.symm).resolve_left hck
  · have : 2 ≤ q := hqp.two_le
    intro hle
    have : q * q ≤ q * 1 := by simpa using hle
    have := Nat.le_of_mul_le_mul_left this (by omega)
    omega

noncomputable def fam {W₀ : Type*} [CommRing W₀] (a1 a2 a3 a4 a6 : W₀) : WeierstrassCurve (PowerSeries W₀) :=
  ⟨PowerSeries.C a1, PowerSeries.C a2 + PowerSeries.X, PowerSeries.C a3, PowerSeries.C a4, PowerSeries.C a6⟩

theorem fam_b₂ {W₀ : Type*} [CommRing W₀] (a1 a2 a3 a4 a6 : W₀) (h : a1 ^ 2 + 4 * a2 = 0) :
    (fam a1 a2 a3 a4 a6).b₂ = 4 * PowerSeries.X := by
  simp only [fam, WeierstrassCurve.b₂]
  have : (PowerSeries.C a1 : PowerSeries W₀) ^ 2 + 4 * PowerSeries.C a2 = 0 := by
    rw [← map_pow, ← map_ofNat (PowerSeries.C (R := W₀)) 4, ← map_mul, ← map_add, h, map_zero]
  linear_combination this

theorem fam_b₄ {W₀ : Type*} [CommRing W₀] (a1 a2 a3 a4 a6 : W₀) :
    (fam a1 a2 a3 a4 a6).b₄ = 2 * PowerSeries.C a4 + PowerSeries.C a1 * PowerSeries.C a3 := by
  simp only [fam, WeierstrassCurve.b₄]

theorem fam_b₆ {W₀ : Type*} [CommRing W₀] (a1 a2 a3 a4 a6 : W₀) :
    (fam a1 a2 a3 a4 a6).b₆ = PowerSeries.C a3 ^ 2 + 4 * PowerSeries.C a6 := by
  simp only [fam, WeierstrassCurve.b₆]

theorem fam_c₆ {W₀ : Type*} [CommRing W₀] (a1 a2 a3 a4 a6 : W₀) (h : a1 ^ 2 + 4 * a2 = 0)
    (i4 i8 : W₀) (hi4 : 4 * i4 = 1) (hi8 : 8 * i8 = 1) :
    (fam a1 a2 a3 a4 a6).c₆ = -64 * (PowerSeries.X ^ 3
        + PowerSeries.C (-9 * i4 * (2 * a4 + a1 * a3)) * PowerSeries.X + PowerSeries.C (27 * i8 * (a3 ^ 2 + 4 * a6))) := by
  rw [WeierstrassCurve.c₆, fam_b₂ a1 a2 a3 a4 a6 h, fam_b₄, fam_b₆]
  have h4 : (PowerSeries.C (4 * i4) : PowerSeries W₀) = 1 := by rw [hi4, map_one]
  have h8 : (PowerSeries.C (8 * i8) : PowerSeries W₀) = 1 := by rw [hi8, map_one]
  rw [map_mul, map_ofNat] at h4 h8
  simp only [map_mul, map_add, map_pow, map_neg, map_ofNat]
  linear_combination (-144 * (2 * PowerSeries.C a4 + PowerSeries.C a1 * PowerSeries.C a3) * PowerSeries.X) * h4 + (216 * (PowerSeries.C a3 ^ 2 + 4 * PowerSeries.C a6)) * h8

end L3Aux

open L3Aux

set_option maxHeartbeats 6400000 in
theorem solution
    (q : ℕ) [Fact q.Prime] (hq : q = 3) (k : Type) [Field k] [CharP k q]
    (E₀ : WeierstrassCurve k) [E₀.IsElliptic] (hE₀ : E₀.formalGroup.IsDrinfeldBasisAdic ⊥ q 0 0)
    (W₀ : Type) [CommRing W₀] [IsDomain W₀] [IsDiscreteValuationRing W₀]
    [IsAdicComplete (maximalIdeal W₀) W₀] (hW₀ : maximalIdeal W₀ = Ideal.span {(q : W₀)})
    (res₀ : W₀ →+* k) (hres₀ : Function.Surjective res₀) (hker₀ : RingHom.ker res₀ = maximalIdeal W₀) :
    ∃ (𝓔 : WeierstrassCurve (PowerSeries W₀)) (h𝓔 : IsUnit 𝓔.Δ)
      (_ : 𝓔.map (res₀.comp (PowerSeries.constantCoeff : PowerSeries W₀ →+* W₀)) = E₀)
      (Fu : FormalGroup (PowerSeries W₀)) (_ : Fu.IsComm) (_ : Fu.toPowerSeries = 𝓔.formalGroupLawFixed)
      (_ : Fu.IsBaseChange (res₀.comp (PowerSeries.constantCoeff : PowerSeries W₀ →+* W₀)) E₀.formalGroup)
      (_ : PowerSeries.coeff 1 (PowerSeries.coeff q (Fu.nthSeries q)) - 1 ∈ maximalIdeal W₀)
      (u₁ : PowerSeries W₀) (_ : IsUnit u₁)
      (_ : PowerSeries.coeff q (Fu.nthSeries q) - u₁ * PowerSeries.X ∈ Ideal.span {(q : PowerSeries W₀)})
      (a₀ : W₀) (e : ℕ) (_ : 1 ≤ e) (u₂ : PowerSeries W₀) (_ : IsUnit u₂)

      (P : Polynomial W₀) (_ : P.Monic) (_ : P.natDegree = e)
      (_ : ∀ i < e, P.coeff i ∈ maximalIdeal W₀ ^ ((e - i) * q / (q + 1) + 1)),
      𝓔.jOfUnit h𝓔 - algebraMap W₀ (PowerSeries W₀) a₀ =
        u₂ * (P.map (algebraMap W₀ (PowerSeries W₀))).eval PowerSeries.X := by
  classical
  subst hq
  have hqp : (3 : ℕ).Prime := Fact.out
  have hq2 : (3 : ℕ) ≠ 2 := by decide

  have hunit : ∀ w : W₀, res₀ w ≠ 0 → IsUnit w := by
    intro w hw
    by_contra hnu
    apply hw
    have : w ∈ RingHom.ker res₀ := by rw [hker₀]; exact (IsLocalRing.mem_maximalIdeal _).mpr hnu
    exact (RingHom.mem_ker).mp this
  have h2k : (2 : k) ≠ 0 := by
    intro h
    have := (CharP.cast_eq_zero_iff k 3 2).mp (by exact_mod_cast h)
    omega
  have h2 : IsUnit (2 : W₀) := hunit 2 (by rw [map_ofNat]; exact h2k)
  have h4 : IsUnit (4 : W₀) := by rw [show (4 : W₀) = 2 ^ 2 by norm_num]; exact h2.pow 2
  have h8 : IsUnit (8 : W₀) := by rw [show (8 : W₀) = 2 ^ 3 by norm_num]; exact h2.pow 3
  obtain ⟨i4, hi4⟩ := h4.exists_right_inv
  obtain ⟨i8, hi8⟩ := h8.exists_right_inv

  have hb₂ : E₀.b₂ = 0 := by
    rw [← hasseInvariant_three]; exact hasseInvariant_eq_zero_of_isDrinfeldBasisAdic 3 hq2 E₀ hE₀

  obtain ⟨a1, ha1⟩ := hres₀ E₀.a₁
  obtain ⟨a3, ha3⟩ := hres₀ E₀.a₃
  obtain ⟨a4, ha4⟩ := hres₀ E₀.a₄
  obtain ⟨a6, ha6⟩ := hres₀ E₀.a₆
  set a2 : W₀ := -(a1 ^ 2) * i4 with ha2def
  have ha12 : a1 ^ 2 + 4 * a2 = 0 := by
    rw [ha2def]; linear_combination (-(a1 ^ 2)) * hi4
  have ha2 : res₀ a2 = E₀.a₂ := by

    have h4k : (4 : k) ≠ 0 := by rw [show (4 : k) = 2 ^ 2 by norm_num]; exact pow_ne_zero _ h2k
    have e1 : res₀ a1 ^ 2 + 4 * res₀ a2 = 0 := by
      have := congrArg res₀ ha12; rwa [map_add, map_mul, map_pow, map_ofNat, map_zero] at this
    rw [ha1] at e1
    have e2 : E₀.a₁ ^ 2 + 4 * E₀.a₂ = 0 := by rw [← hb₂, WeierstrassCurve.b₂]
    have : (4 : k) * (res₀ a2 - E₀.a₂) = 0 := by linear_combination e1 - e2
    exact sub_eq_zero.mp ((mul_eq_zero.mp this).resolve_left h4k)

  set 𝓔 : WeierstrassCurve (PowerSeries W₀) := fam a1 a2 a3 a4 a6 with h𝓔def
  set ρ : PowerSeries W₀ →+* k := res₀.comp (PowerSeries.constantCoeff : PowerSeries W₀ →+* W₀) with hρ
  set π : PowerSeries W₀ →+* PowerSeries k := PowerSeries.map res₀ with hπ
  have hmapρ : 𝓔.map ρ = E₀ := by
    rw [h𝓔def, fam]
    ext <;> simp [hρ, ha1, ha2, ha3, ha4, ha6]

  have hΔ : IsUnit 𝓔.Δ := by
    rw [PowerSeries.isUnit_iff_constantCoeff]
    apply hunit
    have : res₀ (PowerSeries.constantCoeff 𝓔.Δ) = (𝓔.map ρ).Δ := by rw [WeierstrassCurve.map_Δ, hρ]; rfl
    rw [this, hmapρ]
    exact (WeierstrassCurve.IsElliptic.isUnit (W := E₀)).ne_zero

  have hb₂𝓔 : 𝓔.b₂ = 4 * PowerSeries.X := fam_b₂ a1 a2 a3 a4 a6 ha12
  have hH : (𝓔.map π).hasseInvariant 3 = PowerSeries.C (4 : k) * PowerSeries.X := by
    rw [hasseInvariant_three, WeierstrassCurve.map_b₂, hb₂𝓔, map_mul, map_ofNat, hπ, PowerSeries.map_X, map_ofNat]
  have hH0 : PowerSeries.coeff 0 ((𝓔.map π).hasseInvariant 3) = 0 := by
    rw [hH, PowerSeries.coeff_C_mul, PowerSeries.coeff_zero_X, mul_zero]
  have hH1 : PowerSeries.coeff 1 ((𝓔.map π).hasseInvariant 3) ≠ 0 := by
    rw [hH, PowerSeries.coeff_C_mul, PowerSeries.coeff_one_X, mul_one, show (4 : k) = 2 ^ 2 by norm_num]
    exact pow_ne_zero _ h2k

  set q₁ : W₀ := -9 * i4 * (2 * a4 + a1 * a3) with hq₁
  set q₀ : W₀ := 27 * i8 * (a3 ^ 2 + 4 * a6) with hq₀
  set Q : Polynomial W₀ := Polynomial.X ^ 3 + (Polynomial.C q₁ * Polynomial.X + Polynomial.C q₀) with hQ
  have hdeg : (Polynomial.C q₁ * Polynomial.X + Polynomial.C q₀).degree < 3 := by
    refine lt_of_le_of_lt (Polynomial.degree_add_le _ _) (max_lt ?_ ?_)
    · exact lt_of_le_of_lt (Polynomial.degree_C_mul_X_le q₁) (by exact_mod_cast (by norm_num : (1:ℕ) < 3))
    · exact lt_of_le_of_lt Polynomial.degree_C_le (by exact_mod_cast (by norm_num : (0:ℕ) < 3))
  have hQm : Q.Monic := by rw [hQ]; exact Polynomial.monic_X_pow_add hdeg
  have hQd : Q.natDegree = 3 := by
    rw [hQ, Polynomial.natDegree_add_eq_left_of_degree_lt, Polynomial.natDegree_X_pow]
    rw [Polynomial.degree_X_pow]; exact hdeg
  set P : Polynomial W₀ := Q ^ 2 with hP
  have hPm : P.Monic := hQm.pow 2
  have hPd : P.natDegree = 6 := by rw [hP, hQm.natDegree_pow, hQd]

  have hPexp : P = Polynomial.X ^ 6 + Polynomial.C (2 * q₁) * Polynomial.X ^ 4 + Polynomial.C (2 * q₀) * Polynomial.X ^ 3
      + Polynomial.C (q₁ ^ 2) * Polynomial.X ^ 2 + Polynomial.C (2 * q₁ * q₀) * Polynomial.X ^ 1 + Polynomial.C (q₀ ^ 2) * Polynomial.X ^ 0 := by
    rw [hP, hQ]; simp only [map_mul, map_pow, map_ofNat, pow_zero, mul_one, pow_one]; ring
  have hcoeff : ∀ i, P.coeff i = if i = 6 then 1 else if i = 4 then 2 * q₁ else if i = 3 then 2 * q₀ else if i = 2 then q₁ ^ 2
      else if i = 1 then 2 * q₁ * q₀ else if i = 0 then q₀ ^ 2 else 0 := by
    intro i
    rw [hPexp]
    simp only [Polynomial.coeff_add, Polynomial.coeff_C_mul_X_pow, Polynomial.coeff_X_pow]
    split_ifs <;> first | omega | ring

  have hm3 : ∀ (n : ℕ) (x : W₀), (3 : W₀) ^ n ∣ x → x ∈ maximalIdeal W₀ ^ n := by
    intro n x hx
    rw [hW₀, Ideal.span_singleton_pow, Ideal.mem_span_singleton]; exact_mod_cast hx
  have hq₁d : (3 : W₀) ^ 2 ∣ q₁ := ⟨-(i4 * (2 * a4 + a1 * a3)), by rw [hq₁]; ring⟩
  have hq₀d : (3 : W₀) ^ 3 ∣ q₀ := ⟨i8 * (a3 ^ 2 + 4 * a6), by rw [hq₀]; ring⟩
  have hPc : ∀ i < 6, P.coeff i ∈ maximalIdeal W₀ ^ ((6 - i) * 3 / (3 + 1) + 1) := by
    intro i hi
    rw [hcoeff]
    interval_cases i
    ·
      norm_num
      exact Ideal.pow_le_pow_right (by norm_num) (hm3 6 _ (by obtain ⟨c, hc⟩ := hq₀d; exact ⟨c ^ 2, by rw [hc]; ring⟩))
    ·
      norm_num
      exact Ideal.pow_le_pow_right (by norm_num) (hm3 5 _ (by
        obtain ⟨c, hc⟩ := hq₁d; obtain ⟨d, hd⟩ := hq₀d; exact ⟨2 * c * d, by rw [hc, hd]; ring⟩))
    ·
      norm_num
      exact hm3 4 _ (by obtain ⟨c, hc⟩ := hq₁d; exact ⟨c ^ 2, by rw [hc]; ring⟩)
    ·
      norm_num
      exact hm3 3 _ (by obtain ⟨d, hd⟩ := hq₀d; exact ⟨2 * d, by rw [hd]; ring⟩)
    ·
      norm_num
      exact hm3 2 _ (by obtain ⟨c, hc⟩ := hq₁d; exact ⟨2 * c, by rw [hc]; ring⟩)
    ·
      norm_num

  have hc₆ := fam_c₆ a1 a2 a3 a4 a6 ha12 i4 i8 hi4 hi8
  have hPeval : (P.map (algebraMap W₀ (PowerSeries W₀))).eval PowerSeries.X =
      (PowerSeries.X ^ 3 + PowerSeries.C q₁ * PowerSeries.X + PowerSeries.C q₀) ^ 2 := by
    rw [hP, hQ]
    simp only [Polynomial.map_pow, Polynomial.map_add, Polynomial.map_mul, Polynomial.map_X, Polynomial.map_C,
      Polynomial.eval_pow, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_X, Polynomial.eval_C, ← PowerSeries.C_eq_algebraMap]
    ring
  have h4096 : IsUnit (4096 : W₀) := by rw [show (4096 : W₀) = 2 ^ 12 by norm_num]; exact h2.pow 12
  have hc₆' : 𝓔.c₆ = -64 * (PowerSeries.X ^ 3 + PowerSeries.C q₁ * PowerSeries.X + PowerSeries.C q₀) := by
    rw [hq₁, hq₀]; exact hc₆
  have hj0 := jOfUnit_sub_1728 𝓔 hΔ
  have hj : 𝓔.jOfUnit hΔ - algebraMap W₀ (PowerSeries W₀) 1728 =
      (↑hΔ.unit⁻¹ * PowerSeries.C (4096 : W₀)) * (P.map (algebraMap W₀ (PowerSeries W₀))).eval PowerSeries.X := by
    rw [hPeval, map_ofNat, hj0, hc₆', show (PowerSeries.C (4096 : W₀) : PowerSeries W₀) = 4096 from map_ofNat _ _]
    ring

  exact WeierstrassCurve.exists_powerSeries_lift_coeff_nthSeries_sub_mul_X_mem_span_and_jOfUnit_sub_eq_mul_eval_of_coeff_hasseInvariant_map
    3 hq2 k E₀ W₀ hW₀ res₀ hres₀ hker₀ 𝓔 hΔ hmapρ hH0 hH1 1728 6 (by norm_num) _ ((Units.isUnit _).mul (h4096.map _))
    P hPm hPd hPc hj

end S_WeierstrassCurve_exists_powerSeries_lift_coeff_nthSeries_sub_mul_X_mem_span_and_jOfUnit_sub_eq_mul_eval_of_eq_three
end P2MW
export P2MW.S_WeierstrassCurve_exists_powerSeries_lift_coeff_nthSeries_sub_mul_X_mem_span_and_jOfUnit_sub_eq_mul_eval_of_eq_three (solution)
