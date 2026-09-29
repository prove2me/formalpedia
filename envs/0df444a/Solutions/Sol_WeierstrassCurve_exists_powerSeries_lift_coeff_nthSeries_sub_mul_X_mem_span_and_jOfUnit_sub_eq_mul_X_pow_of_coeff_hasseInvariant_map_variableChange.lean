-- Prove2me | solution 1 for WeierstrassCurve.exists_powerSeries_lift_coeff_nthSeries_sub_mul_X_mem_span_and_jOfUnit_sub_eq_mul_X_pow_of_coeff_hasseInvariant_map_variableChange
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.822295+00:00
-- url     : https://prove2.me/submissions/97d73047-c501-57b1-973e-b0a0030d72d9

import Mathlib
import Definitions.Def_FormalGroup_NSeries
import Definitions.Def_FormalGroup_DrinfeldBasis
import Definitions.Def_FormalGroup_PointTransport
import Definitions.Def_WeierstrassCurve_FormalGroupLaw
import Definitions.Def_WeierstrassCurve_FormalGroup
import Definitions.Def_WeierstrassCurve_HasseInvariant
import Definitions.Def_ModularCurve_WeierstrassLevelCarrier
import Theorems.Thm_WeierstrassCurve_exists_powerSeries_lift_coeff_nthSeries_sub_mul_X_mem_span_and_jOfUnit_sub_eq_mul_X_pow_of_coeff_hasseInvariant_map
import Theorems.Thm_WeierstrassCurve_hasseInvariant_variableChange
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_WeierstrassCurve_exists_powerSeries_lift_coeff_nthSeries_sub_mul_X_mem_span_and_jOfUnit_sub_eq_mul_X_pow_of_coeff_hasseInvariant_map_variableChange
p2m_attr_erase "simp" "ModularCurve.qExpand_coeff_mul ModularCurve.qExpandₐ_apply ModularCurve.jqN_one ModularCurve.qExpand_single ModularCurve.dedekindPsi_one ModularCurve.ModularPolynomialData.mk.sizeOf_spec ModularCurve.evalAtJ_X ModularCurve.ModularPolynomialData.mk.injEq ModularCurve.constantCoeff_jNum ModularCurve.constantCoeff_eisenstein4 ModularCurve.qExpand_C ModularCurve.coeff_jq_neg_one ModularCurve.constantCoeff_jNumQ"

set_option autoImplicit false

open FormalGroup IsLocalRing

theorem solution
    (q : ℕ) [Fact q.Prime] (hq : q ≠ 2) (k : Type) [Field k] [CharP k q]
    (E₀ : WeierstrassCurve k) [E₀.IsElliptic]
    (W₀ : Type) [CommRing W₀] [IsDomain W₀] [IsDiscreteValuationRing W₀]
    [IsAdicComplete (maximalIdeal W₀) W₀] (hW₀ : maximalIdeal W₀ = Ideal.span {(q : W₀)})
    (res₀ : W₀ →+* k) (hres₀ : Function.Surjective res₀) (hker₀ : RingHom.ker res₀ = maximalIdeal W₀)
    (C₀ : WeierstrassCurve.VariableChange k)
    (𝓔 : WeierstrassCurve (PowerSeries W₀)) (h𝓔 : IsUnit 𝓔.Δ)
    (h𝓔₀ : 𝓔.map (res₀.comp (PowerSeries.constantCoeff : PowerSeries W₀ →+* W₀)) = C₀ • E₀)
    (hH0 : PowerSeries.coeff 0 ((𝓔.map (PowerSeries.map res₀)).hasseInvariant q) = 0)
    (hH1 : PowerSeries.coeff 1 ((𝓔.map (PowerSeries.map res₀)).hasseInvariant q) ≠ 0)
    (a₀ : W₀) (e : ℕ) (he : 1 ≤ e) (u₂ : PowerSeries W₀) (hu₂ : IsUnit u₂)
    (hj : 𝓔.jOfUnit h𝓔 - algebraMap W₀ (PowerSeries W₀) a₀ = u₂ * PowerSeries.X ^ e) :
    ∃ (𝓔 : WeierstrassCurve (PowerSeries W₀)) (h𝓔 : IsUnit 𝓔.Δ)
      (_ : 𝓔.map (res₀.comp (PowerSeries.constantCoeff : PowerSeries W₀ →+* W₀)) = E₀)
      (Fu : FormalGroup (PowerSeries W₀)) (_ : Fu.IsComm) (_ : Fu.toPowerSeries = 𝓔.formalGroupLawFixed)
      (_ : Fu.IsBaseChange (res₀.comp (PowerSeries.constantCoeff : PowerSeries W₀ →+* W₀)) E₀.formalGroup)
      (_ : PowerSeries.coeff 1 (PowerSeries.coeff q (Fu.nthSeries q)) - 1 ∈ maximalIdeal W₀)
      (u₁ : PowerSeries W₀) (_ : IsUnit u₁)
      (_ : PowerSeries.coeff q (Fu.nthSeries q) - u₁ * PowerSeries.X ∈ Ideal.span {(q : PowerSeries W₀)})
      (a₀ : W₀) (e : ℕ) (_ : 1 ≤ e) (u₂ : PowerSeries W₀) (_ : IsUnit u₂),
      𝓔.jOfUnit h𝓔 - algebraMap W₀ (PowerSeries W₀) a₀ = u₂ * PowerSeries.X ^ e := by
  classical

  obtain ⟨ut, hut⟩ := hres₀ ((C₀.u : kˣ) : k)
  obtain ⟨rt, hrt⟩ := hres₀ C₀.r
  obtain ⟨st, hst⟩ := hres₀ C₀.s
  obtain ⟨tt, htt⟩ := hres₀ C₀.t
  have hutu : IsUnit ut := by
    by_contra h
    have hm : ut ∈ maximalIdeal W₀ := (mem_maximalIdeal ut).mpr h
    rw [← hker₀, RingHom.mem_ker, hut] at hm
    exact (C₀.u).ne_zero hm
  obtain ⟨Cw, hCw⟩ : ∃ Cw : WeierstrassCurve.VariableChange W₀, Cw = ⟨hutu.unit, rt, st, tt⟩ := ⟨_, rfl⟩
  have hCw_res : Cw.map res₀ = C₀ := by
    rw [hCw]
    refine WeierstrassCurve.VariableChange.ext ?_ ?_ ?_ ?_
    · exact Units.ext (by simp [WeierstrassCurve.VariableChange.map, hut])
    · simp [WeierstrassCurve.VariableChange.map, hrt]
    · simp [WeierstrassCurve.VariableChange.map, hst]
    · simp [WeierstrassCurve.VariableChange.map, htt]

  obtain ⟨Ct, hCt⟩ : ∃ Ct : WeierstrassCurve.VariableChange (PowerSeries W₀),
      Ct = Cw.map (PowerSeries.C : W₀ →+* PowerSeries W₀) := ⟨_, rfl⟩
  obtain ⟨E', hE'⟩ : ∃ E' : WeierstrassCurve (PowerSeries W₀), E' = Ct⁻¹ • 𝓔 := ⟨_, rfl⟩
  have hsmul : Ct • E' = 𝓔 := by rw [hE', smul_inv_smul]

  have hρC : ((res₀.comp (PowerSeries.constantCoeff : PowerSeries W₀ →+* W₀)).comp
      (PowerSeries.C : W₀ →+* PowerSeries W₀)) = res₀ := by
    ext w; simp
  have hCtρ : Ct.map (res₀.comp (PowerSeries.constantCoeff : PowerSeries W₀ →+* W₀)) = C₀ := by
    rw [hCt, WeierstrassCurve.VariableChange.map_map, hρC, hCw_res]
  have h1 : E'.map (res₀.comp (PowerSeries.constantCoeff : PowerSeries W₀ →+* W₀)) = E₀ := by
    have h2 := congrArg (fun E : WeierstrassCurve (PowerSeries W₀) =>
      E.map (res₀.comp (PowerSeries.constantCoeff : PowerSeries W₀ →+* W₀))) hsmul
    rw [← WeierstrassCurve.map_variableChange, hCtρ, h𝓔₀] at h2
    exact MulAction.injective C₀ h2

  have hE'Δ : IsUnit E'.Δ := by
    rw [hE']; exact WeierstrassCurve.isUnit_Δ_variableChange _ Ct⁻¹ h𝓔

  have hj' : E'.jOfUnit hE'Δ - algebraMap W₀ (PowerSeries W₀) a₀ = u₂ * PowerSeries.X ^ e := by
    have hj2 : E'.jOfUnit hE'Δ = 𝓔.jOfUnit h𝓔 := by
      have hΔ3 : IsUnit (Ct⁻¹ • 𝓔).Δ := by rw [← hE']; exact hE'Δ
      have := WeierstrassCurve.jOfUnit_variableChange _ Ct⁻¹ h𝓔 hΔ3
      rw [← this]
      congr 1
    rw [hj2]; exact hj

  haveI : CharP (PowerSeries k) q := charP_of_injective_algebraMap (algebraMap k (PowerSeries k)).injective q
  have hmapE : E'.map (PowerSeries.map res₀) = (Ct⁻¹.map (PowerSeries.map res₀)) • (𝓔.map (PowerSeries.map res₀)) := by
    rw [hE', WeierstrassCurve.map_variableChange]
  have hu : (((Ct⁻¹.map (PowerSeries.map res₀)).u⁻¹ : (PowerSeries k)ˣ) : PowerSeries k) =
      PowerSeries.C ((C₀.u : kˣ) : k) := by
    rw [hCt, hCw]
    simp [WeierstrassCurve.VariableChange.map, WeierstrassCurve.VariableChange.inv_def, PowerSeries.map_C, hut]
  have hH : (E'.map (PowerSeries.map res₀)).hasseInvariant q =
      PowerSeries.C (((C₀.u : kˣ) : k) ^ (q - 1)) * (𝓔.map (PowerSeries.map res₀)).hasseInvariant q := by
    rw [hmapE, WeierstrassCurve.hasseInvariant_variableChange, hu, map_pow]
  have hH0' : PowerSeries.coeff 0 ((E'.map (PowerSeries.map res₀)).hasseInvariant q) = 0 := by
    rw [hH, PowerSeries.coeff_C_mul, hH0, mul_zero]
  have hH1' : PowerSeries.coeff 1 ((E'.map (PowerSeries.map res₀)).hasseInvariant q) ≠ 0 := by
    rw [hH, PowerSeries.coeff_C_mul]
    exact mul_ne_zero (pow_ne_zero _ (C₀.u).ne_zero) hH1
  exact WeierstrassCurve.exists_powerSeries_lift_coeff_nthSeries_sub_mul_X_mem_span_and_jOfUnit_sub_eq_mul_X_pow_of_coeff_hasseInvariant_map
    q hq k E₀ W₀ hW₀ res₀ hres₀ hker₀ E' hE'Δ h1 hH0' hH1' a₀ e he u₂ hu₂ hj'

end S_WeierstrassCurve_exists_powerSeries_lift_coeff_nthSeries_sub_mul_X_mem_span_and_jOfUnit_sub_eq_mul_X_pow_of_coeff_hasseInvariant_map_variableChange
end P2MW
export P2MW.S_WeierstrassCurve_exists_powerSeries_lift_coeff_nthSeries_sub_mul_X_mem_span_and_jOfUnit_sub_eq_mul_X_pow_of_coeff_hasseInvariant_map_variableChange (solution)
