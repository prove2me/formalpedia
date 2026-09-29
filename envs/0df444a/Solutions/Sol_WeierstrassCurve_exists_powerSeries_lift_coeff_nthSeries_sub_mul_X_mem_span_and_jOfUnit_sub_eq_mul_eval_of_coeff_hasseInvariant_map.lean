-- Prove2me | solution 1 for WeierstrassCurve.exists_powerSeries_lift_coeff_nthSeries_sub_mul_X_mem_span_and_jOfUnit_sub_eq_mul_eval_of_coeff_hasseInvariant_map
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.822295+00:00
-- url     : https://prove2.me/submissions/770c5756-5176-578e-be8c-de3509b5ef7b

import Mathlib
import Definitions.Def_FormalGroup_NSeries
import Definitions.Def_FormalGroup_DrinfeldBasis
import Definitions.Def_FormalGroup_PointTransport
import Definitions.Def_WeierstrassCurve_FormalGroupLaw
import Definitions.Def_WeierstrassCurve_FormalGroup
import Definitions.Def_WeierstrassCurve_HasseInvariant
import Definitions.Def_ModularCurve_WeierstrassLevelCarrier
import Theorems.Thm_WeierstrassCurve_formalW_map_and_formalGroupLawFixed_map
import Theorems.Thm_FormalGroup_IsBaseChange_nthSeries_eq_map
import Theorems.Thm_WeierstrassCurve_exists_coeff_nthSeries_eq_mul_hasseInvariant
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_WeierstrassCurve_exists_powerSeries_lift_coeff_nthSeries_sub_mul_X_mem_span_and_jOfUnit_sub_eq_mul_eval_of_coeff_hasseInvariant_map
p2m_attr_erase "simp" "ModularCurve.qExpand_coeff_mul ModularCurve.qExpandₐ_apply ModularCurve.jqN_one ModularCurve.qExpand_single ModularCurve.dedekindPsi_one ModularCurve.ModularPolynomialData.mk.sizeOf_spec ModularCurve.evalAtJ_X ModularCurve.ModularPolynomialData.mk.injEq ModularCurve.constantCoeff_jNum ModularCurve.constantCoeff_eisenstein4 ModularCurve.qExpand_C ModularCurve.coeff_jq_neg_one ModularCurve.constantCoeff_jNumQ"

set_option autoImplicit false

open FormalGroup IsLocalRing

namespace WeierstrassCurve
p2m_export "WeierstrassCurve" "map_map map map_j mk reduction map_Δ Δ j formalGroupLawFixed formalGroup hasseInvariant jOfUnit jOfUnit_map formalW_map_and_formalGroupLawFixed_map exists_coeff_nthSeries_eq_mul_hasseInvariant"
namespace TemplateAAux
p2m_open "WeierstrassCurve"

open PowerSeries in

theorem mem_span_C_of_forall_coeff_mem {W₀ : Type*} [CommRing W₀] (π : W₀) (f : PowerSeries W₀)
    (h : ∀ n, PowerSeries.coeff n f ∈ Ideal.span {π}) :
    f ∈ Ideal.span {(PowerSeries.C π : PowerSeries W₀)} := by
  classical
  choose b hb using fun n => Ideal.mem_span_singleton'.mp (h n)
  refine Ideal.mem_span_singleton'.mpr ⟨PowerSeries.mk b, ?_⟩
  ext n
  rw [mul_comm, PowerSeries.coeff_C_mul, PowerSeries.coeff_mk, mul_comm]
  exact hb n

theorem charP_powerSeries (k : Type*) [CommRing k] (q : ℕ) [CharP k q] : CharP (PowerSeries k) q := by
  refine charP_of_injective_algebraMap (R := k) (A := PowerSeries k) (fun a b h => ?_) q
  have := congrArg PowerSeries.constantCoeff h
  simpa using this

theorem rescale_C {W₀ : Type*} [CommRing W₀] (μ a : W₀) :
    PowerSeries.rescale μ (PowerSeries.C a) = PowerSeries.C a := by
  ext n
  rw [PowerSeries.coeff_rescale, PowerSeries.coeff_C]
  split_ifs with h
  · rw [h, pow_zero, one_mul]
  · rw [mul_zero]

end WeierstrassCurve.TemplateAAux

open WeierstrassCurve.TemplateAAux

theorem solution
    (q : ℕ) [Fact q.Prime] (hq : q ≠ 2) (k : Type) [Field k] [CharP k q]
    (E₀ : WeierstrassCurve k) [E₀.IsElliptic]
    (W₀ : Type) [CommRing W₀] [IsDomain W₀] [IsDiscreteValuationRing W₀]
    [IsAdicComplete (maximalIdeal W₀) W₀] (hW₀ : maximalIdeal W₀ = Ideal.span {(q : W₀)})
    (res₀ : W₀ →+* k) (hres₀ : Function.Surjective res₀) (hker₀ : RingHom.ker res₀ = maximalIdeal W₀)
    (𝓔 : WeierstrassCurve (PowerSeries W₀)) (h𝓔 : IsUnit 𝓔.Δ)
    (h𝓔₀ : 𝓔.map (res₀.comp (PowerSeries.constantCoeff : PowerSeries W₀ →+* W₀)) = E₀)
    (hH0 : PowerSeries.coeff 0 ((𝓔.map (PowerSeries.map res₀)).hasseInvariant q) = 0)
    (hH1 : PowerSeries.coeff 1 ((𝓔.map (PowerSeries.map res₀)).hasseInvariant q) ≠ 0)
    (a₀ : W₀) (e : ℕ) (he : 1 ≤ e) (u₂ : PowerSeries W₀) (hu₂ : IsUnit u₂)
    (P : Polynomial W₀) (hPm : P.Monic) (hPd : P.natDegree = e)
    (hPc : ∀ i < e, P.coeff i ∈ maximalIdeal W₀ ^ ((e - i) * q / (q + 1) + 1))
    (hj : 𝓔.jOfUnit h𝓔 - algebraMap W₀ (PowerSeries W₀) a₀ = u₂ * (P.map (algebraMap W₀ (PowerSeries W₀))).eval PowerSeries.X) :
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

  set ρ : PowerSeries W₀ →+* k := res₀.comp (PowerSeries.constantCoeff : PowerSeries W₀ →+* W₀) with hρ
  set π : PowerSeries W₀ →+* PowerSeries k := PowerSeries.map res₀ with hπ
  have hqp : q.Prime := Fact.out
  haveI : CharP (PowerSeries k) q := charP_powerSeries k q

  haveI h𝓔ell : 𝓔.IsElliptic := ⟨h𝓔⟩
  set G : FormalGroup (PowerSeries W₀) := 𝓔.formalGroup with hG
  have hGlaw : G.toPowerSeries = 𝓔.formalGroupLawFixed := rfl
  set γ : PowerSeries W₀ := PowerSeries.coeff q (G.nthSeries q) with hγ

  obtain ⟨c, hc0, hc⟩ := WeierstrassCurve.exists_coeff_nthSeries_eq_mul_hasseInvariant q hq
  have hΔπ : IsUnit (𝓔.map π).Δ := by rw [WeierstrassCurve.map_Δ]; exact h𝓔.map π
  have hGπ : (G.map π).toPowerSeries = (𝓔.map π).formalGroupLawFixed := by
    rw [FormalGroup.map_toPowerSeries, (WeierstrassCurve.formalW_map_and_formalGroupLawFixed_map 𝓔 π).2, hGlaw]
  have hγπ : π γ = (c : PowerSeries k) * (𝓔.map π).hasseInvariant q := by
    rw [hγ, ← PowerSeries.coeff_map, ← FormalGroup.IsBaseChange.nthSeries_eq_map G π (G.map π) rfl q]
    exact hc (PowerSeries k) (𝓔.map π) hΔπ (G.map π) hGπ

  set Hbar := (𝓔.map π).hasseInvariant q with hHbar
  set v : PowerSeries k := PowerSeries.mk fun n => PowerSeries.coeff (n + 1) Hbar with hv
  have hHv : Hbar = PowerSeries.X * v := by
    have e := PowerSeries.eq_X_mul_shift_add_const Hbar
    rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, hH0, map_zero, _root_.add_zero] at e
    exact e
  have hv0 : PowerSeries.constantCoeff v ≠ 0 := by
    rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, hv, PowerSeries.coeff_mk, _root_.zero_add]; exact hH1
  have hck : ((c : ℤ) : k) ≠ 0 := by
    intro h
    apply hc0
    rw [ZMod.intCast_zmod_eq_zero_iff_dvd]
    exact (CharP.intCast_eq_zero_iff k q c).mp h

  obtain ⟨u₁', hu₁'⟩ := PowerSeries.map_surjective res₀ hres₀ (PowerSeries.C ((c : ℤ) : k) * v)
  have hu₁'unit : IsUnit u₁' := by
    rw [PowerSeries.isUnit_iff_constantCoeff]
    by_contra hnu
    have hmem : PowerSeries.constantCoeff u₁' ∈ RingHom.ker res₀ := by
      rw [hker₀]; exact (IsLocalRing.mem_maximalIdeal _).mpr hnu
    rw [RingHom.mem_ker] at hmem
    have := congrArg PowerSeries.constantCoeff hu₁'
    rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_map,
      PowerSeries.coeff_zero_eq_constantCoeff_apply, hmem, map_mul, PowerSeries.constantCoeff_C] at this
    exact mul_ne_zero hck hv0 this.symm

  have hδ : γ - u₁' * PowerSeries.X ∈ Ideal.span {((q : ℕ) : PowerSeries W₀)} := by
    rw [show ((q : ℕ) : PowerSeries W₀) = PowerSeries.C ((q : ℕ) : W₀) by rw [map_natCast]]
    have hπδ : π (γ - u₁' * PowerSeries.X) = 0 := by
      rw [map_sub, map_mul, hγπ, hHv, hπ, hu₁', PowerSeries.map_X, ← map_intCast (PowerSeries.C (R := k)) c]
      ring
    apply mem_span_C_of_forall_coeff_mem
    intro n
    rw [← hW₀, ← hker₀, RingHom.mem_ker, ← PowerSeries.coeff_map]
    show PowerSeries.coeff n (π (γ - u₁' * PowerSeries.X)) = 0
    rw [hπδ, map_zero]

  have hκ : IsUnit (PowerSeries.coeff 1 γ) := by
    have h1 : PowerSeries.coeff 1 (γ - u₁' * PowerSeries.X) ∈ maximalIdeal W₀ := by
      have := hδ
      rw [show ((q : ℕ) : PowerSeries W₀) = PowerSeries.C ((q : ℕ) : W₀) by rw [map_natCast]] at this
      obtain ⟨b, hb⟩ := Ideal.mem_span_singleton'.mp this
      rw [← hb, mul_comm, PowerSeries.coeff_C_mul, hW₀]
      exact Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _)
    rw [map_sub, PowerSeries.coeff_succ_mul_X, PowerSeries.coeff_zero_eq_constantCoeff_apply] at h1
    by_contra hnu
    have h2 : PowerSeries.coeff 1 γ ∈ maximalIdeal W₀ := (IsLocalRing.mem_maximalIdeal _).mpr hnu
    have h3 : PowerSeries.constantCoeff u₁' ∈ maximalIdeal W₀ := by
      have := Ideal.sub_mem _ h2 h1; rwa [sub_sub_cancel] at this
    exact (IsLocalRing.mem_maximalIdeal _).mp h3 (PowerSeries.isUnit_iff_constantCoeff.mp hu₁'unit)

  obtain ⟨κU, hκU⟩ := hκ
  set μ : W₀ := ↑κU⁻¹ with hμ
  set σ : PowerSeries W₀ →+* PowerSeries W₀ := PowerSeries.rescale μ with hσ
  have hρσ : ρ.comp σ = ρ := by
    refine RingHom.ext fun f => ?_
    show res₀ (PowerSeries.constantCoeff (PowerSeries.rescale μ f)) = res₀ (PowerSeries.constantCoeff f)
    rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_rescale, pow_zero, one_mul,
      PowerSeries.coeff_zero_eq_constantCoeff_apply]
  set 𝓔' := 𝓔.map σ with h𝓔'
  have hΔ' : IsUnit 𝓔'.Δ := by rw [h𝓔', WeierstrassCurve.map_Δ]; exact h𝓔.map σ
  have h𝓔'₀ : 𝓔'.map ρ = E₀ := by rw [h𝓔', WeierstrassCurve.map_map, hρσ]; exact h𝓔₀
  haveI h𝓔'ell : 𝓔'.IsElliptic := ⟨hΔ'⟩

  have hlaw' : 𝓔'.formalGroup.toPowerSeries = MvPowerSeries.map σ G.toPowerSeries := by
    show 𝓔'.formalGroupLawFixed = MvPowerSeries.map σ 𝓔.formalGroupLawFixed
    rw [h𝓔']; exact (WeierstrassCurve.formalW_map_and_formalGroupLawFixed_map 𝓔 σ).2
  have hbc' : 𝓔'.formalGroup.IsBaseChange ρ E₀.formalGroup := by
    show E₀.formalGroup.toPowerSeries = MvPowerSeries.map ρ 𝓔'.formalGroup.toPowerSeries
    show E₀.formalGroupLawFixed = MvPowerSeries.map ρ 𝓔'.formalGroupLawFixed
    rw [← (WeierstrassCurve.formalW_map_and_formalGroupLawFixed_map 𝓔' ρ).2, h𝓔'₀]
  have hγ' : PowerSeries.coeff q (𝓔'.formalGroup.nthSeries q) = σ γ := by
    rw [FormalGroup.IsBaseChange.nthSeries_eq_map G σ 𝓔'.formalGroup hlaw' q, PowerSeries.coeff_map]
  have hμκ : μ * PowerSeries.coeff 1 γ = 1 := by rw [hμ, ← hκU, Units.inv_mul]
  refine ⟨𝓔', hΔ', h𝓔'₀, 𝓔'.formalGroup, inferInstance, rfl, hbc', ?_, σ u₁' * PowerSeries.C μ,
    (hu₁'unit.map σ).mul ?_, ?_, a₀, e, he, σ u₂ * PowerSeries.C (μ ^ e), (hu₂.map σ).mul ?_,
    P.scaleRoots (↑κU : W₀), (Polynomial.monic_scaleRoots_iff _).mpr hPm,
    (by rw [Polynomial.natDegree_scaleRoots, hPd]), ?_, ?_⟩
  ·
    rw [hγ', hσ, PowerSeries.coeff_rescale, pow_one, hμκ, sub_self]
    exact zero_mem _
  · rw [PowerSeries.isUnit_iff_constantCoeff, PowerSeries.constantCoeff_C, hμ]; exact Units.isUnit _
  ·
    have := Ideal.mem_map_of_mem σ hδ
    rw [Ideal.map_span, Set.image_singleton, map_natCast, map_sub, map_mul] at this
    rw [hγ']
    convert this using 2
    rw [hσ, PowerSeries.rescale_X]; ring
  · rw [PowerSeries.isUnit_iff_constantCoeff, PowerSeries.constantCoeff_C, hμ, ← Units.val_pow_eq_pow_val]
    exact Units.isUnit _
  ·
    intro i hi
    rw [Polynomial.coeff_scaleRoots, hPd]
    exact Ideal.mul_mem_right _ _ (hPc i hi)
  ·
    rw [WeierstrassCurve.jOfUnit_map 𝓔 σ h𝓔 hΔ']
    have hσC : ∀ w : W₀, σ (algebraMap W₀ (PowerSeries W₀) w) = algebraMap W₀ (PowerSeries W₀) w := by
      intro w; rw [← PowerSeries.C_eq_algebraMap, hσ, rescale_C]
    have hσalg : σ.comp (algebraMap W₀ (PowerSeries W₀)) = algebraMap W₀ (PowerSeries W₀) := RingHom.ext hσC
    have hkey : Polynomial.eval₂ (algebraMap W₀ (PowerSeries W₀)) (PowerSeries.C μ * PowerSeries.X) P =
        PowerSeries.C (μ ^ e) *
          Polynomial.eval₂ (algebraMap W₀ (PowerSeries W₀)) PowerSeries.X (P.scaleRoots (↑κU : W₀)) := by
      have h1 := Polynomial.scaleRoots_eval₂_mul (p := P) (algebraMap W₀ (PowerSeries W₀))
        (PowerSeries.C μ * PowerSeries.X) (↑κU : W₀)
      have hκμ : algebraMap W₀ (PowerSeries W₀) (↑κU : W₀) * (PowerSeries.C μ * PowerSeries.X) = PowerSeries.X := by
        rw [← PowerSeries.C_eq_algebraMap, ← mul_assoc, ← map_mul, hμ, Units.mul_inv, map_one, one_mul]
      rw [hκμ, hPd] at h1
      rw [h1, ← mul_assoc, ← PowerSeries.C_eq_algebraMap, ← map_pow, ← map_mul, ← mul_pow, hμ,
        Units.inv_mul, one_pow, map_one, one_mul]
    rw [← hσC a₀, ← map_sub, hj, map_mul, Polynomial.eval_map, Polynomial.hom_eval₂, hσalg, hσ,
      PowerSeries.rescale_X, hkey, Polynomial.eval_map]
    ring

end S_WeierstrassCurve_exists_powerSeries_lift_coeff_nthSeries_sub_mul_X_mem_span_and_jOfUnit_sub_eq_mul_eval_of_coeff_hasseInvariant_map
end P2MW
export P2MW.S_WeierstrassCurve_exists_powerSeries_lift_coeff_nthSeries_sub_mul_X_mem_span_and_jOfUnit_sub_eq_mul_eval_of_coeff_hasseInvariant_map (solution)
