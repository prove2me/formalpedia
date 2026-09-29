-- Prove2me | solution 1 for WeierstrassCurve.exists_isComm_lift_powerSeries_formalGroup_coeff_nthSeries_of_ne_two
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.822295+00:00
-- url     : https://prove2.me/submissions/5ad197a9-2b5c-596a-8b3e-61f0e4ba6298

import Mathlib
import Definitions.Def_FormalGroup_NSeries
import Definitions.Def_FormalGroup_DrinfeldBasis
import Definitions.Def_FormalGroup_PointTransport
import Definitions.Def_WeierstrassCurve_FormalGroupLaw
import Definitions.Def_WeierstrassCurve_FormalGroup
import Theorems.Thm_WeierstrassCurve_formalW_map_and_formalGroupLawFixed_map
import Theorems.Thm_FormalGroup_IsBaseChange_nthSeries_eq_map
import Theorems.Thm_WeierstrassCurve_exists_map_fstHom_eq_and_snd_coeff_nthSeries_ne_zero_of_ne_two
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_WeierstrassCurve_exists_isComm_lift_powerSeries_formalGroup_coeff_nthSeries_of_ne_two
p2m_attr_erase "simp" "ModularCurve.qExpand_coeff_mul ModularCurve.qExpandₐ_apply ModularCurve.jqN_one ModularCurve.qExpand_single ModularCurve.dedekindPsi_one ModularCurve.ModularPolynomialData.mk.sizeOf_spec ModularCurve.evalAtJ_X ModularCurve.ModularPolynomialData.mk.injEq ModularCurve.constantCoeff_jNum ModularCurve.constantCoeff_eisenstein4 ModularCurve.qExpand_C ModularCurve.coeff_jq_neg_one ModularCurve.constantCoeff_jNumQ"

set_option autoImplicit false

open FormalGroup IsLocalRing

namespace DW2ELL

noncomputable def trunc {W₀ k : Type*} [CommRing W₀] [CommRing k] (res₀ : W₀ →+* k) :
    PowerSeries W₀ →+* DualNumber k where
  toFun f := TrivSqZeroExt.inl (res₀ (PowerSeries.coeff 0 f)) + TrivSqZeroExt.inr (res₀ (PowerSeries.coeff 1 f))
  map_one' := by
    apply TrivSqZeroExt.ext <;> simp [PowerSeries.coeff_one]
  map_mul' f g := by
    have c1 : PowerSeries.coeff 1 (f * g) =
        PowerSeries.coeff 0 f * PowerSeries.coeff 1 g + PowerSeries.coeff 1 f * PowerSeries.coeff 0 g := by
      rw [PowerSeries.coeff_mul, Finset.Nat.sum_antidiagonal_succ, Finset.Nat.antidiagonal_zero, Finset.sum_singleton]
    apply TrivSqZeroExt.ext
    · simp [PowerSeries.coeff_zero_eq_constantCoeff, TrivSqZeroExt.fst_mul]
    · simp only [TrivSqZeroExt.snd_add, TrivSqZeroExt.snd_inl, TrivSqZeroExt.snd_inr, _root_.zero_add, DualNumber.snd_mul,
        TrivSqZeroExt.fst_add, TrivSqZeroExt.fst_inl, TrivSqZeroExt.fst_inr, _root_.add_zero, c1, map_add, map_mul]
  map_zero' := by apply TrivSqZeroExt.ext <;> simp
  map_add' f g := by
    apply TrivSqZeroExt.ext <;> simp

theorem trunc_apply_fst {W₀ k : Type*} [CommRing W₀] [CommRing k] (res₀ : W₀ →+* k) (f : PowerSeries W₀) :
    TrivSqZeroExt.fst (trunc res₀ f) = res₀ (PowerSeries.coeff 0 f) := by
  simp [trunc]

theorem trunc_apply_snd {W₀ k : Type*} [CommRing W₀] [CommRing k] (res₀ : W₀ →+* k) (f : PowerSeries W₀) :
    TrivSqZeroExt.snd (trunc res₀ f) = res₀ (PowerSeries.coeff 1 f) := by
  simp [trunc]

end DW2ELL

set_option maxHeartbeats 6400000 in
theorem solution
    (q : ℕ) [Fact q.Prime] (hq : q ≠ 2) (k : Type) [Field k] [CharP k q]
    (E₀ : WeierstrassCurve k) [E₀.IsElliptic] (hE₀ : E₀.formalGroup.IsDrinfeldBasisAdic ⊥ q 0 0)
    (W₀ : Type) [CommRing W₀] [IsDomain W₀] [IsDiscreteValuationRing W₀]
    [IsAdicComplete (maximalIdeal W₀) W₀] (hW₀ : maximalIdeal W₀ = Ideal.span {(q : W₀)})
    (res₀ : W₀ →+* k) (hres₀ : Function.Surjective res₀) (hker₀ : RingHom.ker res₀ = maximalIdeal W₀) :
    ∃ (Fu : FormalGroup (PowerSeries W₀)) (_ : Fu.IsComm)
      (_ : Fu.IsBaseChange (res₀.comp (PowerSeries.constantCoeff : PowerSeries W₀ →+* W₀)) E₀.formalGroup),
      PowerSeries.coeff 1 (PowerSeries.coeff q (Fu.nthSeries q)) - 1 ∈ maximalIdeal W₀ := by
  classical
  set ρ : PowerSeries W₀ →+* k := res₀.comp (PowerSeries.constantCoeff : PowerSeries W₀ →+* W₀) with hρ

  obtain ⟨E₁, hE₁, hHD⟩ :=
    WeierstrassCurve.exists_map_fstHom_eq_and_snd_coeff_nthSeries_ne_zero_of_ne_two q hq k E₀ hE₀

  have lift : ∀ a : DualNumber k, ∃ f : PowerSeries W₀, ρ f = TrivSqZeroExt.fst a ∧ DW2ELL.trunc res₀ f = a := by
    intro a
    obtain ⟨b, hb⟩ := hres₀ (TrivSqZeroExt.fst a)
    obtain ⟨d, hd⟩ := hres₀ (TrivSqZeroExt.snd a)
    refine ⟨PowerSeries.C b + PowerSeries.C d * PowerSeries.X, ?_, ?_⟩
    · simp [hρ, hb]
    · apply TrivSqZeroExt.ext
      · rw [DW2ELL.trunc_apply_fst]; simp [hb]
      · rw [DW2ELL.trunc_apply_snd]; simp [PowerSeries.coeff_C, hd]
  choose L hLρ hLπ using lift
  let E : WeierstrassCurve (PowerSeries W₀) := ⟨L E₁.a₁, L E₁.a₂, L E₁.a₃, L E₁.a₄, L E₁.a₆⟩
  have hfst : ∀ {a : DualNumber k} {b : k}, (TrivSqZeroExt.fstHom k k k).toRingHom a = b → TrivSqZeroExt.fst a = b :=
    fun h => h
  have hEρ : E.map ρ = E₀ := by
    have h1 := congrArg WeierstrassCurve.a₁ hE₁
    have h2 := congrArg WeierstrassCurve.a₂ hE₁
    have h3 := congrArg WeierstrassCurve.a₃ hE₁
    have h4 := congrArg WeierstrassCurve.a₄ hE₁
    have h6 := congrArg WeierstrassCurve.a₆ hE₁
    simp only [WeierstrassCurve.map] at h1 h2 h3 h4 h6
    ext <;> simp only [E, WeierstrassCurve.map, hLρ] <;> first
      | exact hfst h1 | exact hfst h2 | exact hfst h3 | exact hfst h4 | exact hfst h6
  have hEπ : E.map (DW2ELL.trunc res₀) = E₁ := by
    ext <;> simp only [E, WeierstrassCurve.map, hLπ]

  have hΔ : IsUnit E.Δ := by
    rw [PowerSeries.isUnit_iff_constantCoeff]
    have h1 : res₀ (PowerSeries.constantCoeff E.Δ) = E₀.Δ := by
      rw [← hEρ, WeierstrassCurve.map_Δ]; rfl
    by_contra hu
    have hm : PowerSeries.constantCoeff E.Δ ∈ maximalIdeal W₀ :=
      (IsLocalRing.mem_maximalIdeal _).mpr (mem_nonunits_iff.mpr hu)
    rw [← hker₀, RingHom.mem_ker, h1] at hm
    exact E₀.isUnit_Δ.ne_zero hm
  haveI hEll : E.IsElliptic := ⟨hΔ⟩

  set u : W₀ := PowerSeries.coeff 1 (PowerSeries.coeff q (E.formalGroup.nthSeries q)) with hu
  have hGπ : E.formalGroup.IsBaseChange (DW2ELL.trunc res₀) (E.formalGroup.map (DW2ELL.trunc res₀)) := rfl
  have hlaw : (E.formalGroup.map (DW2ELL.trunc res₀)).toPowerSeries = E₁.formalGroupLawFixed := by
    rw [← hEπ, (E.formalW_map_and_formalGroupLawFixed_map (DW2ELL.trunc res₀)).2]
    rfl
  have hsnd := hHD (E.formalGroup.map (DW2ELL.trunc res₀)) hlaw
  rw [FormalGroup.IsBaseChange.nthSeries_eq_map E.formalGroup (DW2ELL.trunc res₀) _ hGπ q,
    PowerSeries.coeff_map, DW2ELL.trunc_apply_snd] at hsnd

  have hunit : IsUnit u := by
    by_contra h
    have hm : u ∈ maximalIdeal W₀ := (IsLocalRing.mem_maximalIdeal _).mpr (mem_nonunits_iff.mpr h)
    rw [← hker₀, RingHom.mem_ker] at hm
    exact hsnd hm

  set σ : PowerSeries W₀ →+* PowerSeries W₀ := PowerSeries.rescale ((hunit.unit⁻¹ : W₀ˣ) : W₀) with hσ
  have hρσ : ρ.comp σ = ρ := by
    refine RingHom.ext fun f => ?_
    show res₀ (PowerSeries.constantCoeff (σ f)) = res₀ (PowerSeries.constantCoeff f)
    rw [hσ, ← PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_rescale, pow_zero, one_mul,
      PowerSeries.coeff_zero_eq_constantCoeff_apply]
  let E' : WeierstrassCurve (PowerSeries W₀) := E.map σ
  haveI : E'.IsElliptic := inferInstance
  have hE'ρ : E'.map ρ = E₀ := by
    rw [show E'.map ρ = E.map (ρ.comp σ) from (E.map_map σ ρ), hρσ, hEρ]
  refine ⟨E'.formalGroup, inferInstance, ?_, ?_⟩
  ·
    show E₀.formalGroupLawFixed = MvPowerSeries.map ρ E'.formalGroupLawFixed
    rw [← (E'.formalW_map_and_formalGroupLawFixed_map ρ).2, hE'ρ]
  ·
    have hbc : E.formalGroup.IsBaseChange σ E'.formalGroup := by
      show E'.formalGroupLawFixed = MvPowerSeries.map σ E.formalGroupLawFixed
      exact (E.formalW_map_and_formalGroupLawFixed_map σ).2
    rw [FormalGroup.IsBaseChange.nthSeries_eq_map E.formalGroup σ E'.formalGroup hbc q, PowerSeries.coeff_map,
      hσ, PowerSeries.coeff_rescale, ← hu, pow_one, IsUnit.val_inv_mul, sub_self]
    exact Submodule.zero_mem _

end S_WeierstrassCurve_exists_isComm_lift_powerSeries_formalGroup_coeff_nthSeries_of_ne_two
end P2MW
export P2MW.S_WeierstrassCurve_exists_isComm_lift_powerSeries_formalGroup_coeff_nthSeries_of_ne_two (solution)
