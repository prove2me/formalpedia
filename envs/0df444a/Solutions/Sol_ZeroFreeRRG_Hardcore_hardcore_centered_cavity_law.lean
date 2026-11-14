-- Prove2me | solution 1 for ZeroFreeRRG.Hardcore.hardcore_centered_cavity_law
-- status  : ACCEPTED   (prove)
-- author  : @wcysai
-- created : 2026-11-13T08:17:24.537889+00:00
-- url     : https://prove2.me/submissions/b75f1197-3d0d-44d2-a07f-74369aa72331

import Definitions.Def_ZeroFreeRRG_Hardcore_BetheFunctional
import Mathlib
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open MeasureTheory Set ZeroFreeRRG.Hardcore
open scoped Classical

theorem solution (α : ℝ) (ha : 0 < α) (ha1 : α < 1/2)
    (ν : ProbabilityMeasure (Fin 2 → ℝ)) (hν : ν ∈ cavityLaws .hardcore α)
    (hne : ν ≠ diracPi .hardcore α) :
    let η := Measure.map (fun x : Fin 2 → ℝ => (x 1-α)/(1-α)) (ν : Measure (Fin 2 → ℝ))
    IsProbabilityMeasure η ∧ (∀ᵐ h ∂η, -1 ≤ h ∧ h ≤ 1) ∧
      Integrable (fun h : ℝ => h) η ∧ (∫ h : ℝ, h ∂η) = 0 ∧
      ¬(∀ᵐ h ∂η, h=0) := by
  dsimp only
  let C := fun x : Fin 2 → ℝ => (x 1-α)/(1-α)
  let η := Measure.map C (ν : Measure (Fin 2 → ℝ))
  have hc : Continuous C := by dsimp [C]; fun_prop
  have hνae : ∀ᵐ x ∂(ν : Measure (Fin 2 → ℝ)), x ∈ stdSimplex ℝ (Fin 2) := by
    apply ae_iff.mpr
    exact hν.1
  have hden : 0 < 1-α := by linarith
  have hbound : ∀ᵐ x ∂(ν : Measure (Fin 2 → ℝ)), -1 ≤ C x ∧ C x ≤ 1 := by
    filter_upwards [hνae] with x hx
    have hh := mem_Icc_of_mem_stdSimplex hx (1 : Fin 2)
    dsimp [C]
    constructor
    · apply (le_div_iff₀ hden).2
      nlinarith [hh.1]
    · apply (div_le_iff₀ hden).2
      nlinarith [hh.2]
  letI : IsProbabilityMeasure η := Measure.isProbabilityMeasure_map hc.measurable.aemeasurable
  have hboundη : ∀ᵐ h ∂η, -1 ≤ h ∧ h ≤ 1 := by
    apply (ae_map_iff hc.measurable.aemeasurable
      ((measurableSet_le measurable_const measurable_id).inter (measurableSet_le measurable_id measurable_const))).2
    exact hbound
  have hηint : Integrable (fun h : ℝ => h) η := by
    apply Integrable.of_bound measurable_id.aestronglyMeasurable 1
    filter_upwards [hboundη] with h hh
    change ‖h‖ ≤ 1
    rw [Real.norm_eq_abs, abs_le]
    exact hh
  have hxint : Integrable (fun x : Fin 2 → ℝ => x 1) (ν : Measure (Fin 2 → ℝ)) := by
    apply Integrable.of_bound (continuous_apply (1 : Fin 2)).aestronglyMeasurable 1
    filter_upwards [hνae] with x hx
    have hh := mem_Icc_of_mem_stdSimplex hx (1 : Fin 2)
    simpa [Real.norm_eq_abs,abs_of_nonneg hh.1] using hh.2
  have hpi : Model.pi .hardcore α (1 : Fin 2) = α := by
    simp [Model.pi, Model.Spin, Model.P, Fin.sum_univ_two] <;> ring
  have hmean1 : (∫ x : Fin 2 → ℝ, x 1 ∂(ν : Measure (Fin 2 → ℝ))) = α := by
    have h := hν.2 (show Model.hardcore.Spin from (1 : Fin 2))
    change (∫ x : Fin 2 → ℝ, x 1 ∂(ν : Measure (Fin 2 → ℝ))) = Model.pi .hardcore α (1 : Fin 2) at h
    rw [h,hpi]
  have hηmean : (∫ h : ℝ, h ∂η) = 0 := by
    change (∫ h, id h ∂Measure.map C (ν : Measure (Fin 2 → ℝ))) = 0
    rw [integral_map hc.measurable.aemeasurable measurable_id.aestronglyMeasurable]
    dsimp only [Function.comp_def,id_eq,C]
    rw [integral_div,integral_sub hxint (integrable_const α),hmean1]
    simp
  have hnot : ¬(∀ᵐ h ∂η, h=0) := by
    intro hz
    apply hne
    have hz' : ∀ᵐ x ∂(ν : Measure (Fin 2 → ℝ)), C x=0 :=
      (ae_map_iff hc.measurable.aemeasurable (measurableSet_singleton (0:ℝ))).1 hz
    have hxeq : ∀ᵐ x : Fin 2 → ℝ ∂(ν : Measure (Fin 2 → ℝ)), x = (Model.pi .hardcore α : Fin 2 → ℝ) := by
      filter_upwards [hνae,hz'] with x hx hz''
      have hx1 : x 1 = α := by
        dsimp [C] at hz''
        have := (div_eq_zero_iff).1 hz''
        rcases this with hh | hh
        · linarith
        · exact (hden.ne' hh).elim
      have hsum : x 0 + x 1 = 1 := by simpa [Fin.sum_univ_two] using hx.2
      funext i
      fin_cases i <;> simp [Model.pi,Model.Spin,Model.P,Fin.sum_univ_two,hx1] <;> linarith
    apply ProbabilityMeasure.toMeasure_injective
    change (ν : Measure (Fin 2 → ℝ)) = Measure.dirac (Model.pi .hardcore α)
    calc
      _ = Measure.map id (ν : Measure (Fin 2 → ℝ)) := (Measure.map_id).symm
      _ = Measure.map (fun _ => Model.pi .hardcore α) (ν : Measure (Fin 2 → ℝ)) := Measure.map_congr hxeq
      _ = _ := by rw [Measure.map_const]; simp
  exact ⟨inferInstance,hboundη,hηint,hηmean,hnot⟩
