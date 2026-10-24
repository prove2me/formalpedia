-- Prove2me | solution 1 for StochasticOrders.Multivariate.multivariate_order_common_source_iff_v2
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-23T21:09:36.882959+00:00
-- url     : https://prove2.me/submissions/21c5f624-2356-425c-9c25-b11962fd1743

import Mathlib
import Definitions.Def_StochasticOrders_Multivariate_MultivariateOrder_v2
import Theorems.Thm_StochasticOrders_Multivariate_multivariate_order_coupling_iff_v2
open MeasureTheory ProbabilityTheory
namespace CPL97CS

lemma forward {n : ℕ} {Ω'' : Type} [MeasurableSpace Ω''] (ρ : Measure Ω'')
    (Xh Yh : Ω'' → Fin n → ℝ) (hXh : Measurable Xh) (hYh : Measurable Yh)
    (hle : ρ {ω | Xh ω ≤ Yh ω} = 1) [IsProbabilityMeasure ρ] :
    ∃ (Z : Ω'' → ℝ) (ψ1 ψ2 : ℝ → Fin n → ℝ),
      Measurable Z ∧ Measurable ψ1 ∧ Measurable ψ2 ∧ (∀ z : ℝ, ψ1 z ≤ ψ2 z) ∧
      ψ1 ∘ Z =ᵐ[ρ] Xh ∧ ψ2 ∘ Z =ᵐ[ρ] Yh := by
  classical
  obtain ⟨f, hf⟩ := MeasureTheory.exists_measurableEmbedding_real
    (α := (Fin n → ℝ) × (Fin n → ℝ))
  set g : ℝ → (Fin n → ℝ) × (Fin n → ℝ) :=
    Function.extend f id (fun _ => ((0 : Fin n → ℝ), (0 : Fin n → ℝ))) with hgdef
  have hg : Measurable g := hf.measurable_extend measurable_id measurable_const
  have hgf : ∀ p, g (f p) = p := fun p => by
    rw [hgdef, hf.injective.extend_apply]; rfl
  have hS : MeasurableSet {z | (g z).1 ≤ (g z).2} :=
    measurableSet_le hg.fst hg.snd
  refine ⟨fun ω => f (Xh ω, Yh ω),
    fun z => if (g z).1 ≤ (g z).2 then (g z).1 else 0,
    fun z => if (g z).1 ≤ (g z).2 then (g z).2 else 0,
    hf.measurable.comp (hXh.prodMk hYh),
    Measurable.ite hS hg.fst measurable_const,
    Measurable.ite hS hg.snd measurable_const, ?_, ?_, ?_⟩
  · intro z
    by_cases h : (g z).1 ≤ (g z).2
    · simp [h]
    · simp [h]
  · have hae : ∀ᵐ ω ∂ρ, Xh ω ≤ Yh ω := by
      rw [ae_iff]
      have h1 := prob_compl_eq_zero_iff (μ := ρ)
        (measurableSet_le hXh hYh) |>.mpr hle
      simpa [Set.compl_def] using h1
    filter_upwards [hae] with ω hω
    show (if _ then _ else _) = _
    simp only [hgf, if_pos hω]
  · have hae : ∀ᵐ ω ∂ρ, Xh ω ≤ Yh ω := by
      rw [ae_iff]
      have h1 := prob_compl_eq_zero_iff (μ := ρ)
        (measurableSet_le hXh hYh) |>.mpr hle
      simpa [Set.compl_def] using h1
    filter_upwards [hae] with ω hω
    show (if _ then _ else _) = _
    simp only [hgf, if_pos hω]

end CPL97CS

open StochasticOrders.Multivariate in
theorem solution {Ω Ω' : Type*} [MeasurableSpace Ω]
    [MeasurableSpace Ω'] {n : ℕ} (μ : Measure Ω) (ν : Measure Ω')
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (X : Ω → Fin n → ℝ) (Y : Ω' → Fin n → ℝ) (hX : Measurable X) (hY : Measurable Y) :
    MultivariateOrder μ ν X Y ↔
      ∃ (Ω'' : Type) (_ : MeasurableSpace Ω'') (ρ : Measure Ω'') (_ : IsProbabilityMeasure ρ)
        (Z : Ω'' → ℝ) (ψ1 ψ2 : ℝ → Fin n → ℝ),
        Measurable Z ∧ Measurable ψ1 ∧ Measurable ψ2 ∧
        (∀ z : ℝ, ψ1 z ≤ ψ2 z) ∧
        IdentDistrib (ψ1 ∘ Z) X ρ μ ∧ IdentDistrib (ψ2 ∘ Z) Y ρ ν := by
  rw [multivariate_order_coupling_iff_v2 μ ν X Y hX hY]
  constructor
  · rintro ⟨Ω'', _, ρ, _, Xh, Yh, hXh, hYh, hiX, hiY, hle⟩
    obtain ⟨Z, ψ1, ψ2, hZ, h1, h2, hψ, e1, e2⟩ := CPL97CS.forward ρ Xh Yh hXh hYh hle
    exact ⟨Ω'', _, ρ, inferInstance, Z, ψ1, ψ2, hZ, h1, h2, hψ,
      (IdentDistrib.of_ae_eq (h1.comp hZ).aemeasurable e1).trans hiX,
      (IdentDistrib.of_ae_eq (h2.comp hZ).aemeasurable e2).trans hiY⟩
  · rintro ⟨Ω'', _, ρ, _, Z, ψ1, ψ2, hZ, h1, h2, hψ, hi1, hi2⟩
    refine ⟨Ω'', _, ρ, inferInstance, ψ1 ∘ Z, ψ2 ∘ Z, h1.comp hZ, h2.comp hZ, hi1, hi2, ?_⟩
    have : {ω | (ψ1 ∘ Z) ω ≤ (ψ2 ∘ Z) ω} = Set.univ := by
      ext ω; simp [hψ (Z ω)]
    rw [this, measure_univ]
