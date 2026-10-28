-- Prove2me | solution 1 for OTSensitivity.Info.eq_68
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-24T16:56:53.92961+00:00
-- url     : https://prove2.me/submissions/5893faf7-f751-45a5-a717-463b592af3c1

import Mathlib
import Definitions.Def_OTSensitivity_Info_Setting

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal BoundedContinuousFunction

namespace OTGen

theorem compProd_eq {α β : Type*} [mα : MeasurableSpace α] [mβ : MeasurableSpace β]
    (μ : Measure α) [IsFiniteMeasure μ] (g : α → β) (hg : Measurable g)
    (η : Kernel β α) [IsMarkovKernel η]
    (hη : ∀ A, MeasurableSet A → ∀ B, MeasurableSet B →
      ∫⁻ u in A, η u B ∂(μ.map g) = μ (g ⁻¹' A ∩ B)) :
    (μ.map g) ⊗ₘ η = μ.map (fun x => (g x, x)) := by
  have hgx : Measurable (fun x => (g x, x)) := hg.prodMk measurable_id
  have hrect : ∀ A, MeasurableSet A → ∀ B, MeasurableSet B →
      ((μ.map g) ⊗ₘ η) (A ×ˢ B) = (μ.map (fun x => (g x, x))) (A ×ˢ B) := by
    intro A hA B hB
    rw [Measure.compProd_apply_prod hA hB, hη A hA B hB, Measure.map_apply hgx (hA.prod hB)]
    rfl
  refine ext_of_generate_finite _ generateFrom_prod.symm isPiSystem_prod ?_ ?_
  · rintro _ ⟨A, hA, B, hB, rfl⟩
    exact hrect A hA B hB
  · rw [← Set.univ_prod_univ]
    exact hrect _ MeasurableSet.univ _ MeasurableSet.univ

theorem setLIntegral_disint {α β : Type*} [mα : MeasurableSpace α] [mβ : MeasurableSpace β]
    (μ : Measure α) [IsFiniteMeasure μ] (g : α → β) (hg : Measurable g)
    (η : Kernel β α) [IsMarkovKernel η]
    (hη : ∀ A, MeasurableSet A → ∀ B, MeasurableSet B →
      ∫⁻ u in A, η u B ∂(μ.map g) = μ (g ⁻¹' A ∩ B))
    (A : Set β) (hA : MeasurableSet A) (f : α → ℝ≥0∞) (hf : Measurable f) :
    ∫⁻ u in A, ∫⁻ x, f x ∂(η u) ∂(μ.map g) = ∫⁻ x in g ⁻¹' A, f x ∂μ := by
  have hcp := compProd_eq μ g hg η hη
  have hgx : Measurable (fun x => (g x, x)) := hg.prodMk measurable_id
  let h : β × α → ℝ≥0∞ := fun p => A.indicator (fun _ => (1 : ℝ≥0∞)) p.1 * f p.2
  have hh : Measurable h :=
    ((measurable_const.indicator hA).comp measurable_fst).mul (hf.comp measurable_snd)
  have h1 : ∫⁻ p, h p ∂((μ.map g) ⊗ₘ η) = ∫⁻ u in A, ∫⁻ x, f x ∂(η u) ∂(μ.map g) := by
    rw [Measure.lintegral_compProd hh]
    have : ∀ u, ∫⁻ x, h (u, x) ∂(η u) =
        A.indicator (fun u => ∫⁻ x, f x ∂(η u)) u := by
      intro u
      show ∫⁻ x, A.indicator (fun _ => (1 : ℝ≥0∞)) u * f x ∂(η u) = _
      rw [lintegral_const_mul _ hf]
      by_cases hu : u ∈ A <;> simp [hu]
    simp_rw [this]
    exact lintegral_indicator hA _
  have h2 : ∫⁻ p, h p ∂(μ.map (fun x => (g x, x))) = ∫⁻ x in g ⁻¹' A, f x ∂μ := by
    rw [lintegral_map hh hgx]
    have : ∀ x, h (g x, x) = (g ⁻¹' A).indicator f x := by
      intro x
      show A.indicator (fun _ => (1 : ℝ≥0∞)) (g x) * f x = _
      by_cases hx : g x ∈ A
      · simp [hx, Set.indicator_of_mem (show x ∈ g ⁻¹' A from hx)]
      · simp [hx, Set.indicator_of_notMem (show x ∉ g ⁻¹' A from hx)]
    simp_rw [this]
    exact lintegral_indicator (hg hA) _
  rw [← h1, hcp, h2]

theorem mix_ae {α β 𝓨 : Type*} [mα : MeasurableSpace α] [mβ : MeasurableSpace β]
    [m𝓨 : MeasurableSpace 𝓨] [MeasurableSpace.CountablyGenerated 𝓨]
    (μ : Measure α) [IsFiniteMeasure μ] (g : α → β) (hg : Measurable g)
    (η : Kernel β α) [IsMarkovKernel η]
    (hη : ∀ A, MeasurableSet A → ∀ B, MeasurableSet B →
      ∫⁻ u in A, η u B ∂(μ.map g) = μ (g ⁻¹' A ∩ B))
    (κ : Kernel α 𝓨) [IsMarkovKernel κ] (κ' : Kernel β 𝓨) [IsMarkovKernel κ']
    (h : ∀ A, MeasurableSet A → ∀ B, MeasurableSet B →
      ∫⁻ u in A, κ' u B ∂(μ.map g) = ∫⁻ x in g ⁻¹' A, κ x B ∂μ) :
    ∀ᵐ u ∂(μ.map g), κ' u = (η u).bind κ := by
  have hrect : ∀ A, MeasurableSet A → ∀ B, MeasurableSet B →
      ((μ.map g) ⊗ₘ κ') (A ×ˢ B) = ((μ.map g) ⊗ₘ (κ ∘ₖ η)) (A ×ˢ B) := by
    intro A hA B hB
    rw [Measure.compProd_apply_prod hA hB, Measure.compProd_apply_prod hA hB, h A hA B hB]
    have : ∀ u, (κ ∘ₖ η) u B = ∫⁻ x, κ x B ∂(η u) := fun u => Kernel.comp_apply' _ _ _ hB
    simp_rw [this]
    rw [setLIntegral_disint μ g hg η hη A hA _ (κ.measurable_coe hB)]
  have hcp : (μ.map g) ⊗ₘ κ' = (μ.map g) ⊗ₘ (κ ∘ₖ η) := by
    refine ext_of_generate_finite _ generateFrom_prod.symm isPiSystem_prod ?_ ?_
    · rintro _ ⟨A, hA, B, hB, rfl⟩
      exact hrect A hA B hB
    · rw [← Set.univ_prod_univ]
      exact hrect _ MeasurableSet.univ _ MeasurableSet.univ
  filter_upwards [Kernel.ae_eq_of_compProd_eq hcp] with u hu
  rw [hu, Kernel.comp_apply]

end OTGen

open OTSensitivity.Info in
theorem solution {Ω 𝓧 𝓨 𝓤 : Type*} [MeasurableSpace Ω]
    [TopologicalSpace 𝓧] [PolishSpace 𝓧] [m𝓧 : MeasurableSpace 𝓧] [BorelSpace 𝓧]
    [TopologicalSpace 𝓨] [PolishSpace 𝓨] [MeasurableSpace 𝓨] [BorelSpace 𝓨]
    [TopologicalSpace 𝓤] [PolishSpace 𝓤] [m𝓤 : MeasurableSpace 𝓤] [BorelSpace 𝓤]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (X : Ω → 𝓧) (Y : Ω → 𝓨) (hX : Measurable X) (hY : Measurable Y)
    (g : 𝓧 → 𝓤) (hg : Measurable g)
    (κ : Kernel 𝓧 𝓨) (hκ : IsCondDistrib P X Y m𝓧 κ)
    (κU : Kernel 𝓤 𝓨) (hκU : IsCondDistrib P (g ∘ X) Y m𝓤 κU)
    (μg : Kernel 𝓤 𝓧) (hμg : IsCondDistrib (P.map X) g id m𝓤 μg) :
    ∀ᵐ u ∂(P.map (g ∘ X)), κU u = (μg u).bind κ := by
  set μ : Measure 𝓧 := P.map X with hμdef
  haveI : IsProbabilityMeasure μ := Measure.isProbabilityMeasure_map hX.aemeasurable
  haveI : IsMarkovKernel κ := hκ.1
  haveI : IsMarkovKernel κU := hκU.1
  haveI : IsMarkovKernel μg := hμg.1
  have hmap : μ.map g = P.map (g ∘ X) := Measure.map_map hg hX
  have hη : ∀ A, MeasurableSet A → ∀ B, MeasurableSet B →
      ∫⁻ u in A, μg u B ∂(μ.map g) = μ (g ⁻¹' A ∩ B) := by
    intro A hA B hB
    exact (hμg.2.2 A hA B hB).symm
  have h : ∀ A, MeasurableSet A → ∀ B, MeasurableSet B →
      ∫⁻ u in A, κU u B ∂(μ.map g) = ∫⁻ x in g ⁻¹' A, κ x B ∂μ := by
    intro A hA B hB
    rw [hmap, ← hκU.2.2 A hA B hB, ← hκ.2.2 (g ⁻¹' A) (hg hA) B hB]
    rfl
  have h1 := OTGen.mix_ae μ g hg μg hη κ κU h
  rw [hmap] at h1
  exact h1
