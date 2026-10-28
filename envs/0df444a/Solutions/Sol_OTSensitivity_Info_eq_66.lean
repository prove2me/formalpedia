-- Prove2me | solution 1 for OTSensitivity.Info.eq_66
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-24T16:56:04.031078+00:00
-- url     : https://prove2.me/submissions/a0885aff-3ce5-4446-9085-dd7e8c739b01

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
theorem solution {Ω 𝓧 𝓨 : Type*} [MeasurableSpace Ω] (F : MeasurableSpace 𝓧)
    [TopologicalSpace 𝓧] [PolishSpace 𝓧] [m𝓧 : MeasurableSpace 𝓧] [BorelSpace 𝓧]
    [TopologicalSpace 𝓨] [PolishSpace 𝓨] [MeasurableSpace 𝓨] [BorelSpace 𝓨]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (X : Ω → 𝓧) (Y : Ω → 𝓨) (hX : Measurable X) (hY : Measurable Y)
    (hF : F ≤ m𝓧)
    (κ : Kernel 𝓧 𝓨) (hκ : IsCondDistrib P X Y m𝓧 κ)
    (κF : Kernel 𝓧 𝓨) (hκF : IsCondDistrib P X Y F κF)
    (μF : Kernel 𝓧 𝓧) (hμF : IsCondDistrib (P.map X) id id F μF) :
    ∀ᵐ x' ∂(P.map X), κF x' = (μF x').bind κ := by
  set μ : Measure 𝓧 := P.map X with hμdef
  haveI : IsProbabilityMeasure μ := Measure.isProbabilityMeasure_map hX.aemeasurable
  haveI : IsMarkovKernel κ := hκ.1
  haveI : IsMarkovKernel κF := hκF.1
  haveI : IsMarkovKernel μF := hμF.1
  have hid : @Measurable 𝓧 𝓧 m𝓧 F id := measurable_id'' hF
  let μF' : @Kernel 𝓧 𝓧 F m𝓧 :=
    @Kernel.mk 𝓧 𝓧 F m𝓧 (fun x => μF x)
      (Measure.measurable_of_measurable_coe (mβ := F) (fun x => μF x)
        (fun B hB => hμF.2.1 B hB))
  haveI : @IsMarkovKernel 𝓧 𝓧 F m𝓧 μF' :=
    ⟨fun x => (inferInstance : IsProbabilityMeasure (μF x))⟩
  let κF' : @Kernel 𝓧 𝓨 F _ :=
    @Kernel.mk 𝓧 𝓨 F _ (fun x => κF x)
      (Measure.measurable_of_measurable_coe (mβ := F) (fun x => κF x)
        (fun B hB => hκF.2.1 B hB))
  haveI : @IsMarkovKernel 𝓧 𝓨 F _ κF' :=
    ⟨fun x => (inferInstance : IsProbabilityMeasure (κF x))⟩
  have hconv : ∀ (f : 𝓧 → ℝ≥0∞), Measurable[F] f → ∀ A, MeasurableSet[F] A →
      ∫⁻ u in A, f u ∂(@Measure.map 𝓧 𝓧 m𝓧 F id μ) = ∫⁻ x in A, f x ∂μ := by
    intro f hf A hA
    rw [@setLIntegral_map 𝓧 𝓧 m𝓧 F μ f id A hA hf hid]
    rfl
  have hη : ∀ A, MeasurableSet[F] A → ∀ B, MeasurableSet B →
      ∫⁻ u in A, μF' u B ∂(@Measure.map 𝓧 𝓧 m𝓧 F id μ) = μ (id ⁻¹' A ∩ B) := by
    intro A hA B hB
    refine (hconv (fun u => μF u B) (hμF.2.1 B hB) A hA).trans ?_
    have := hμF.2.2 A hA B hB
    rw [Measure.map_id] at this
    exact this.symm
  have h : ∀ A, MeasurableSet[F] A → ∀ B, MeasurableSet B →
      ∫⁻ u in A, κF' u B ∂(@Measure.map 𝓧 𝓧 m𝓧 F id μ) = ∫⁻ x in id ⁻¹' A, κ x B ∂μ := by
    intro A hA B hB
    refine (hconv (fun u => κF u B) (hκF.2.1 B hB) A hA).trans ?_
    show ∫⁻ x in A, κF x B ∂μ = ∫⁻ x in A, κ x B ∂μ
    rw [← hκF.2.2 A hA B hB, ← hκ.2.2 A (hF A hA) B hB]
  have h1 := OTGen.mix_ae (mα := m𝓧) (mβ := F) μ id hid μF' hη κ κF' h
  refine ae_of_ae_map (mβ := F) (f := id) (μ := μ) ?_ h1
  exact ⟨id, hid, Filter.EventuallyEq.rfl⟩
