-- Prove2me | solution 1 for SamplingRealizesAverages
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T12:48:09.38485+00:00
-- url     : https://prove2.me/submissions/469131a1-9554-45b3-95c5-b538845b783c

import Definitions.Def_Tablet_Preamble
import Definitions.Def_Tablet_SamplingRealizesAverages

set_option autoImplicit false
open MeasureTheory ProbabilityTheory Filter Finset Function
theorem _root_.solution
    {X : Type*} [MeasurableSpace X] (mu : Measure X) [IsProbabilityMeasure mu]
    (g : ℕ → X → ℝ) (hgm : ∀ j, Measurable (g j)) (hg : ∀ j, Integrable (g j) mu)
    (S : Set X) (hSm : MeasurableSet S) (hS : mu Sᶜ = 0) :
    ∃ x : ℕ → X, (∀ i, x i ∈ S) ∧
      ∀ j, Tendsto (fun n : ℕ => (∑ i ∈ range n, g j (x i)) / n) atTop
        (nhds (∫ y, g j y ∂mu)) := by
-- BODY
  classical
  set P : Measure (ℕ → X) := Measure.infinitePi (fun _ : ℕ => mu) with hP
  have hPr : IsProbabilityMeasure P := by rw [hP]; infer_instance
  have hmp : ∀ i : ℕ, MeasurePreserving (fun ω : ℕ → X => ω i) P mu :=
    fun i => measurePreserving_eval_infinitePi (fun _ : ℕ => mu) i
  have hindep : iIndepFun (fun (i : ℕ) (ω : ℕ → X) => ω i) P :=
    iIndepFun_infinitePi (fun _ => measurable_id)
  -- Step 1: for each j, the strong law holds P-a.e.
  have key : ∀ j : ℕ, ∀ᵐ ω ∂P,
      Tendsto (fun n : ℕ => (∑ i ∈ range n, g j (ω i)) / n) atTop (nhds (∫ y, g j y ∂mu)) := by
    intro j
    have hcomp : iIndepFun (fun (i : ℕ) (ω : ℕ → X) => g j (ω i)) P :=
      hindep.comp (fun _ => g j) (fun _ => hgm j)
    have hpair : Pairwise ((· ⟂ᵢ[P] ·) on (fun (i : ℕ) (ω : ℕ → X) => g j (ω i))) :=
      fun a b hab => hcomp.indepFun hab
    have hint : Integrable (fun ω : ℕ → X => g j (ω 0)) P :=
      ((hmp 0).integrable_comp (hg j).aestronglyMeasurable).2 (hg j)
    have hident : ∀ i : ℕ,
        IdentDistrib (fun ω : ℕ → X => g j (ω i)) (fun ω : ℕ → X => g j (ω 0)) P P := by
      intro i
      refine ⟨((hgm j).comp (measurable_pi_apply i)).aemeasurable,
              ((hgm j).comp (measurable_pi_apply 0)).aemeasurable, ?_⟩
      rw [show (fun ω : ℕ → X => g j (ω i)) = (g j) ∘ (fun ω : ℕ → X => ω i) from rfl,
          show (fun ω : ℕ → X => g j (ω 0)) = (g j) ∘ (fun ω : ℕ → X => ω 0) from rfl,
          ← Measure.map_map (hgm j) (measurable_pi_apply i),
          ← Measure.map_map (hgm j) (measurable_pi_apply 0),
          (hmp i).map_eq, (hmp 0).map_eq]
    have := strong_law_ae_real (fun i (ω : ℕ → X) => g j (ω i)) hint hpair hident
    have hEq : P[fun ω : ℕ → X => g j (ω 0)] = ∫ y, g j y ∂mu := by
      conv_rhs => rw [← (hmp 0).map_eq]
      rw [integral_map (measurable_pi_apply 0).aemeasurable
        ((hgm j).aestronglyMeasurable)]
    rw [hEq] at this
    exact this
  -- Step 2: almost every sample stays in S
  have hin : ∀ᵐ ω ∂P, ∀ i : ℕ, ω i ∈ S := by
    rw [ae_all_iff]
    intro i
    have hz : P ((fun ω : ℕ → X => ω i) ⁻¹' Sᶜ) = 0 := by
      rw [← Measure.map_apply (measurable_pi_apply i) hSm.compl, (hmp i).map_eq, hS]
    exact mem_ae_iff.mpr hz
  -- Step 3: combine and pick a point
  have hall : ∀ᵐ ω ∂P, (∀ i : ℕ, ω i ∈ S) ∧
      ∀ j : ℕ, Tendsto (fun n : ℕ => (∑ i ∈ range n, g j (ω i)) / n) atTop
        (nhds (∫ y, g j y ∂mu)) := by
    filter_upwards [hin, (ae_all_iff.2 key)] with ω h1 h2 using ⟨h1, h2⟩
  obtain ⟨ω, hω⟩ := hPr.ae_neBot.nonempty_of_mem hall
  exact ⟨ω, hω.1, hω.2⟩
