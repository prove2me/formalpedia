-- Prove2me | solution 1 for SpreadBetting.Inertial.lemma_4
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-30T17:25:48.435917+00:00
-- url     : https://prove2.me/submissions/ceb3e6f6-c45a-4694-b17f-cdc2003ba4c1

import Mathlib
import Definitions.Def_GittinsIndex

open MeasureTheory ProbabilityTheory Filter Topology

theorem solution {S : Type*} [MeasurableSpace S] (K : Kernel S S) [IsMarkovKernel K]
    (μ₀ : Measure S) [IsProbabilityMeasure μ₀] (u fn : S → ℝ) (hu : Measurable u)
    (huK : ∀ z, Integrable u (K z)) (hf : ∀ z, fn z = (∫ y, u y ∂(K z)) - u z)
    (hint : ∀ s : ℕ, Integrable (fun ω : ℕ → S => u (ω s))
      (Kernel.trajMeasure (X := fun _ => S) μ₀ (BanditAlgorithm.markovChainStep K))) :
    ∀ t : ℕ, ∑ s ∈ Finset.range t,
        ∫ ω, fn (ω s) ∂(Kernel.trajMeasure (X := fun _ => S) μ₀ (BanditAlgorithm.markovChainStep K))
      = (∫ ω, u (ω t) ∂(Kernel.trajMeasure (X := fun _ => S) μ₀ (BanditAlgorithm.markovChainStep K)))
        - ∫ ω, u (ω 0) ∂(Kernel.trajMeasure (X := fun _ => S) μ₀ (BanditAlgorithm.markovChainStep K)) := by
  intro t
  set P := Kernel.trajMeasure (X := fun _ => S) μ₀ (BanditAlgorithm.markovChainStep K) with hP
  have key : ∀ s : ℕ, Integrable (fun ω : ℕ → S => ∫ y, u y ∂(K (ω s))) P ∧
      ∫ ω, u (ω (s + 1)) ∂P = ∫ ω, (∫ y, u y ∂(K (ω s))) ∂P := by
    intro s
    have hmap : (P.map (Preorder.frestrictLe s)) ⊗ₘ BanditAlgorithm.markovChainStep K s
        = P.map (fun x : ℕ → S => (Preorder.frestrictLe s x, x (s + 1))) :=
      Kernel.map_frestrictLe_trajMeasure_compProd_eq_map_trajMeasure
        (X := fun _ => S) (κ := BanditAlgorithm.markovChainStep K) (μ₀ := μ₀) (a := s)
    have hmeas : Measurable (fun x : ℕ → S => (Preorder.frestrictLe s x, x (s + 1))) := by
      fun_prop
    have hi : Integrable (fun p : (Π _i : Finset.Iic s, S) × S => u p.2)
        ((P.map (Preorder.frestrictLe s)) ⊗ₘ BanditAlgorithm.markovChainStep K s) := by
      rw [hmap]
      exact (integrable_map_measure (g := fun p : (Π _i : Finset.Iic s, S) × S => u p.2)
        (hu.comp measurable_snd).aestronglyMeasurable hmeas.aemeasurable).2 (hint (s + 1))
    have h1 := hi.integral_compProd
    simp only [Kernel.prodMkLeft_apply, Kernel.const_apply] at h1
    have h2 := Measure.integral_compProd hi
    rw [hmap, integral_map hmeas.aemeasurable
      (f := fun p : (Π _i : Finset.Iic s, S) × S => u p.2)
      (hu.comp measurable_snd).aestronglyMeasurable] at h2
    have hfr : Measurable (Preorder.frestrictLe (π := fun _ : ℕ => S) s) := by fun_prop
    have hg : AEStronglyMeasurable
        (fun x : (Π _i : Finset.Iic s, S) => ∫ y, u y ∂(BanditAlgorithm.markovChainStep K s x))
        (P.map (Preorder.frestrictLe s)) := h1.aestronglyMeasurable
    rw [integral_map hfr.aemeasurable hg] at h2
    rw [integrable_map_measure hg hfr.aemeasurable] at h1
    simp only [BanditAlgorithm.markovChainStep, Kernel.comap_apply, Preorder.frestrictLe_apply,
      Function.comp_def] at h1 h2
    exact ⟨h1, h2⟩
  have step : ∀ s : ℕ, ∫ ω, fn (ω s) ∂P = ∫ ω, u (ω (s + 1)) ∂P - ∫ ω, u (ω s) ∂P := by
    intro s
    rw [(key s).2, ← integral_sub (key s).1 (hint s)]
    congr 1
    ext ω
    rw [hf]
  rw [Finset.sum_congr rfl (fun s _ => step s)]
  exact Finset.sum_range_sub (fun s => ∫ ω, u (ω s) ∂P) t
