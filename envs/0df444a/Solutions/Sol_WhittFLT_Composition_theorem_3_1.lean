-- Prove2me | solution 1 for WhittFLT.Composition.theorem_3_1
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-05T13:19:08.878279+00:00
-- url     : https://prove2.me/submissions/245eece3-e79a-4fff-a3e1-d92ecdebd663

import Theorems.Thm_WhittFLT_Composition_theorem_3_1_i
import Theorems.Thm_WhittFLT_Composition_theorem_3_1_ii

open WhittFLT.Composition
open Set Filter Topology
open scoped ENNReal

theorem solution {S : Type*} [MetricSpace S] [CompleteSpace S] [TopologicalSpace.SeparableSpace S]
    (T₁ T₂ T₃ : Set ℝ) (hT₁ : T₁.OrdConnected) (hT₂ : T₂.OrdConnected)
    (hT₃ : T₃.OrdConnected) (hT₁ne : T₁.Nonempty) (hT₂₃ : T₂ ⊆ T₃)
    (hT₃nt : (interior T₃).Nonempty)
    (xs : ℕ → ℝ → S) (x : ℝ → S) (ys : ℕ → ℝ → ℝ) (y : ℝ → ℝ)
    (hys : ∀ n, MonotoneOn (ys n) T₁ ∧ MapsTo (ys n) T₁ T₂)
    (hy : MonotoneOn y T₁ ∧ MapsTo y T₁ T₂)
    (hxs : J1Tendsto T₃ xs x) (hys' : J1Tendsto T₁ ys y)
    (hcase : ContinuousOn x T₃ ∨
      (ContinuousOn y T₁ ∧ StrictMonoOn y T₁ ∧
        ∀ t, IsEndpoint T₁ t → ContinuousWithinAt x T₃ (y t))) :
    J1Tendsto T₁ (fun n => xs n ∘ ys n) (x ∘ y) := by
  rcases hcase with hx | ⟨hyc, hym, hB⟩
  · exact theorem_3_1_i T₁ T₂ T₃ hT₁ hT₂ hT₃ hT₁ne hT₂₃ hT₃nt xs x ys y hys hy hxs hys' hx
  · exact theorem_3_1_ii T₁ T₂ T₃ hT₁ hT₂ hT₃ hT₁ne hT₂₃ xs x ys y hys hy hxs hys' ⟨hyc, hym⟩ hB
