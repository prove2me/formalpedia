-- Prove2me | solution 1 for PettisIntegral.weakIntegral_comp_continuousLinearMap
-- status  : ACCEPTED   (prove)
-- author  : @emmgaml
-- created : 2026-11-22T11:53:41.847069+00:00
-- url     : https://prove2.me/submissions/65533e76-8260-4f64-9e69-5c7825f04b7f

import Mathlib
import Definitions.Def_PettisIntegral_Basic

open MeasureTheory

set_option autoImplicit false

open PettisIntegral

theorem solution {𝕜 E F X : Type*} [RCLike 𝕜]
    [AddCommGroup E] [Module 𝕜 E] [TopologicalSpace E] [IsTopologicalAddGroup E]
    [ContinuousSMul 𝕜 E] [PolynormableSpace 𝕜 E] [T2Space E]
    [AddCommGroup F] [Module 𝕜 F] [TopologicalSpace F] [IsTopologicalAddGroup F]
    [ContinuousSMul 𝕜 F] [PolynormableSpace 𝕜 F] [T2Space F]
    [MeasurableSpace X] (μ : Measure X) (f : X → E) (T : E →L[𝕜] F) :
    (WeaklyIntegrable 𝕜 μ f →
      WeaklyIntegrable 𝕜 μ (fun x => T (f x)) ∧
        ∀ φ : StrongDual 𝕜 F,
          weakIntegral 𝕜 μ (fun x => T (f x)) φ = weakIntegral 𝕜 μ f (φ.comp T)) ∧
    ∀ a : E, HasPettisIntegral 𝕜 μ f a → HasPettisIntegral 𝕜 μ (fun x => T (f x)) (T a) := by
  -- For `φ ∈ F'`, the scalar function `φ ∘ (T ∘ f)` is literally `(φ ∘ T) ∘ f`.
  have key : WeaklyIntegrable 𝕜 μ f → WeaklyIntegrable 𝕜 μ (fun x => T (f x)) := by
    intro hf φ
    exact hf (φ.comp T)
  refine ⟨fun hf => ⟨key hf, fun φ => rfl⟩, ?_⟩
  rintro a ⟨hf, ha⟩
  refine ⟨key hf, fun φ => ?_⟩
  exact ha (φ.comp T)
