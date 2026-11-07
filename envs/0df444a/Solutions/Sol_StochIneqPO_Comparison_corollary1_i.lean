-- Prove2me | solution 1 for StochIneqPO.Comparison.corollary1_i
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-06T17:37:13.733203+00:00
-- url     : https://prove2.me/submissions/16e81fde-4fec-4f7c-bd89-39cd55ef3adb
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_StochIneqPO_Comparison_StochLE
import Theorems.Thm_StochIneqPO_Comparison_comparison_theorem

open MeasureTheory ProbabilityTheory Finset StochIneqPO.Comparison

theorem solution {E : Type*} [TopologicalSpace E] [PolishSpace E] [MeasurableSpace E]
    [BorelSpace E] [PartialOrder E] [OrderClosedTopology E]
    (P₁ Q₁ : Measure E) [IsProbabilityMeasure P₁] [IsProbabilityMeasure Q₁]
    (p q : (n : ℕ) → Kernel (Π _ : Iic n, E) E)
    [∀ n, IsMarkovKernel (p n)] [∀ n, IsMarkovKernel (q n)]
    (hPQ : StochLE P₁ Q₁)
    (hpq : ∀ n, ∀ x y : Π _ : Iic n, E, x ≤ y → StochLE (p n x) (q n y))
    (A : Set E) (hA : MeasurableSet A) (hAup : IsUpperSet A) (n : ℕ) :
    Kernel.trajMeasure (X := fun _ => E) P₁ p {x | x n ∈ A} ≤
      Kernel.trajMeasure (X := fun _ => E) Q₁ q {x | x n ∈ A} := by
  obtain ⟨Ω, mΩ, μ, hμ, X, Y, hX, hY, hlX, hlY, hle⟩ :=
    comparison_theorem (E := fun _ => E) P₁ Q₁ p q hPQ hpq
  have hS : MeasurableSet {x : ℕ → E | x n ∈ A} := measurable_pi_apply n hA
  have hXm : Measurable (fun ω n => X n ω) := measurable_pi_lambda _ hX
  have hYm : Measurable (fun ω n => Y n ω) := measurable_pi_lambda _ hY
  rw [← hlX, ← hlY, Measure.map_apply hXm hS, Measure.map_apply hYm hS]
  apply measure_mono_ae
  filter_upwards [hle] with ω h hx
  exact hAup (h n) hx
