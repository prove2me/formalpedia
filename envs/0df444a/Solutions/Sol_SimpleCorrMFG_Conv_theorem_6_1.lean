-- Prove2me | solution 1 for SimpleCorrMFG.Conv.theorem_6_1
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-21T06:03:36.975007+00:00
-- url     : https://prove2.me/submissions/c5bc4247-2132-4ecb-8e77-0fad75f78372

import Mathlib
import Definitions.Def_SimpleCorrMFG_Conv_Model
import Definitions.Def_SimpleCorrMFG_Conv_NPlayer
import Definitions.Def_SimpleCorrMFG_Conv_MFG
import Theorems.Thm_SimpleCorrMFG_Conv_limit_points_optimal
import Theorems.Thm_SimpleCorrMFG_Conv_limit_points_consistent

open MeasureTheory ProbabilityTheory unitInterval Filter Topology SimpleCorrMFG.Conv

theorem solution {T : ℕ} {X Γ : Type} [Fintype X] [DecidableEq X] [Nonempty X]
    [TopologicalSpace X] [DiscreteTopology X] [MeasurableSpace X] [DiscreteMeasurableSpace X]
    [Fintype Γ] [Nonempty Γ] [TopologicalSpace Γ] [DiscreteTopology Γ] [MeasurableSpace Γ]
    [DiscreteMeasurableSpace Γ]
    (M : Model T X Γ) (hM : M.Standing) (hA1 : M.A1) (hA2 : M.A2)
    (m₀ : Meas X) (m0N : ℕ → Meas X) (γ : (N : ℕ) → ProbabilityMeasure (Fin N → Strat T X Γ))
    (ε : ℕ → ℝ) (hε : ∀ N, 0 ≤ ε N)
    (hA3 : ∀ N : ℕ, 2 ≤ N → IsSymmetric (γ N) ∧ IsEpsCE M (prodInit N (m0N N)) (γ N) (ε N))
    (hA4 : Tendsto ε atTop (𝓝 0))
    (hA5 : Tendsto m0N atTop (𝓝 m₀)) :
    IsCompact (closure (Set.range (rhoSeq M m0N γ))) ∧
      ∀ ρ : ProbabilityMeasure (Strat T X Γ × Flow T X),
        (∃ φ : ℕ → ℕ, StrictMono φ ∧ Tendsto (rhoSeq M m0N γ ∘ φ) atTop (𝓝 ρ)) →
          IsCorrelatedSolution M m₀ ρ := by
  have hX : CompactSpace (Meas X) := isCompact_iff_compactSpace.mp (isCompact_stdSimplex ℝ X)
  have hC : CompactSpace (ProbabilityMeasure (Strat T X Γ × Flow T X)) :=
    @instCompactSpaceProbabilityMeasure (Strat T X Γ × Flow T X) _ _ _ _ _
  refine ⟨isClosed_closure.isCompact, fun ρ hρ => ⟨?_, ?_⟩⟩
  · exact limit_points_optimal M hM hA1 hA2 m₀ m0N γ ε hε hA3 hA4 hA5 ρ hρ
  · exact limit_points_consistent M hM hA1 hA2 m₀ m0N γ ε hε hA3 hA4 hA5 ρ hρ
