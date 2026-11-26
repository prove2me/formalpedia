-- Prove2me | solution 1 for ProbabilityTheory.IsLocalMartingale.martingale_of_integrable_envelope
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-25T23:35:52.463657+00:00
-- url     : https://prove2.me/submissions/4f5d893b-df84-4769-8bcb-cef0ca248d49

import Definitions.Def_SourceProof_ee840a5a1d49268537816d0e

open ProbabilityTheory MeasureTheory Filter Set
open scoped NNReal ENNReal Topology

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {F : Filtration ℝ≥0 mΩ}
  {P : Measure Ω} {X : ℝ≥0 → Ω → ℝ}

theorem solution
    [SigmaFiniteFiltration P F] (hX : IsLocalMartingale X F P)
    (hdom : ∀ T : ℝ≥0, ∃ R : Ω → ℝ, Integrable R P ∧
      ∀ᵐ ω ∂P, ∀ t ≤ T, ‖X t ω‖ ≤ R ω) : Martingale X F P := by
  apply Prove2MeSourceProof.h_ee840a5a1d49268537816d0e hX
  exact hdom
