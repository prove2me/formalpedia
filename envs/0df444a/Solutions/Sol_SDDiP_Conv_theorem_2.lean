-- Prove2me | solution 1 for SDDiP.Conv.theorem_2
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-04T00:34:45.271129+00:00
-- url     : https://prove2.me/submissions/c823927c-8b7c-40ad-ab17-2b921555445a

import Mathlib
import Definitions.Def_SDDiP_Conv_SND
import Theorems.Thm_SDDiP_Conv_finite_changes
import Theorems.Thm_SDDiP_Conv_claim_2

open SDDiP.Conv StochasticProg.Multistage MeasureTheory Filter

theorem solution {H d ℓ M : ℕ} (D : Model H d ℓ) (hM : 0 < M) (L : D.T.Node → ℝ)
    (hL : ∀ n x, ¬ D.IsLeaf n → L n ≤ D.Qcal n x)
    (sol : D.Solver) (hsol : D.IsOptimalSolver sol)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (S : ℕ → Ω → Fin M → D.Leaf) (hS : D.IsSampling P S)
    (κ : Ω → ℕ → D.T.Node → Cut d)
    (hvalid : ∀ ω, D.ValidCuts (fun i => S i ω) (κ ω))
    (htight : ∀ ω, D.TightCuts L sol (fun i => S i ω) (κ ω))
    (hfin : ∀ ω, D.FiniteCuts (fun i => S i ω) (κ ω)) :
    ∀ᵐ ω ∂P, ∀ᶠ i in atTop, D.IsOptimal (D.forwardSol L sol (fun i => S i ω) (κ ω) i) := by
  filter_upwards [claim_2 D hM L hL sol hsol P S hS κ hvalid htight hfin] with ω hω
  obtain ⟨i₁, hi₁⟩ := finite_changes D L (fun i => S i ω) (κ ω) (hfin ω)
  rw [eventually_atTop]
  refine ⟨i₁, fun i hi => hω i (fun k hk => ?_)⟩
  rw [hi₁ k (le_trans hi hk), hi₁ i hi]
