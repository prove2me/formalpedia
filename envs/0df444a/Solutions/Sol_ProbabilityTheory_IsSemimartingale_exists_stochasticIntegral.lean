-- Prove2me | solution 1 for ProbabilityTheory.IsSemimartingale.exists_stochasticIntegral
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-25T23:21:21.656802+00:00
-- url     : https://prove2.me/submissions/872cc3f4-0468-4a56-ad68-664e40af0de5

import Definitions.Def_SourceProof_361655cd6ef42aa35eef5e59

open ProbabilityTheory MeasureTheory Filter Set
open scoped NNReal ENNReal Topology

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsFiniteMeasure P]
  {F : Filtration ℝ≥0 mΩ} {X H : ℝ≥0 → Ω → ℝ}

theorem solution
    (hX : IsSemimartingale X F P) (hF : F.IsUsual P)
    (ha : Adapted F H) (hr : HasCagladPaths H P) :
    ∃ J : ℝ≥0 → Ω → ℝ, Adapted F J ∧ (∀ ω, IsCadlagPath (J · ω)) ∧
      ∀ S : ℕ → ℝ≥0 → Ω → ℝ, ∀ hS : ∀ n, IsSimplePredictable (S n) F,
        TendstoUCP P S atTop H →
          TendstoUCP P (fun n ↦ (hS n).elementaryIntegralProcess X) atTop J := by
  exact Prove2MeSourceProof.h_361655cd6ef42aa35eef5e59 hX hF ha hr
