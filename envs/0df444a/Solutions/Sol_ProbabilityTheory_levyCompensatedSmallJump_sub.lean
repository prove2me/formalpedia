-- Prove2me | solution 1 for ProbabilityTheory.levyCompensatedSmallJump_sub
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-01T20:33:44.990205+00:00
-- url     : https://prove2.me/submissions/9817fc6e-a73d-48af-8cfe-6c7de75bcf92

import Definitions.Def_LeanLevy_RandomMeasure_TimeSpacePoisson
import Definitions.Def_LeanLevy_RandomMeasure_PoissonCompensated
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Integral.Bochner.Basic
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal
variable {Ω : Type} [MeasurableSpace Ω] {ν : Measure ℝ} [SigmaFinite ν]
  {K : ℕ → Ω → ℕ} {X : ℕ → ℕ → Ω → ℝ × ℝ} {μ : Measure Ω}
theorem solution [IsProbabilityMeasure μ]
    (hd : IsPoissonPointFamily K X (volume.prod ν) μ) (hν : IsLevyMeasure ν) {s t : ℝ}
    (h0 : 0 ≤ s) (hst : s ≤ t) :
    levyCompensatedSmallJump hd hν t - levyCompensatedSmallJump hd hν s
      = compensatedPoissonIntegral hd ((memLp_two_smallJumpBandFun hν s t).toLp _) := by
  have hdisj : Disjoint (Set.Ioc 0 s ×ˢ Set.Ioo (-1 : ℝ) 1) (Set.Ioc s t ×ˢ Set.Ioo (-1 : ℝ) 1) :=
    Set.Disjoint.set_prod_left (Set.Ioc_disjoint_Ioc_of_le (le_refl s)) _ _
  have hfun : ((Set.Ioc 0 t ×ˢ Set.Ioo (-1 : ℝ) 1).indicator fun p : ℝ × ℝ => p.2)
      = (Set.Ioc 0 s ×ˢ Set.Ioo (-1 : ℝ) 1).indicator (fun p : ℝ × ℝ => p.2)
        + (Set.Ioc s t ×ˢ Set.Ioo (-1 : ℝ) 1).indicator (fun p : ℝ × ℝ => p.2) := by
    rw [← Set.Ioc_union_Ioc_eq_Ioc h0 hst, Set.union_prod, Set.indicator_union_of_disjoint hdisj]
    rfl
  have htoLp : (memLp_two_smallJumpFun hν t).toLp
        ((Set.Ioc 0 t ×ˢ Set.Ioo (-1 : ℝ) 1).indicator fun p : ℝ × ℝ => p.2)
      = (memLp_two_smallJumpFun hν s).toLp
          ((Set.Ioc 0 s ×ˢ Set.Ioo (-1 : ℝ) 1).indicator fun p : ℝ × ℝ => p.2)
        + (memLp_two_smallJumpBandFun hν s t).toLp
          ((Set.Ioc s t ×ˢ Set.Ioo (-1 : ℝ) 1).indicator fun p : ℝ × ℝ => p.2) := by
    rw [← MemLp.toLp_add]
    exact MemLp.toLp_congr _ _ (Filter.EventuallyEq.of_eq hfun)
  simp only [levyCompensatedSmallJump]
  rw [htoLp, compensatedPoissonIntegral_add, add_sub_cancel_left]
