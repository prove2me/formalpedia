-- Prove2me | solution 1 for ProbabilityTheory.compensatedBand_sub_aux
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-01T19:35:34.202177+00:00
-- url     : https://prove2.me/submissions/b471ea21-0a52-4667-9e53-c3d373507482

import Definitions.Def_LeanLevy_RandomMeasure_LevyJumpPath
import Definitions.Def_LeanLevy_RandomMeasure_PoissonCompensated
import Definitions.Def_LeanLevy_RandomMeasure_TimeSpacePoisson
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true
open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal
variable {Ω : Type} [MeasurableSpace Ω] {K : ℕ → Ω → ℕ}
  {X : ℕ → ℕ → Ω → ℝ × ℝ} {ν : Measure ℝ} [SigmaFinite ν]
  {μ : Measure Ω} {A : Set ℝ}
theorem solution [IsProbabilityMeasure μ]
    (hd : IsPoissonPointFamily K X ((volume : Measure ℝ).prod ν) μ)
    (hA : MeasurableSet A) (hAsub : A ⊆ Set.Ioo (-1 : ℝ) 1) (hAfin : ν A < ⊤)
    {s t : ℝ} (h0 : 0 ≤ s) (hst : s ≤ t) :
    compensatedPoissonIntegral hd ((memLp_two_bandFun hA hAsub hAfin 0 t).toLp _)
        - compensatedPoissonIntegral hd ((memLp_two_bandFun hA hAsub hAfin 0 s).toLp _)
      = compensatedPoissonIntegral hd ((memLp_two_bandFun hA hAsub hAfin s t).toLp _) := by
  have hdisj : Disjoint (Set.Ioc 0 s ×ˢ A) (Set.Ioc s t ×ˢ A) :=
    Set.Disjoint.set_prod_left (Set.Ioc_disjoint_Ioc_of_le (le_refl s)) _ _
  have hfun : ((Set.Ioc 0 t ×ˢ A).indicator fun p : ℝ × ℝ => p.2)
      = (Set.Ioc 0 s ×ˢ A).indicator (fun p : ℝ × ℝ => p.2)
        + (Set.Ioc s t ×ˢ A).indicator (fun p : ℝ × ℝ => p.2) := by
    rw [← Set.Ioc_union_Ioc_eq_Ioc h0 hst, Set.union_prod, Set.indicator_union_of_disjoint hdisj]
    rfl
  have htoLp : (memLp_two_bandFun hA hAsub hAfin 0 t).toLp
        ((Set.Ioc 0 t ×ˢ A).indicator fun p : ℝ × ℝ => p.2)
      = (memLp_two_bandFun hA hAsub hAfin 0 s).toLp
          ((Set.Ioc 0 s ×ˢ A).indicator fun p : ℝ × ℝ => p.2)
        + (memLp_two_bandFun hA hAsub hAfin s t).toLp
          ((Set.Ioc s t ×ˢ A).indicator fun p : ℝ × ℝ => p.2) := by
    rw [← MemLp.toLp_add]
    exact MemLp.toLp_congr _ _ (Filter.EventuallyEq.of_eq hfun)
  rw [htoLp, compensatedPoissonIntegral_add, add_sub_cancel_left]