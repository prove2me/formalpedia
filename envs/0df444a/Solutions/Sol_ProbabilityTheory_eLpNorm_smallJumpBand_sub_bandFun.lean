-- Prove2me | solution 1 for ProbabilityTheory.eLpNorm_smallJumpBand_sub_bandFun
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-01T20:33:55.13319+00:00
-- url     : https://prove2.me/submissions/d3d09be0-5224-40f9-ad56-2399bbed6743

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
    (hd : IsPoissonPointFamily K X ((volume : Measure ℝ).prod ν) μ) (hν : IsLevyMeasure ν)
    (s t : ℝ) {B : Set ℝ} (hB : MeasurableSet B) (hBsub : B ⊆ Set.Ioo (-1) 1) (hBfin : ν B < ⊤) :
    eLpNorm (compensatedPoissonIntegral hd ((memLp_two_smallJumpBandFun hν s t).toLp
          ((Set.Ioc s t ×ˢ Set.Ioo (-1:ℝ) 1).indicator fun p => p.2))
        - compensatedPoissonIntegral hd ((memLp_two_bandFun hB hBsub hBfin s t).toLp
            ((Set.Ioc s t ×ˢ B).indicator fun p => p.2))) 2 μ
      = eLpNorm ((Set.Ioc s t ×ˢ (Set.Ioo (-1:ℝ) 1 \ B)).indicator fun p : ℝ × ℝ => p.2) 2
          (volume.prod ν) := by
  have hunion_prod : Set.Ioc s t ×ˢ Set.Ioo (-1:ℝ) 1
      = (Set.Ioc s t ×ˢ B) ∪ (Set.Ioc s t ×ˢ (Set.Ioo (-1:ℝ) 1 \ B)) := by
    rw [← Set.prod_union, Set.union_sdiff_cancel hBsub]
  have hdisj_prod : Disjoint (Set.Ioc s t ×ˢ B) (Set.Ioc s t ×ˢ (Set.Ioo (-1:ℝ) 1 \ B)) :=
    Set.Disjoint.set_prod_right disjoint_sdiff_self_right _ _
  have hsplit_fun : ((Set.Ioc s t ×ˢ Set.Ioo (-1:ℝ) 1).indicator fun p : ℝ × ℝ => p.2)
        - ((Set.Ioc s t ×ˢ B).indicator fun p : ℝ × ℝ => p.2)
      = (Set.Ioc s t ×ˢ (Set.Ioo (-1:ℝ) 1 \ B)).indicator fun p : ℝ × ℝ => p.2 := by
    rw [hunion_prod, Set.indicator_union_of_disjoint hdisj_prod]
    ext p
    simp only [Pi.sub_apply]
    ring
  have hsub : compensatedPoissonIntegral hd ((memLp_two_smallJumpBandFun hν s t).toLp
          ((Set.Ioc s t ×ˢ Set.Ioo (-1:ℝ) 1).indicator fun p => p.2))
        - compensatedPoissonIntegral hd ((memLp_two_bandFun hB hBsub hBfin s t).toLp
            ((Set.Ioc s t ×ˢ B).indicator fun p => p.2))
      = compensatedPoissonIntegral hd ((memLp_two_smallJumpBandFun hν s t).toLp
            ((Set.Ioc s t ×ˢ Set.Ioo (-1:ℝ) 1).indicator fun p => p.2)
          - (memLp_two_bandFun hB hBsub hBfin s t).toLp
            ((Set.Ioc s t ×ˢ B).indicator fun p => p.2)) :=
    (compensatedPoissonIntegral_sub _ _ _).symm
  rw [hsub, eLpNorm_compensatedPoissonIntegral]
  refine eLpNorm_congr_ae ?_
  filter_upwards [Lp.coeFn_sub ((memLp_two_smallJumpBandFun hν s t).toLp
      ((Set.Ioc s t ×ˢ Set.Ioo (-1:ℝ) 1).indicator fun p => p.2))
      ((memLp_two_bandFun hB hBsub hBfin s t).toLp
      ((Set.Ioc s t ×ˢ B).indicator fun p => p.2)),
    (memLp_two_smallJumpBandFun hν s t).coeFn_toLp,
    (memLp_two_bandFun hB hBsub hBfin s t).coeFn_toLp] with p h0 h2 h3
  rw [h0]
  simp only [Pi.sub_apply]
  rw [h2, h3]
  exact congrFun hsplit_fun p
