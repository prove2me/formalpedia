-- Prove2me | solution 1 for ProbabilityTheory.aestronglyMeasurable_levyCompensatedSmallJump_band
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-01T21:19:33.635302+00:00
-- url     : https://prove2.me/submissions/83d22e8a-f5d5-417d-b9d2-175ae675b128

import Mathlib
import Definitions.Def_LeanLevy_RandomMeasure_PoissonMartingale
import Definitions.Def_LeanLevy_RandomMeasure_PoissonFiltration
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology
variable {Ω : Type} [MeasurableSpace Ω] {ν : Measure ℝ} [SigmaFinite ν]
  {K : ℕ → Ω → ℕ} {X : ℕ → ℕ → Ω → ℝ × ℝ} {μ : Measure Ω}
namespace ProbabilityTheory
private lemma smallJumpBandFun_toLp_ae_zero_off (hν : IsLevyMeasure ν) {s t : ℝ} {A : Set ℝ}
    (hA : Set.Ioc s t ⊆ A) :
    ∀ᵐ p ∂((volume : Measure ℝ).prod ν), p ∉ A ×ˢ (Set.univ : Set ℝ) →
      (memLp_two_smallJumpBandFun hν s t).toLp
          ((Set.Ioc s t ×ˢ Set.Ioo (-1) 1).indicator fun q : ℝ × ℝ => q.2) p = 0 := by
  filter_upwards [MemLp.coeFn_toLp (memLp_two_smallJumpBandFun hν s t)] with p hp hpA
  rw [hp]
  apply Set.indicator_of_notMem
  intro hmem
  exact hpA ⟨hA hmem.1, Set.mem_univ _⟩
end ProbabilityTheory
theorem solution [IsProbabilityMeasure μ]
    (hd : IsPoissonPointFamily K X ((volume : Measure ℝ).prod ν) μ) (hν : IsLevyMeasure ν)
    (s t : ℝ) :
    AEStronglyMeasurable[prmEvalSigma K X (volume.prod ν) (Set.Ioc s t ×ˢ Set.univ)]
      (compensatedPoissonIntegral hd ((memLp_two_smallJumpBandFun hν s t).toLp _)) μ :=
  aestronglyMeasurable_compensatedPoissonIntegral_prmEvalSigma hd
    (measurableSet_Ioc.prod MeasurableSet.univ)
    (smallJumpBandFun_toLp_ae_zero_off hν (subset_refl _))
