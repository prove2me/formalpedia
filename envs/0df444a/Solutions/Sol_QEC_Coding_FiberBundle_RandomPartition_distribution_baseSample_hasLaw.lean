-- Prove2me | solution 1 for QEC.Coding.FiberBundle.RandomPartition.distribution_baseSample_hasLaw
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T08:36:42.755206+00:00
-- url     : https://prove2.me/submissions/7c48ea0f-586e-4f3c-85b5-9776808a3a24

import Definitions.Def_QEC_Coding_FiberBundle_TwistGraphSpectrumProbability
import Definitions.Def_QEC_Coding_FiberBundle_RandomBase_Rank
import Definitions.Def_QEC_Coding_FiberBundle_RandomBase_Distance
import Definitions.Def_QEC_Coding_FiberBundle_RandomBase_ExpansionProbability
import Mathlib.Probability.Independence.Integration
import Definitions.Def_QEC_Coding_FiberBundle_PartitionedChecksProbability
import Theorems.Thm_QEC_Coding_FiberBundle_RandomPartition_distribution_incidence_iIndepFun
import Theorems.Thm_QEC_Coding_FiberBundle_RandomPartition_distribution_incidence_hasLaw
import Theorems.Thm_QEC_Coding_FiberBundle_RandomBase_independentProduct_toMeasure_eq_pi


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.FiberBundle QEC.Coding.FiberBundle.RandomPartition
open scoped BigOperators
open MeasureTheory
namespace QEC.Coding.FiberBundle.RandomPartition
theorem _root_.solution
    (r Delta : Nat) (hDelta : Delta ≤ 4 * r) :
    ProbabilityTheory.HasLaw
      (baseSample : Sample r → RandomBase.Sample r)
      (RandomBase.distribution r Delta hDelta).toMeasure
      (distribution r Delta hDelta).toMeasure := by
  let μedge :
      (Fin (3 * r) × Fin (4 * r)) → Measure Bool :=
    fun _ =>
      (PMF.bernoulli
        (RandomBase.incidenceProbability (4 * r) Delta)
        (RandomBase.incidenceProbability_le_one hDelta)).toMeasure
  have hCoordinate :
      ∀ edge,
        ProbabilityTheory.HasLaw
          (fun sample : Sample r => sample edge.1 edge.2 false)
          (μedge edge)
          (distribution r Delta hDelta).toMeasure := by
    intro edge
    exact distribution_incidence_hasLaw r Delta hDelta edge
  have hLawPi :
      ProbabilityTheory.HasLaw
        (fun sample : Sample r =>
          fun edge => sample edge.1 edge.2 false)
        (Measure.pi μedge)
        (distribution r Delta hDelta).toMeasure :=
    (distribution_incidence_iIndepFun
      r Delta hDelta).hasLaw_pi hCoordinate
  rw [RandomBase.distribution,
    RandomBase.independentProduct_toMeasure_eq_pi]
  exact hLawPi
end QEC.Coding.FiberBundle.RandomPartition
