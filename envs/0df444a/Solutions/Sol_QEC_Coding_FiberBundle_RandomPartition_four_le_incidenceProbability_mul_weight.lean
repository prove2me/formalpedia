-- Prove2me | solution 1 for QEC.Coding.FiberBundle.RandomPartition.four_le_incidenceProbability_mul_weight
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T08:34:35.878736+00:00
-- url     : https://prove2.me/submissions/037e0ab6-fd90-41c6-af4f-a310540f8912

import Definitions.Def_QEC_Coding_FiberBundle_TwistGraphSpectrumProbability
import Definitions.Def_QEC_Coding_FiberBundle_RandomBase_Rank
import Definitions.Def_QEC_Coding_FiberBundle_RandomBase_Distance
import Definitions.Def_QEC_Coding_FiberBundle_RandomBase_ExpansionProbability
import Mathlib.Probability.Independence.Integration
import Definitions.Def_QEC_Coding_FiberBundle_PartitionedChecksProbability
import Theorems.Thm_QEC_Coding_FiberBundle_RandomBase_check_expected_degree


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.FiberBundle QEC.Coding.FiberBundle.RandomPartition
open scoped BigOperators
open MeasureTheory
namespace QEC.Coding.FiberBundle.RandomPartition
theorem _root_.solution
    (r Delta weight : Nat) (hr : 0 < r)
    (hWeight : 4 * (4 * r) ≤ Delta * weight) :
    (4 : Real) ≤
      (RandomBase.incidenceProbability (4 * r) Delta).toReal *
        weight := by
  let p : Real :=
    (RandomBase.incidenceProbability (4 * r) Delta).toReal
  have hScale :
      ((4 * r : Nat) : Real) * p = Delta :=
    RandomBase.check_expected_degree r Delta hr
  have hWeightReal :
      (4 : Real) * (4 * r : Nat) ≤ (Delta : Real) * weight := by
    exact_mod_cast hWeight
  have hFourRPos : (0 : Real) < (4 * r : Nat) := by positivity
  have hpWeight :
      p * weight =
        ((Delta : Real) * weight) / (4 * r : Nat) := by
    apply (eq_div_iff hFourRPos.ne').2
    nlinarith
  rw [hpWeight]
  exact (le_div_iff₀ hFourRPos).2 hWeightReal
end QEC.Coding.FiberBundle.RandomPartition
