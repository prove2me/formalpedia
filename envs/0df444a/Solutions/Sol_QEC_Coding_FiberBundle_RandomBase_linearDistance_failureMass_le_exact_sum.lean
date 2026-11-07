-- Prove2me | solution 1 for QEC.Coding.FiberBundle.RandomBase.linearDistance_failureMass_le_exact_sum
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T06:23:39.349192+00:00
-- url     : https://prove2.me/submissions/a8e2132f-c0f2-4308-89e3-dba33f39165b

import Definitions.Def_QEC_Coding_FiberBundle_RandomBase_Rank
import Definitions.Def_QEC_Coding_FiberBundle_RandomBase_Distance
import Theorems.Thm_QEC_Coding_FiberBundle_RandomBase_supportWord_mem_code_eventMass
import Theorems.Thm_QEC_Coding_FiberBundle_RandomBase_exists_lowWeightSupport_mem_code_of_not_hasLinearDistance
import Theorems.Thm_QEC_Coding_FiberBundle_RandomBase_failureMass_le_sum_eventMass


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.FiberBundle QEC.Coding.FiberBundle.RandomBase
open scoped BigOperators
open MeasureTheory
namespace QEC.Coding.FiberBundle.RandomBase
theorem _root_.solution
    (r Delta : Nat) (hDelta : Delta ≤ 4 * r) :
    failureMass
        (distribution r Delta hDelta)
        (@HasLinearDistance r) ≤
      ∑ A : LowWeightSupport r,
        (ENNReal.ofReal
          ((1 +
            (1 - 2 * (incidenceProbability (4 * r) Delta).toReal) ^
              A.1.card) / 2)) ^ (3 * r) := by
  calc
    _ ≤ ∑ A : LowWeightSupport r,
        eventMass
          (distribution r Delta hDelta)
          (fun sample => supportWord A.1 ∈ (code sample).carrier) := by
      apply failureMass_le_sum_eventMass
      intro sample hsample
      exact exists_lowWeightSupport_mem_code_of_not_hasLinearDistance hsample
    _ = _ := by
      apply Fintype.sum_congr
      intro A
      exact supportWord_mem_code_eventMass r Delta hDelta A.1
end QEC.Coding.FiberBundle.RandomBase
