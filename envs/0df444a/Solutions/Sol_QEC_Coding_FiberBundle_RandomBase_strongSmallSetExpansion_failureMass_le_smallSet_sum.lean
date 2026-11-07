-- Prove2me | solution 1 for QEC.Coding.FiberBundle.RandomBase.strongSmallSetExpansion_failureMass_le_smallSet_sum
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T08:36:31.087777+00:00
-- url     : https://prove2.me/submissions/5d31ffa2-aaad-4463-9c3f-f4f3297f7801

import Definitions.Def_QEC_Coding_FiberBundle_RandomBase_Expansion
import Definitions.Def_QEC_Coding_FiberBundle_RandomBase_ExpansionProbability
import Theorems.Thm_QEC_Coding_FiberBundle_RandomBase_fixedSet_expansionFailure_eventMass_le_exp
import Theorems.Thm_QEC_Coding_FiberBundle_RandomBase_exists_smallNonemptyCheckSet_of_not_hasStrongSmallSetExpansion
import Theorems.Thm_QEC_Coding_FiberBundle_RandomBase_failureMass_le_sum_eventMass


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.FiberBundle QEC.Coding.FiberBundle.RandomBase
open scoped BigOperators
open MeasureTheory
namespace QEC.Coding.FiberBundle.RandomBase
theorem _root_.solution
    (r Delta : Nat) (hr : 0 < r) (hDelta : Delta ≤ 4 * r) :
    failureMass
        (distribution r Delta hDelta)
        (fun sample =>
          HasStrongSmallSetExpansion (Delta := Delta) sample) ≤
      ∑ S : SmallNonemptyCheckSet r Delta,
        ENNReal.ofReal
          (Real.exp (-((Delta : Real) * S.1.1.card / 1000))) := by
  calc
    _ ≤ ∑ S : SmallNonemptyCheckSet r Delta,
        eventMass
          (distribution r Delta hDelta)
          (fun sample =>
            100 * (checkSetNeighborhood sample S.1.1).card <
              92 * Delta * S.1.1.card) := by
      apply failureMass_le_sum_eventMass
      intro sample hsample
      exact
        exists_smallNonemptyCheckSet_of_not_hasStrongSmallSetExpansion
          hsample
    _ ≤ _ := by
      exact Finset.sum_le_sum fun S _ =>
        fixedSet_expansionFailure_eventMass_le_exp
          r Delta hr hDelta S.1.1 S.2
end QEC.Coding.FiberBundle.RandomBase
