-- Prove2me | solution 1 for QEC.Coding.FiberBundle.RandomBase.strongSmallSetExpansion_failureMass_le_occupancy_sum
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T08:55:32.343287+00:00
-- url     : https://prove2.me/submissions/0d1ab181-20a8-429a-8332-2445456824f9

import Definitions.Def_QEC_Coding_FiberBundle_RandomBase_Expansion
import Definitions.Def_QEC_Coding_FiberBundle_RandomBase_ExpansionProbability
import Theorems.Thm_QEC_Coding_FiberBundle_RandomBase_exactNeighborhood_eventMass_le_hitBound
import Theorems.Thm_QEC_Coding_FiberBundle_RandomBase_exists_exact_expansionWitness_of_not_hasStrongSmallSetExpansion
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
        (fun sample =>
          HasStrongSmallSetExpansion (Delta := Delta) sample) ≤
      ∑ witness : ExpansionWitness r Delta,
        ((witness.1.1.card : ENNReal) *
          (incidenceProbability (4 * r) Delta : ENNReal)) ^
            witness.1.2.card *
        (((1 - incidenceProbability (4 * r) Delta : NNReal) : ENNReal) ^
          witness.1.1.card) ^ (4 * r - witness.1.2.card) := by
  calc
    _ ≤ ∑ witness : ExpansionWitness r Delta,
        eventMass
          (distribution r Delta hDelta)
          (fun sample =>
            checkSetNeighborhood sample witness.1.1 = witness.1.2) := by
      apply failureMass_le_sum_eventMass
      intro sample hsample
      exact
        exists_exact_expansionWitness_of_not_hasStrongSmallSetExpansion
          hsample
    _ ≤ _ := by
      exact Finset.sum_le_sum fun witness _ =>
        exactNeighborhood_eventMass_le_hitBound
          r Delta hDelta witness.1.1 witness.1.2
end QEC.Coding.FiberBundle.RandomBase
