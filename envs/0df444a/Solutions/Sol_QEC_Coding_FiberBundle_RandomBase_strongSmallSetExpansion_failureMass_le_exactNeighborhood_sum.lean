-- Prove2me | solution 1 for QEC.Coding.FiberBundle.RandomBase.strongSmallSetExpansion_failureMass_le_exactNeighborhood_sum
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T08:55:22.803201+00:00
-- url     : https://prove2.me/submissions/1395c107-b1f3-4874-a8ee-3101cb5f7ef4

import Definitions.Def_QEC_Coding_FiberBundle_RandomBase_Expansion
import Definitions.Def_QEC_Coding_FiberBundle_RandomBase_ExpansionProbability
import Theorems.Thm_QEC_Coding_FiberBundle_RandomBase_exactNeighborhood_eventMass
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
        (1 -
          (((1 - incidenceProbability (4 * r) Delta : NNReal) : ENNReal) ^
            witness.1.1.card)) ^ witness.1.2.card *
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
    _ = _ := by
      apply Fintype.sum_congr
      intro witness
      exact exactNeighborhood_eventMass
        r Delta hDelta witness.1.1 witness.1.2
end QEC.Coding.FiberBundle.RandomBase
