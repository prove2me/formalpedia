-- Prove2me | solution 1 for QEC.Coding.FiberBundle.RandomBase.strongSmallSetExpansion_failureMass_le_exact_sum
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T07:49:03.257745+00:00
-- url     : https://prove2.me/submissions/79a38451-e252-41a5-8474-d214f21df8c1

import Definitions.Def_QEC_Coding_FiberBundle_RandomBase_Distance
import Definitions.Def_QEC_Coding_FiberBundle_RandomBase_Expansion
import Theorems.Thm_QEC_Coding_FiberBundle_RandomBase_avoidsOutside_eventMass
import Theorems.Thm_QEC_Coding_FiberBundle_RandomBase_exists_expansionWitness_of_not_hasStrongSmallSetExpansion
import Theorems.Thm_QEC_Coding_FiberBundle_RandomBase_failureMass_le_sum_eventMass


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.FiberBundle QEC.Coding.FiberBundle.RandomBase
open scoped BigOperators
namespace QEC.Coding.FiberBundle.RandomBase
theorem _root_.solution
    (r Delta : Nat) (hDelta : Delta ≤ 4 * r) :
    failureMass
        (distribution r Delta hDelta)
        (fun sample =>
          HasStrongSmallSetExpansion (Delta := Delta) sample) ≤
      ∑ witness : ExpansionWitness r Delta,
        (((1 - incidenceProbability (4 * r) Delta : NNReal) : ENNReal) ^
          (witness.1.1.card * (4 * r - witness.1.2.card))) := by
  calc
    _ ≤ ∑ witness : ExpansionWitness r Delta,
        eventMass
          (distribution r Delta hDelta)
          (AvoidsOutside witness.1.1 witness.1.2) := by
      apply failureMass_le_sum_eventMass
      intro sample hsample
      exact exists_expansionWitness_of_not_hasStrongSmallSetExpansion hsample
    _ = _ := by
      apply Fintype.sum_congr
      intro witness
      exact avoidsOutside_eventMass
        r Delta hDelta witness.1.1 witness.1.2
end QEC.Coding.FiberBundle.RandomBase
