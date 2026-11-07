-- Prove2me | solution 1 for QEC.Coding.FiberBundle.RandomBase.exists_expansionWitness_of_not_hasStrongSmallSetExpansion
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T06:18:55.133101+00:00
-- url     : https://prove2.me/submissions/ffa37d17-84f1-40ba-982a-a2ab786155c2

import Definitions.Def_QEC_Coding_FiberBundle_RandomBase_Distance
import Definitions.Def_QEC_Coding_FiberBundle_RandomBase_Expansion
import Theorems.Thm_QEC_Coding_FiberBundle_RandomBase_avoidsOutside_iff_neighborhood_subset

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.FiberBundle QEC.Coding.FiberBundle.RandomBase
open scoped BigOperators
namespace QEC.Coding.FiberBundle.RandomBase
theorem _root_.solution
    {r Delta : Nat} {sample : Sample r}
    (h : ¬HasStrongSmallSetExpansion (Delta := Delta) sample) :
    ∃ witness : ExpansionWitness r Delta,
      AvoidsOutside witness.1.1 witness.1.2 sample := by
  rw [HasStrongSmallSetExpansion] at h
  push Not at h
  rcases h with ⟨S, hSmall, hExpansion⟩
  let T := checkSetNeighborhood sample S
  have hAvoids : AvoidsOutside S T sample := by
    rw [avoidsOutside_iff_neighborhood_subset]
  exact ⟨⟨(S, T), hSmall, hExpansion⟩, hAvoids⟩
end QEC.Coding.FiberBundle.RandomBase
