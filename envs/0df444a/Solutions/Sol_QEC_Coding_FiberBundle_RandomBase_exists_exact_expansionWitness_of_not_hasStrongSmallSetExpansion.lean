-- Prove2me | solution 1 for QEC.Coding.FiberBundle.RandomBase.exists_exact_expansionWitness_of_not_hasStrongSmallSetExpansion
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T07:53:18.976222+00:00
-- url     : https://prove2.me/submissions/118c9ee2-8bd1-42e0-8812-ecc636281a57

import Definitions.Def_QEC_Coding_FiberBundle_RandomBase_Expansion
import Definitions.Def_QEC_Coding_FiberBundle_RandomBase_ExpansionProbability

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.FiberBundle QEC.Coding.FiberBundle.RandomBase
open scoped BigOperators
open MeasureTheory
namespace QEC.Coding.FiberBundle.RandomBase
theorem _root_.solution
    {r Delta : Nat} {sample : Sample r}
    (h : ¬HasStrongSmallSetExpansion (Delta := Delta) sample) :
    ∃ witness : ExpansionWitness r Delta,
      checkSetNeighborhood sample witness.1.1 = witness.1.2 := by
  rw [HasStrongSmallSetExpansion] at h
  push Not at h
  rcases h with ⟨S, hSmall, hExpansion⟩
  exact
    ⟨⟨(S, checkSetNeighborhood sample S), hSmall, hExpansion⟩, rfl⟩
end QEC.Coding.FiberBundle.RandomBase
