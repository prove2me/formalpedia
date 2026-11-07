-- Prove2me | solution 1 for QEC.Coding.FiberBundle.RandomBase.exists_check_four_fifths_counique
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T06:33:50.300484+00:00
-- url     : https://prove2.me/submissions/fcfc1d31-091a-4558-9bfc-025dfeeb1e99

import Definitions.Def_QEC_Coding_FiberBundle_RandomBase_Distance
import Definitions.Def_QEC_Coding_FiberBundle_RandomBase_Expansion
import Theorems.Thm_QEC_Coding_FiberBundle_RandomBase_exists_check_many_couniqueNeighbors

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.FiberBundle QEC.Coding.FiberBundle.RandomBase
open scoped BigOperators
namespace QEC.Coding.FiberBundle.RandomBase
theorem _root_.solution
    {r Delta : Nat} {sample : Sample r}
    (hDelta : 0 < Delta)
    (hDegree : HasDegreeWindows (Delta := Delta) sample)
    (hExpansion : HasStrongSmallSetExpansion (Delta := Delta) sample)
    (S : Finset (Fin (3 * r))) (hS : S.Nonempty)
    (hSmall : 100000 * Delta * S.card ≤ 3 * r) :
    ∃ a ∈ S,
      4 * checkDegree sample a < 5 * couniqueDegree sample S a := by
  rcases exists_check_many_couniqueNeighbors
      hDelta hDegree hExpansion S hS hSmall with
    ⟨a, haS, haCounique⟩
  refine ⟨a, haS, ?_⟩
  have haDegree := (hDegree.1 a).2
  ring_nf at haDegree haCounique ⊢
  nlinarith
end QEC.Coding.FiberBundle.RandomBase
