-- Prove2me | solution 1 for QEC.Coding.FiberBundle.RandomBase.couniqueNeighbors_lower
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T06:29:20.106229+00:00
-- url     : https://prove2.me/submissions/810e12bc-2a22-4709-a22c-8d6f899c7f20

import Definitions.Def_QEC_Coding_FiberBundle_RandomBase_Distance
import Definitions.Def_QEC_Coding_FiberBundle_RandomBase_Expansion
import Theorems.Thm_QEC_Coding_FiberBundle_RandomBase_card_checkSetNeighborhood
import Theorems.Thm_QEC_Coding_FiberBundle_RandomBase_nonCouniqueNeighbors_bound

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.FiberBundle QEC.Coding.FiberBundle.RandomBase
open scoped BigOperators
namespace QEC.Coding.FiberBundle.RandomBase
theorem _root_.solution
    {r Delta : Nat} {sample : Sample r}
    (hDegree : HasDegreeWindows (Delta := Delta) sample)
    (hExpansion : HasStrongSmallSetExpansion (Delta := Delta) sample)
    (S : Finset (Fin (3 * r)))
    (hSmall : 100000 * Delta * S.card ≤ 3 * r) :
    83 * Delta * S.card ≤
      100 * (couniqueNeighbors sample S).card := by
  have hNeighborhood := hExpansion S hSmall
  have hNon := nonCouniqueNeighbors_bound hDegree hExpansion S hSmall
  rw [card_checkSetNeighborhood] at hNeighborhood
  ring_nf at hNeighborhood hNon ⊢
  omega
end QEC.Coding.FiberBundle.RandomBase
