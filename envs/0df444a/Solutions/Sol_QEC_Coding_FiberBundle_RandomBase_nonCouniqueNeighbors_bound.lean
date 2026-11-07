-- Prove2me | solution 1 for QEC.Coding.FiberBundle.RandomBase.nonCouniqueNeighbors_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T06:26:59.01971+00:00
-- url     : https://prove2.me/submissions/56c4a218-c8c3-4b95-91ea-bfd3b588431f

import Definitions.Def_QEC_Coding_FiberBundle_RandomBase_Distance
import Definitions.Def_QEC_Coding_FiberBundle_RandomBase_Expansion
import Theorems.Thm_QEC_Coding_FiberBundle_RandomBase_card_neighborhood_add_nonCounique_le_selectedIncidenceCount
import Theorems.Thm_QEC_Coding_FiberBundle_RandomBase_selectedIncidenceCount_upper

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
    100 * (nonCouniqueNeighbors sample S).card ≤
      9 * Delta * S.card := by
  have hTokens :=
    card_neighborhood_add_nonCounique_le_selectedIncidenceCount sample S
  have hIncidence := selectedIncidenceCount_upper hDegree S
  have hNeighborhood := hExpansion S hSmall
  have hTokens100 := Nat.mul_le_mul_left 100 hTokens
  ring_nf at hTokens100 hIncidence hNeighborhood ⊢
  omega
end QEC.Coding.FiberBundle.RandomBase
