-- Prove2me | solution 1 for QEC.Coding.FiberBundle.RandomBase.card_checkSetNeighborhood
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T05:47:04.572102+00:00
-- url     : https://prove2.me/submissions/1fecccc3-8038-4b21-a71b-7231de74d758

import Definitions.Def_QEC_Coding_FiberBundle_RandomBase_Distance
import Definitions.Def_QEC_Coding_FiberBundle_RandomBase_Expansion
import Theorems.Thm_QEC_Coding_FiberBundle_RandomBase_disjoint_couniqueNeighbors_nonCouniqueNeighbors
import Theorems.Thm_QEC_Coding_FiberBundle_RandomBase_checkSetNeighborhood_eq_union

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.FiberBundle QEC.Coding.FiberBundle.RandomBase
open scoped BigOperators
namespace QEC.Coding.FiberBundle.RandomBase
theorem _root_.solution
    {r : Nat} (sample : Sample r)
    (S : Finset (Fin (3 * r))) :
    (checkSetNeighborhood sample S).card =
      (couniqueNeighbors sample S).card +
        (nonCouniqueNeighbors sample S).card := by
  rw [checkSetNeighborhood_eq_union]
  exact Finset.card_union_of_disjoint
    (disjoint_couniqueNeighbors_nonCouniqueNeighbors sample S)
end QEC.Coding.FiberBundle.RandomBase
