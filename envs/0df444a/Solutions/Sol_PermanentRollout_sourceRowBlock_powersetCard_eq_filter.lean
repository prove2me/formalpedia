-- Prove2me | solution 1 for PermanentRollout.sourceRowBlock_powersetCard_eq_filter
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:10.343013+00:00
-- url     : https://prove2.me/submissions/d0be715f-44d3-4cd2-afde-7d7459e0402c

import Mathlib
import Definitions.Def_Permanent

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 100000
open PermanentRollout
open scoped BigOperators
namespace PermanentRollout
theorem _root_.solution
    (b t d : ℕ) (h : Fin b) :
    (sourceRowBlock b t h).powersetCard d =
      ((Finset.univ : Finset (Fin (b * t))).powersetCard d).filter
        (fun omitted => omitted ⊆ sourceRowBlock b t h) := by
  classical
  ext omitted
  simp [Finset.mem_powersetCard, and_comm]
end PermanentRollout
