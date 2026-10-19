-- Prove2me | solution 1 for PermanentRollout.sourceBlockAlpha_algebraMap
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:10.343013+00:00
-- url     : https://prove2.me/submissions/0e2bece3-8181-4207-b3c5-e834aef3236c

import Mathlib
import Definitions.Def_Permanent

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 100000
open PermanentRollout
open scoped BigOperators
namespace PermanentRollout
theorem _root_.solution
    {R : Type*} [CommSemiring R] [Algebra ℂ R]
    {r d : ℕ} (U : Matrix (Fin r) (Fin (r - d)) ℂ)
    (omitted : Finset (Fin r)) :
    sourceBlockAlpha r d
        (fun row column => algebraMap ℂ R (U row column)) omitted =
      algebraMap ℂ R (sourceBlockAlpha r d U omitted) := by
  classical
  simp [sourceBlockAlpha, map_sum, map_prod]
end PermanentRollout
