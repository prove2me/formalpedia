-- Prove2me | solution 1 for ThreeSum.LocalMaskGraph.indexed_dot_zero_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T09:22:39.522107+00:00
-- url     : https://prove2.me/submissions/ab172678-2e9b-4477-b1ae-9d5b8531bddb

import Definitions.Def_Submission_ThreeSum_LightMaskBits
import Definitions.Def_Submission_ThreeSum_LightBooleanDot
import Definitions.Def_Submission_ThreeSum_LocalGraph
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Definitions.Def_Submission_ThreeSum_LocalMaskGraph
import Theorems.Thm_ThreeSum_LocalMaskGraph_subsetMask_setAt
import Theorems.Thm_ThreeSum_LocalMaskGraph_dot_zero_iff

set_option autoImplicit false
open ThreeSum ThreeSum.LocalMaskGraph
open Finset SubsetAddress MaskDecode
open scoped BigOperators
namespace ThreeSum.LocalMaskGraph
theorem _root_.solution {L h i j : ℕ}
    (hi : i < vertexCount L h) (hj : j < vertexCount L h) :
    LightBooleanDot.dot (LightMaskBits.bit L (maskAt L h i))
      (LightMaskBits.bit L (maskAt L h j)) L = 0 ↔ Disjoint (setAt L h i) (setAt L h j) := by
  rw [← subsetMask_setAt hi,← subsetMask_setAt hj]
  exact dot_zero_iff _ _
end ThreeSum.LocalMaskGraph
