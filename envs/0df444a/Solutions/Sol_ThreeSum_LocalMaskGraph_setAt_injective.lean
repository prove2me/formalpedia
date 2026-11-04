-- Prove2me | solution 1 for ThreeSum.LocalMaskGraph.setAt_injective
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T09:18:51.531875+00:00
-- url     : https://prove2.me/submissions/e2469da8-b685-4b26-a36e-8d869ce03cd0

import Definitions.Def_Submission_ThreeSum_LightMaskBits
import Definitions.Def_Submission_ThreeSum_LightBooleanDot
import Definitions.Def_Submission_ThreeSum_LocalGraph
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Definitions.Def_Submission_ThreeSum_LocalMaskGraph
import Theorems.Thm_ThreeSum_LocalMaskGraph_subsetMask_setAt
import Theorems.Thm_ThreeSum_LocalMaskGraph_maskAt_injective

set_option autoImplicit false
open ThreeSum ThreeSum.LocalMaskGraph
open Finset SubsetAddress MaskDecode
open scoped BigOperators
namespace ThreeSum.LocalMaskGraph
theorem _root_.solution {L h i j : ℕ} (hi : i < vertexCount L h) (hj : j < vertexCount L h)
    (he : setAt L h i = setAt L h j) : i=j := by
  apply maskAt_injective hi hj
  rw [← subsetMask_setAt hi,← subsetMask_setAt hj,he]
end ThreeSum.LocalMaskGraph
