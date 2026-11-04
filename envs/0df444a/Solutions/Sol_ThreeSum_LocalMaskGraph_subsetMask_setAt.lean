-- Prove2me | solution 1 for ThreeSum.LocalMaskGraph.subsetMask_setAt
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T09:03:43.890219+00:00
-- url     : https://prove2.me/submissions/fc232ef5-c080-4544-935c-db4c59078726

import Definitions.Def_Submission_ThreeSum_LightMaskBits
import Definitions.Def_Submission_ThreeSum_LightBooleanDot
import Definitions.Def_Submission_ThreeSum_LocalGraph
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Definitions.Def_Submission_ThreeSum_LocalMaskGraph
import Theorems.Thm_ThreeSum_LocalMaskGraph_maskAt_spec
import Theorems.Thm_ThreeSum_MaskDecode_subsetMask_decode


set_option autoImplicit false
open ThreeSum ThreeSum.LocalMaskGraph
open Finset SubsetAddress MaskDecode
open scoped BigOperators
namespace ThreeSum.LocalMaskGraph
theorem _root_.solution {L h i : ℕ} (hi : i < vertexCount L h) :
    subsetMask (setAt L h i) = maskAt L h i := subsetMask_decode (maskAt_spec hi).1
end ThreeSum.LocalMaskGraph
