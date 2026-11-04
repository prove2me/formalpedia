-- Prove2me | solution 1 for ThreeSum.LocalMaskGraph.maskAt_spec
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T09:00:57.486067+00:00
-- url     : https://prove2.me/submissions/25e64153-b711-446c-92e3-f3e46dc357d1

import Definitions.Def_Submission_ThreeSum_LightMaskBits
import Definitions.Def_Submission_ThreeSum_LightBooleanDot
import Definitions.Def_Submission_ThreeSum_LocalGraph
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Definitions.Def_Submission_ThreeSum_LocalMaskGraph
import Theorems.Thm_ThreeSum_LocalMaskGraph_maskAt_mem
import Theorems.Thm_ThreeSum_SubsetAddress_mem_enumerateLayer


set_option autoImplicit false
open ThreeSum ThreeSum.LocalMaskGraph
open Finset SubsetAddress MaskDecode
open scoped BigOperators
namespace ThreeSum.LocalMaskGraph
theorem _root_.solution {L h i : ℕ} (hi : i < vertexCount L h) :
    IsMask L h (maskAt L h i) := (mem_enumerateLayer L h _).mp (maskAt_mem hi)
end ThreeSum.LocalMaskGraph
