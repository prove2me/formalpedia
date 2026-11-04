-- Prove2me | solution 1 for ThreeSum.LocalMaskGraph.setAt_card
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T09:00:58.594214+00:00
-- url     : https://prove2.me/submissions/e61a48b7-5678-40fe-9d51-ce9b6ea86eae

import Definitions.Def_Submission_ThreeSum_LightMaskBits
import Definitions.Def_Submission_ThreeSum_LightBooleanDot
import Definitions.Def_Submission_ThreeSum_LocalGraph
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Definitions.Def_Submission_ThreeSum_LocalMaskGraph
import Theorems.Thm_ThreeSum_LocalMaskGraph_maskAt_mem
import Theorems.Thm_ThreeSum_MaskDecode_decode_card_layer


set_option autoImplicit false
open ThreeSum ThreeSum.LocalMaskGraph
open Finset SubsetAddress MaskDecode
open scoped BigOperators
namespace ThreeSum.LocalMaskGraph
theorem _root_.solution {L h i : ℕ} (hi : i < vertexCount L h) : (setAt L h i).card = h :=
  decode_card_layer (maskAt_mem hi)
end ThreeSum.LocalMaskGraph
