-- Prove2me | solution 1 for ThreeSum.OutputKeyMasks.indexed_blockKey
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:28:27.626807+00:00
-- url     : https://prove2.me/submissions/b210b8f7-6c80-4b96-aefd-e226bab4d8fb

import Definitions.Def_Submission_ThreeSum_GlobalKeyEnumeration
import Definitions.Def_Submission_ThreeSum_BlockCoefficientRows
import Definitions.Def_Submission_ThreeSum_OutputKeyMasks
import Theorems.Thm_ThreeSum_OutputKeyMasks_eval_difference
import Theorems.Thm_ThreeSum_OutputKeyMasks_mapRow_eq
import Theorems.Thm_ThreeSum_LocalMaskGraph_subsetMask_setAt


set_option autoImplicit false
open ThreeSum ThreeSum.OutputKeyMasks
open GlobalEncoding LocalHashMoments LocalCoverBounds
open OneHotMask SubsetAddress
open scoped BigOperators
namespace ThreeSum.OutputKeyMasks
theorem _root_.solution {h : ℕ} (o : Occurrence h)
    (i : Fin ((512*h).choose (2*h))) :
    (eval (BlockCoefficientRows.mapRow h true o.val) (fun _ => 0) (512*h)
      (LocalMaskGraph.maskAt (512*h) (2*h) i.val) : ℤ)-
      (eval (BlockCoefficientRows.mapRow h false o.val) (fun _ => 0) (512*h)
      (LocalMaskGraph.maskAt (512*h) (2*h) i.val) : ℤ) =
      blockKey (o,GlobalKeyEnumeration.layerRecord h i) := by
  rw [mapRow_eq,mapRow_eq,← LocalMaskGraph.subsetMask_setAt i.isLt,eval_difference]
  rfl
end ThreeSum.OutputKeyMasks
