-- Prove2me | solution 1 for ThreeSum.LightColorIndex.color_lt
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T08:54:59.773835+00:00
-- url     : https://prove2.me/submissions/f6244df7-ac7b-421f-a0a9-965bebf3f799

import Definitions.Def_Submission_ThreeSum_LightMaskErase
import Definitions.Def_Submission_ThreeSum_MaskDecode
import Definitions.Def_Submission_ThreeSum_Coloring
import Definitions.Def_Submission_ThreeSum_LightColorIndex

set_option autoImplicit false
open ThreeSum ThreeSum.LightColorIndex
open Light LightSubsetAddress
variable {lim : Limits} {P : Program}
namespace ThreeSum.LightColorIndex
theorem _root_.solution {W : ℕ} (p : Coloring.Parameter W) (m : ℕ) : color p m < 3 :=
  (p.2 _).isLt
end ThreeSum.LightColorIndex
