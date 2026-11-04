-- Prove2me | solution 1 for ThreeSum.EncodedColorLayout.free_le_normalizedEnd
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T10:03:45.416102+00:00
-- url     : https://prove2.me/submissions/adbefe70-f65c-40ec-b50c-a4ed593e8f8d

import Definitions.Def_Submission_ThreeSum_EncodedColorPrimeData
import Definitions.Def_Submission_ThreeSum_LightBandRawAColor
import Definitions.Def_Submission_ThreeSum_EncodedColorLayout

set_option autoImplicit false
open ThreeSum ThreeSum.EncodedColorLayout
namespace ThreeSum.EncodedColorLayout
theorem _root_.solution (free n g : ℕ) : free+8 ≤ normalizedEnd free n g := by
  unfold normalizedEnd LightBandRawA.space LightBandRawA.positionBase LightBandRawA.ownerBase
    LightBandRawA.capacity vals rec tables ce cv be bv ae av class2 class1 class0 colors
  omega
end ThreeSum.EncodedColorLayout
