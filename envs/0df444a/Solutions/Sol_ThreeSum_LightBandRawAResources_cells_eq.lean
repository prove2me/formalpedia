-- Prove2me | solution 1 for ThreeSum.LightBandRawAResources.cells_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:01:51.472511+00:00
-- url     : https://prove2.me/submissions/20c2d7af-5e74-43ac-806c-4ed72b2d8f70

import Definitions.Def_Submission_ThreeSum_EncodedColorLayout
import Definitions.Def_Submission_ThreeSum_LightBandRawAResources
import Theorems.Thm_Light_MatAt_congr
import Theorems.Thm_Light_Seg_congr
import Theorems.Thm_ThreeSum_LightKaratsuba_ProductAt_congr
set_option autoImplicit false
open ThreeSum ThreeSum.LightBandRawAResources
open Light EncodedColorLayout
set_option maxHeartbeats 1800000
set_option maxRecDepth 12000
namespace ThreeSum.LightBandRawAResources
theorem _root_.solution (W n g : ℕ) :
    cells W n g =
      max (19 + 14 * n + ColorBandBounds.count n g + ColorBandBounds.width n g + W)
        (17 + 13 * n + 5 * ColorBandBounds.count n g + 3 * g * ColorBandBounds.count n g) :=
  by
  unfold cells LightBandRawAColor.space LightColorBands.space ColorBandBounds.space LightBandRawA.space
    LightBandRawA.positionBase LightBandRawA.ownerBase LightBandRawA.capacity vals rec tables ce cv be bv ae av class2
    class1 class0 colors
  congr 1 <;> ring
end ThreeSum.LightBandRawAResources
