-- Prove2me | solution 1 for ThreeSum.LightBandRawAResources.space_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T10:02:10.74221+00:00
-- url     : https://prove2.me/submissions/f6441185-f29e-49fb-aa95-157ed333b2ed

import Definitions.Def_Submission_ThreeSum_EncodedColorLayout
import Definitions.Def_Submission_ThreeSum_LightBandRawAResources
set_option autoImplicit false
open ThreeSum ThreeSum.LightBandRawAResources
open Light EncodedColorLayout
set_option maxHeartbeats 1800000
set_option maxRecDepth 12000
namespace ThreeSum.LightBandRawAResources
theorem _root_.solution (free W n g : ℕ) :
    LightBandRawAColor.space (tables free n) (vals free n g) W n g = free + cells W n g :=
  by
  unfold cells LightBandRawAColor.space LightColorBands.space ColorBandBounds.space LightBandRawA.space
    LightBandRawA.positionBase LightBandRawA.ownerBase LightBandRawA.capacity vals rec tables ce cv be bv ae av class2
    class1 class0 colors
  omega
end ThreeSum.LightBandRawAResources
