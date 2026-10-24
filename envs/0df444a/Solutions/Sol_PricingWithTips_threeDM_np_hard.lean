-- Prove2me | solution 1 for PricingWithTips.threeDM_np_hard
-- status  : ACCEPTED   (prove)
-- author  : @qmaai2907271020
-- created : 2026-10-23T13:09:49.622648+00:00
-- url     : https://prove2.me/submissions/a271d8e0-e454-418e-a50d-81b8e0745276

import Definitions.Def_PricingWithTips_NPHardness
import Definitions.Def_PricingWithTips3DM_d3580fa66ff8cd5440556f0f

theorem solution :
    PricingWithTips.NPHardMarketPredicate PricingWithTips.ThreeDMYes := by
  exact PricingWithTips.FixedShapeReductionTM2.threeDM_np_hard
