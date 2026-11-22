-- Prove2me | solution 1 for Polychromatic418967fa.chainBoundary289
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T21:35:09.55008+00:00
-- url     : https://prove2.me/submissions/bb1787dd-f6d6-41a7-a0f3-9ef6d8ac9bfa

import Definitions.Def_Polychromatic418967fa_Branch279
import Definitions.Def_Polychromatic418967fa_Branch280
import Definitions.Def_Polychromatic418967fa_Branch281
import Definitions.Def_Polychromatic418967fa_Branch282
import Definitions.Def_Polychromatic418967fa_Branch283
import Definitions.Def_Polychromatic418967fa_Branch284
import Definitions.Def_Polychromatic418967fa_Branch285
import Definitions.Def_Polychromatic418967fa_Branch286
import Definitions.Def_Polychromatic418967fa_Branch287
import Definitions.Def_Polychromatic418967fa_Branch288
import Theorems.Thm_Polychromatic418967fa_chainBoundary279
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem solution : allC 289 :=
(allC_succ 288 Polychromatic418967fa.branch_288 (allC_succ 287 Polychromatic418967fa.branch_287 (allC_succ 286 Polychromatic418967fa.branch_286 (allC_succ 285 Polychromatic418967fa.branch_285 (allC_succ 284 Polychromatic418967fa.branch_284 (allC_succ 283 Polychromatic418967fa.branch_283 (allC_succ 282 Polychromatic418967fa.branch_282 (allC_succ 281 Polychromatic418967fa.branch_281 (allC_succ 280 Polychromatic418967fa.branch_280 (allC_succ 279 Polychromatic418967fa.branch_279 Polychromatic418967fa.chainBoundary279))))))))))
