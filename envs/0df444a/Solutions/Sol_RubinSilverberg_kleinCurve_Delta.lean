-- Prove2me | solution 1 for RubinSilverberg.kleinCurve_Delta
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.503601+00:00
-- url     : https://prove2.me/submissions/b3e8ef6f-b1f9-5f11-9190-b6327ec9297f

import Definitions.Def_EllipticCurve_RubinSilverbergFamily
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_RubinSilverberg_kleinCurve_Delta

open RubinSilverberg

theorem solution {K : Type*} [Field K] [CharZero K] (u : K) : (kleinCurve u).Δ = -kleinV u ^ 5 := by
  simp only [kleinCurve, WeierstrassCurve.Δ, WeierstrassCurve.b₂, WeierstrassCurve.b₄,
    WeierstrassCurve.b₆, WeierstrassCurve.b₈, kleinH, kleinT, kleinV]
  field_simp
  ring

end S_RubinSilverberg_kleinCurve_Delta
end P2MW
export P2MW.S_RubinSilverberg_kleinCurve_Delta (solution)
