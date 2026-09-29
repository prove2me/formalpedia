-- Prove2me | solution 1 for RubinSilverberg.rsBeta_sub_mul_rsGamma
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.503601+00:00
-- url     : https://prove2.me/submissions/f3b74ffb-5a4d-55ab-97e2-23ea21a0e7b0

import Definitions.Def_EllipticCurve_RubinSilverbergFamily
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_RubinSilverberg_rsBeta_sub_mul_rsGamma

open RubinSilverberg

theorem solution {K : Type*} [Field K] (u : K) (hu : u ≠ 0) (hf : u ^ 10 + 11 * u ^ 5 - 1 ≠ 0) : rsBeta u - u * rsGamma u = -(kleinT u * kleinH u) / (144 * u ^ 4 * (u ^ 10 + 11 * u ^ 5 - 1) ^ 4) := by
  have _h := hf
  unfold rsBeta rsGamma kleinH
  field_simp
  ring

end S_RubinSilverberg_rsBeta_sub_mul_rsGamma
end P2MW
export P2MW.S_RubinSilverberg_rsBeta_sub_mul_rsGamma (solution)
