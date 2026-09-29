-- Prove2me | solution 1 for TateCurve.nnnorm_twistParam_curve_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.503601+00:00
-- url     : https://prove2.me/submissions/32b4ee96-80cf-5081-ac18-9152bc8d8414

import Definitions.Def_TateCurve_QSeries
import Theorems.Thm_WeierstrassCurve_nnnorm_twistParam_eq_one
import Theorems.Thm_TateCurve_nnnorm_c4
import Theorems.Thm_TateCurve_nnnorm_Delta
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_TateCurve_nnnorm_twistParam_curve_eq_one

open scoped NNReal
open TateCurve

theorem solution {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
    (E : WeierstrassCurve K)
    (hc₄ : ‖E.c₄‖₊ = 1) (hΔ : ‖E.Δ‖₊ < 1) {q : K} (hq0 : q ≠ 0) (hq : ‖q‖₊ < 1) :
    ‖E.c₆ * (curve q).c₄ / ((curve q).c₆ * E.c₄)‖₊ = 1 :=
  WeierstrassCurve.nnnorm_twistParam_eq_one E (curve q) hc₄ hΔ (TateCurve.nnnorm_c4 hq)
    (by rw [TateCurve.nnnorm_Delta hq0 hq]; exact hq)

end S_TateCurve_nnnorm_twistParam_curve_eq_one
end P2MW
export P2MW.S_TateCurve_nnnorm_twistParam_curve_eq_one (solution)
