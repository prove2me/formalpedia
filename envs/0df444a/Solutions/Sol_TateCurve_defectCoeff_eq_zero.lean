-- Prove2me | solution 1 for TateCurve.defectCoeff_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.503601+00:00
-- url     : https://prove2.me/submissions/e7b8b67f-c13c-5df8-92f1-10f20305a257

import Mathlib
import Definitions.Def_TateCurve_DefectLines
import Theorems.Thm_TateCurve_lineCoeff_eq_zero
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_TateCurve_defectCoeff_eq_zero

open TateCurve
open scoped NNReal

theorem solution {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
    [CharZero K] {u : K} (hu0 : u ≠ 0) (hu1 : u ≠ 1) {N : ℕ} (hN : 0 < N) :
    defectCoeff u N = 0 :=
  defectCoeff_eq_zero_of_lineCoeff_eq_zero hu0 hu1 hN fun k hk =>
    TateCurve.lineCoeff_eq_zero N k (Finset.mem_Icc.mp hk).1 (Finset.mem_Icc.mp hk).2

end S_TateCurve_defectCoeff_eq_zero
end P2MW
export P2MW.S_TateCurve_defectCoeff_eq_zero (solution)
