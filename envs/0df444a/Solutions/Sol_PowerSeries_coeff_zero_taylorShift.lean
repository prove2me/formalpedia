-- Prove2me | solution 1 for PowerSeries.coeff_zero_taylorShift
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.230386+00:00
-- url     : https://prove2.me/submissions/a313358e-f019-5427-b515-c6c43eb306d2

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_PowerSeries_coeff_zero_taylorShift

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 80000

namespace PowerSeries
p2m_export "PowerSeries" "coeff_mk mk C coeff"
p2m_open "PowerSeries"

variable {L : Type*} [NontriviallyNormedField L] [CompleteSpace L] [IsUltrametricDist L]

end PowerSeries

open _root_.PowerSeries _root_.P2MW.S_PowerSeries_coeff_zero_taylorShift.PowerSeries in

theorem solution {L : Type*} [NontriviallyNormedField L] [CompleteSpace L] [IsUltrametricDist L] (F : PowerSeries L) (a : L) :
    PowerSeries.coeff 0 (PowerSeries.mk fun n => ∑' k : ℕ,
        PowerSeries.coeff (n + k) F * ((n + k).choose n : L) * a ^ k)
      = ∑' k, PowerSeries.coeff k F * a ^ k := by
  rw [PowerSeries.coeff_mk]
  refine tsum_congr fun k => ?_
  simp

#print axioms solution

end S_PowerSeries_coeff_zero_taylorShift
end P2MW
export P2MW.S_PowerSeries_coeff_zero_taylorShift (solution)
