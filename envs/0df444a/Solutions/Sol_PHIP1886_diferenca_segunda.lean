-- Prove2me | solution 1 for PHIP1886.diferenca_segunda
-- status  : ACCEPTED   (prove)
-- author  : @bueno_ricardo
-- created : 2026-11-15T19:11:00.531485+00:00
-- url     : https://prove2.me/submissions/7126d1f2-0c47-4161-9a2c-a013a5cd2265

import Mathlib
import Definitions.Def_RHPF28_PHIP1886_559e0c85eff3
open MeasureTheory Set
open PHIP1886

theorem solution (h t u : Int) (hh : 0 ≤ h) :
    ramp (t + h) u - 2 * ramp t u + ramp (t - h) u = hat h (t - u) := by
  unfold ramp hat; omega
