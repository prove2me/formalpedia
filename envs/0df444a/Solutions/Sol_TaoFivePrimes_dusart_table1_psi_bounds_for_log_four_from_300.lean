-- Prove2me | solution 1 for TaoFivePrimes.dusart_table1_psi_bounds_for_log_four_from_300
-- status  : ACCEPTED   (prove)
-- author  : @abcdefg
-- created : 2026-10-18T13:40:02.706152+00:00
-- url     : https://prove2.me/submissions/8a11ef1f-ac8b-47ec-9a55-d0ebe33c1d6d

import Definitions.Def_DusartTable1ZeroRanges_433_20261018
import Theorems.Thm_ExplicitPNT_dusart_refined_psi_error_of_zero_free_region
import Theorems.Thm_ExplicitPNT_kadiri_zero_free_region_569693
import Definitions.Def_DusartThetaTable1Intervals
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Tactic
import Definitions.Def_PNT_Kadiri_HeckeBridge_433_0010
import Theorems.Thm_OAI_SevenEighths_HeckeFamily_LFunction_ne_zero_of_seven_eighths_lt_re
import Theorems.Thm_TaoFivePrimes_zeta_ne_zero_strip_im_two_to_fourteen
import Theorems.Thm_TaoFivePrimes_rh_verified_block_14_1e2
import Definitions.Def_dusart_psi_433_20261014_PsiZeroSum
import Definitions.Def_dusart_psi_433_20261014_PsiComparison
import Theorems.Thm_ExplicitPNT_DusartTable1_Modules_TableMiddleRows

set_option autoImplicit false
set_option maxHeartbeats 1000000
open ExplicitPNT.DusartTable1

theorem solution :
∀ (r : DusartThetaTable.Row) (hr : r ∈ DusartThetaTable.rows)
    (hb : 300 ≤ r.b) (x : ℝ) (hx : Real.exp (r.b : ℝ) ≤ x),
    |Chebyshev.psi x - x| ≤ (r.epsilon : ℝ) * x :=
  ExplicitPNT.DusartTable1.Modules.TableMiddleRows.2.2.2.2.1
