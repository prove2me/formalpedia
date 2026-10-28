-- Prove2me | solution 1 for TaoFivePrimes.rh_direct_132_gamma_cached_lookup
-- status  : ACCEPTED   (prove)
-- author  : @Johan Mercedes
-- created : 2026-10-28T00:38:37.380247+00:00
-- url     : https://prove2.me/submissions/a4a290c7-032a-418e-aba0-f92afdebfa6e

import Definitions.Def_TaoFivePrimes_RHDirect132CachedRule
import Definitions.Def_TaoFivePrimes_RHDirect132Integer
import Mathlib
import Theorems.Thm_TaoFivePrimes_rh_direct_132_gamma_panel_0
import Theorems.Thm_TaoFivePrimes_rh_direct_132_gamma_panel_1
import Theorems.Thm_TaoFivePrimes_rh_direct_132_gamma_panel_2
import Theorems.Thm_TaoFivePrimes_rh_direct_132_gamma_panel_3
import Theorems.Thm_TaoFivePrimes_rh_direct_132_gamma_panel_4
import Theorems.Thm_TaoFivePrimes_rh_direct_132_gamma_panel_5
import Theorems.Thm_TaoFivePrimes_rh_direct_132_gamma_panel_6
import Theorems.Thm_TaoFivePrimes_rh_direct_132_gamma_panel_7
import Theorems.Thm_TaoFivePrimes_rh_direct_132_gamma_panel_8
import Theorems.Thm_TaoFivePrimes_rh_direct_132_gamma_panel_9
import Theorems.Thm_TaoFivePrimes_rh_direct_132_gamma_panel_10
import Theorems.Thm_TaoFivePrimes_rh_direct_132_gamma_panel_11
import Theorems.Thm_TaoFivePrimes_rh_direct_132_gamma_panel_12
import Theorems.Thm_TaoFivePrimes_rh_direct_132_gamma_panel_13
import Theorems.Thm_TaoFivePrimes_rh_direct_132_gamma_panel_14
import Theorems.Thm_TaoFivePrimes_rh_direct_132_gamma_panel_15
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open Finset

theorem solution (i m : ℕ) (hi : i<16) (hm : m<60) :
    RHDirect132CachedRule.gamma i m =
      (RHDirect132Integer.gammaRe i m, RHDirect132Integer.gammaIm i m) := by
  interval_cases i
  · exact (TaoFivePrimes.rh_direct_132_gamma_panel_0 ⟨m,hm⟩).symm
  · exact (TaoFivePrimes.rh_direct_132_gamma_panel_1 ⟨m,hm⟩).symm
  · exact (TaoFivePrimes.rh_direct_132_gamma_panel_2 ⟨m,hm⟩).symm
  · exact (TaoFivePrimes.rh_direct_132_gamma_panel_3 ⟨m,hm⟩).symm
  · exact (TaoFivePrimes.rh_direct_132_gamma_panel_4 ⟨m,hm⟩).symm
  · exact (TaoFivePrimes.rh_direct_132_gamma_panel_5 ⟨m,hm⟩).symm
  · exact (TaoFivePrimes.rh_direct_132_gamma_panel_6 ⟨m,hm⟩).symm
  · exact (TaoFivePrimes.rh_direct_132_gamma_panel_7 ⟨m,hm⟩).symm
  · exact (TaoFivePrimes.rh_direct_132_gamma_panel_8 ⟨m,hm⟩).symm
  · exact (TaoFivePrimes.rh_direct_132_gamma_panel_9 ⟨m,hm⟩).symm
  · exact (TaoFivePrimes.rh_direct_132_gamma_panel_10 ⟨m,hm⟩).symm
  · exact (TaoFivePrimes.rh_direct_132_gamma_panel_11 ⟨m,hm⟩).symm
  · exact (TaoFivePrimes.rh_direct_132_gamma_panel_12 ⟨m,hm⟩).symm
  · exact (TaoFivePrimes.rh_direct_132_gamma_panel_13 ⟨m,hm⟩).symm
  · exact (TaoFivePrimes.rh_direct_132_gamma_panel_14 ⟨m,hm⟩).symm
  · exact (TaoFivePrimes.rh_direct_132_gamma_panel_15 ⟨m,hm⟩).symm
