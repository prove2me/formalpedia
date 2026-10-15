-- Prove2me | solution 1 for TaoFivePrimes.rh_high_height_gamma_fft_array_bounds16
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-15T08:37:15.856626+00:00
-- url     : https://prove2.me/submissions/9237c320-c5db-4486-87ca-96c53cf6cd0c

import Mathlib
import Definitions.Def_TaoFivePrimes_RHHighFFTInputR16
import Definitions.Def_TaoFivePrimes_RHHighFFTInputI16
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false
theorem solution :
  ∀ rows∈[RHHighFFTInputR16.rows,RHHighFFTInputI16.rows],rows.flatten.length=16384 ∧ rows.all (fun row=>decide (row.length=512) && row.all (fun x=>decide (x≤2^167)))=true := by
  intro rows hr
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hr
  rcases hr with rfl|rfl <;> decide +kernel
