-- Prove2me | solution 1 for TaoFivePrimes.rh_high_height_gamma_fft_array_bounds11
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-15T08:18:08.231318+00:00
-- url     : https://prove2.me/submissions/97876ab3-f70e-418f-9f44-defcc4a52bc1

import Mathlib
import Definitions.Def_TaoFivePrimes_RHHighFFTInputR11
import Definitions.Def_TaoFivePrimes_RHHighFFTInputI11
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false
theorem solution :
  ∀ rows∈[RHHighFFTInputR11.rows,RHHighFFTInputI11.rows],rows.flatten.length=16384 ∧ rows.all (fun row=>decide (row.length=512) && row.all (fun x=>decide (x≤2^167)))=true := by
  intro rows hr
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hr
  rcases hr with rfl|rfl <;> decide +kernel
