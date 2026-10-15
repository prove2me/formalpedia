-- Prove2me | solution 1 for TaoFivePrimes.rh_high_height_gamma_fft_array_bounds25
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-15T09:26:44.251015+00:00
-- url     : https://prove2.me/submissions/cf29dedd-2567-43e7-86e8-4ce35b21e710

import Mathlib
import Definitions.Def_TaoFivePrimes_RHHighFFTInputR25
import Definitions.Def_TaoFivePrimes_RHHighFFTInputI25
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false
theorem solution :
  ∀ rows∈[RHHighFFTInputR25.rows,RHHighFFTInputI25.rows],rows.flatten.length=16384 ∧ rows.all (fun row=>decide (row.length=512) && row.all (fun x=>decide (x≤2^167)))=true := by
  intro rows hr
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hr
  rcases hr with rfl|rfl <;> decide +kernel
