-- Prove2me | solution 1 for TaoFivePrimes.rh_high_height_gamma_fft_array_bounds02
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-15T07:06:55.001183+00:00
-- url     : https://prove2.me/submissions/4f5eb13d-a5f1-4fea-b99b-8d443ff2d4c4

import Mathlib
import Definitions.Def_TaoFivePrimes_RHHighFFTInputR02
import Definitions.Def_TaoFivePrimes_RHHighFFTInputI02
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false
theorem solution :
  ∀ rows∈[RHHighFFTInputR02.rows,RHHighFFTInputI02.rows],rows.flatten.length=16384 ∧ rows.all (fun row=>decide (row.length=512) && row.all (fun x=>decide (x≤2^167)))=true := by
  intro rows hr
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hr
  rcases hr with rfl|rfl <;> decide +kernel
