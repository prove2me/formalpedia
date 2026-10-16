-- Prove2me | solution 1 for TaoFivePrimes.rh_batch01_height_gamma_fft_array_bounds04
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-16T08:51:22.936479+00:00
-- url     : https://prove2.me/submissions/f5e15820-efb3-437d-9ce2-d55e14d1adbf

import Mathlib
import Definitions.Def_TaoFivePrimes_RHBatch01FFTInputR04
import Definitions.Def_TaoFivePrimes_RHBatch01FFTInputI04
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false
theorem solution :
  ∀ rows∈[RHBatch01FFTInputR04.rows,RHBatch01FFTInputI04.rows],rows.flatten.length=16384 ∧ rows.all (fun row=>decide (row.length=512) && row.all (fun x=>decide (x≤2^167)))=true := by
  intro rows hr
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hr
  rcases hr with rfl|rfl <;> decide +kernel
#print axioms solution
