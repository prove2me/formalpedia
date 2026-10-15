-- Prove2me | solution 1 for TaoFivePrimes.rh_high_height_gamma_fft_array_bounds23
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-15T09:16:35.823994+00:00
-- url     : https://prove2.me/submissions/b30229de-d5cf-4291-9152-ea8f6f1dea05

import Mathlib
import Definitions.Def_TaoFivePrimes_RHHighFFTInputR23
import Definitions.Def_TaoFivePrimes_RHHighFFTInputI23
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false
theorem solution :
  ∀ rows∈[RHHighFFTInputR23.rows,RHHighFFTInputI23.rows],rows.flatten.length=16384 ∧ rows.all (fun row=>decide (row.length=512) && row.all (fun x=>decide (x≤2^167)))=true := by
  intro rows hr
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hr
  rcases hr with rfl|rfl <;> decide +kernel
