-- Prove2me | solution 1 for TaoFivePrimes.rh_high_height_gamma_fft_array_bounds21
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-15T09:05:27.649988+00:00
-- url     : https://prove2.me/submissions/e5323c85-49e4-411f-9371-d6c67aefd974

import Mathlib
import Definitions.Def_TaoFivePrimes_RHHighFFTInputR21
import Definitions.Def_TaoFivePrimes_RHHighFFTInputI21
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false
theorem solution :
  ∀ rows∈[RHHighFFTInputR21.rows,RHHighFFTInputI21.rows],rows.flatten.length=16384 ∧ rows.all (fun row=>decide (row.length=512) && row.all (fun x=>decide (x≤2^167)))=true := by
  intro rows hr
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hr
  rcases hr with rfl|rfl <;> decide +kernel
