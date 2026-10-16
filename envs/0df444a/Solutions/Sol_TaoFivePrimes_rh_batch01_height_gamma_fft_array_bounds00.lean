-- Prove2me | solution 1 for TaoFivePrimes.rh_batch01_height_gamma_fft_array_bounds00
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-15T20:42:40.001069+00:00
-- url     : https://prove2.me/submissions/3691f828-d274-4a66-8dc3-a29d291b7f76

import Mathlib
import Definitions.Def_TaoFivePrimes_RHBatch01FFTInputR00
import Definitions.Def_TaoFivePrimes_RHBatch01FFTInputI00
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false
theorem solution :
  ∀ rows∈[RHBatch01FFTInputR00.rows,RHBatch01FFTInputI00.rows],rows.flatten.length=16384 ∧ rows.all (fun row=>decide (row.length=512) && row.all (fun x=>decide (x≤2^167)))=true := by
  intro rows hr
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hr
  rcases hr with rfl|rfl <;> decide +kernel
#print axioms solution
