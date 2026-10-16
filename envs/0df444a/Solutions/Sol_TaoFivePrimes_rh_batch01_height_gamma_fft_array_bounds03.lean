-- Prove2me | solution 1 for TaoFivePrimes.rh_batch01_height_gamma_fft_array_bounds03
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-15T23:32:00.093004+00:00
-- url     : https://prove2.me/submissions/8bac5e48-227e-4988-95fa-45de6ea75d92

import Mathlib
import Definitions.Def_TaoFivePrimes_RHBatch01FFTInputR03
import Definitions.Def_TaoFivePrimes_RHBatch01FFTInputI03
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false
theorem solution :
  ∀ rows∈[RHBatch01FFTInputR03.rows,RHBatch01FFTInputI03.rows],rows.flatten.length=16384 ∧ rows.all (fun row=>decide (row.length=512) && row.all (fun x=>decide (x≤2^167)))=true := by
  intro rows hr
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hr
  rcases hr with rfl|rfl <;> decide +kernel
#print axioms solution
