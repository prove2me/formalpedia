-- Prove2me | solution 1 for TaoFivePrimes.rh_batch01_height_gamma_fft_array_bounds07
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-16T13:04:02.846097+00:00
-- url     : https://prove2.me/submissions/59fcbdb0-ec45-4409-ba85-838519def07e

import Mathlib
import Definitions.Def_TaoFivePrimes_RHBatch01FFTInputR07
import Definitions.Def_TaoFivePrimes_RHBatch01FFTInputI07
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false
theorem solution :
  ∀ rows∈[RHBatch01FFTInputR07.rows,RHBatch01FFTInputI07.rows],rows.flatten.length=16384 ∧ rows.all (fun row=>decide (row.length=512) && row.all (fun x=>decide (x≤2^167)))=true := by
  intro rows hr
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hr
  rcases hr with rfl|rfl <;> decide +kernel
#print axioms solution
