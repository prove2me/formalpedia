-- Prove2me | solution 1 for TaoFivePrimes.fft_input_bounds_chunk4
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-18T14:36:20.688866+00:00
-- url     : https://prove2.me/submissions/2b0dd2a7-0b5b-4f56-bcba-87dac28c3aec

import Definitions.Def_TaoFivePrimes_RHHighFFTInputR14
import Definitions.Def_TaoFivePrimes_RHHighFFTInputI14
import Definitions.Def_TaoFivePrimes_RHHighFFTInputR15
import Definitions.Def_TaoFivePrimes_RHHighFFTInputI15
import Definitions.Def_TaoFivePrimes_RHHighFFTInputR16
import Definitions.Def_TaoFivePrimes_RHHighFFTInputI16

set_option maxHeartbeats 0
set_option maxRecDepth 10000

theorem solution :
  ∀ rows ∈ [RHHighFFTInputR14.rows,RHHighFFTInputI14.rows,RHHighFFTInputR15.rows,RHHighFFTInputI15.rows,RHHighFFTInputR16.rows,RHHighFFTInputI16.rows],rows.flatten.length=16384 ∧ rows.all (fun row=>decide (row.length=512) && row.all (fun x=>decide (x≤2^167)))=true := by
  intro rows hrows
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hrows
  rcases hrows with rfl | rfl | rfl | rfl | rfl | rfl
  all_goals decide +kernel
