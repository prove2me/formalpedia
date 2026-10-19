-- Prove2me | solution 1 for TaoFivePrimes.fft_input_bounds_chunk0
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-18T14:34:02.65734+00:00
-- url     : https://prove2.me/submissions/fc3e265c-f716-45f1-a877-09b70e2e6be3

import Definitions.Def_TaoFivePrimes_RHHighFFTInputR00
import Definitions.Def_TaoFivePrimes_RHHighFFTInputI00
import Definitions.Def_TaoFivePrimes_RHHighFFTInputR01
import Definitions.Def_TaoFivePrimes_RHHighFFTInputI01
import Definitions.Def_TaoFivePrimes_RHHighFFTInputR02
import Definitions.Def_TaoFivePrimes_RHHighFFTInputI02
import Definitions.Def_TaoFivePrimes_RHHighFFTInputR03

set_option maxHeartbeats 0
set_option maxRecDepth 10000

theorem solution :
  ∀ rows ∈ [RHHighFFTInputR00.rows,RHHighFFTInputI00.rows,RHHighFFTInputR01.rows,RHHighFFTInputI01.rows,RHHighFFTInputR02.rows,RHHighFFTInputI02.rows,RHHighFFTInputR03.rows],rows.flatten.length=16384 ∧ rows.all (fun row=>decide (row.length=512) && row.all (fun x=>decide (x≤2^167)))=true := by
  intro rows hrows
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hrows
  rcases hrows with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals decide +kernel
