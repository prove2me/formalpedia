-- Prove2me | solution 1 for TaoFivePrimes.fft_input_bounds_chunk2
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-18T14:36:19.059062+00:00
-- url     : https://prove2.me/submissions/c7709379-e5a9-47ce-836a-a8a5548aaecf

import Definitions.Def_TaoFivePrimes_RHHighFFTInputR07
import Definitions.Def_TaoFivePrimes_RHHighFFTInputI07
import Definitions.Def_TaoFivePrimes_RHHighFFTInputR08
import Definitions.Def_TaoFivePrimes_RHHighFFTInputI08
import Definitions.Def_TaoFivePrimes_RHHighFFTInputR09
import Definitions.Def_TaoFivePrimes_RHHighFFTInputI09
import Definitions.Def_TaoFivePrimes_RHHighFFTInputR10

set_option maxHeartbeats 0
set_option maxRecDepth 10000

theorem solution :
  ∀ rows ∈ [RHHighFFTInputR07.rows,RHHighFFTInputI07.rows,RHHighFFTInputR08.rows,RHHighFFTInputI08.rows,RHHighFFTInputR09.rows,RHHighFFTInputI09.rows,RHHighFFTInputR10.rows],rows.flatten.length=16384 ∧ rows.all (fun row=>decide (row.length=512) && row.all (fun x=>decide (x≤2^167)))=true := by
  intro rows hrows
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hrows
  rcases hrows with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals decide +kernel
