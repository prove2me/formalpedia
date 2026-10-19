-- Prove2me | solution 1 for TaoFivePrimes.fft_input_bounds_chunk7
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-18T14:36:22.70019+00:00
-- url     : https://prove2.me/submissions/58a1e57a-ca40-4c79-95f7-1cc817b2e47f

import Definitions.Def_TaoFivePrimes_RHHighFFTInputR23
import Definitions.Def_TaoFivePrimes_RHHighFFTInputI23
import Definitions.Def_TaoFivePrimes_RHHighFFTInputR24
import Definitions.Def_TaoFivePrimes_RHHighFFTInputI24
import Definitions.Def_TaoFivePrimes_RHHighFFTInputR25
import Definitions.Def_TaoFivePrimes_RHHighFFTInputI25

set_option maxHeartbeats 0
set_option maxRecDepth 10000

theorem solution :
  ∀ rows ∈ [RHHighFFTInputR23.rows,RHHighFFTInputI23.rows,RHHighFFTInputR24.rows,RHHighFFTInputI24.rows,RHHighFFTInputR25.rows,RHHighFFTInputI25.rows],rows.flatten.length=16384 ∧ rows.all (fun row=>decide (row.length=512) && row.all (fun x=>decide (x≤2^167)))=true := by
  intro rows hrows
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hrows
  rcases hrows with rfl | rfl | rfl | rfl | rfl | rfl
  all_goals decide +kernel
