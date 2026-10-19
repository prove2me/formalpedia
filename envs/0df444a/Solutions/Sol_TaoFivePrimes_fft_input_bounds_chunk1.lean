-- Prove2me | solution 1 for TaoFivePrimes.fft_input_bounds_chunk1
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-18T14:36:18.411548+00:00
-- url     : https://prove2.me/submissions/cce4aede-b868-4af3-ac17-a78b81350402

import Definitions.Def_TaoFivePrimes_RHHighFFTInputI03
import Definitions.Def_TaoFivePrimes_RHHighFFTInputR04
import Definitions.Def_TaoFivePrimes_RHHighFFTInputI04
import Definitions.Def_TaoFivePrimes_RHHighFFTInputR05
import Definitions.Def_TaoFivePrimes_RHHighFFTInputI05
import Definitions.Def_TaoFivePrimes_RHHighFFTInputR06
import Definitions.Def_TaoFivePrimes_RHHighFFTInputI06

set_option maxHeartbeats 0
set_option maxRecDepth 10000

theorem solution :
  ∀ rows ∈ [RHHighFFTInputI03.rows,RHHighFFTInputR04.rows,RHHighFFTInputI04.rows,RHHighFFTInputR05.rows,RHHighFFTInputI05.rows,RHHighFFTInputR06.rows,RHHighFFTInputI06.rows],rows.flatten.length=16384 ∧ rows.all (fun row=>decide (row.length=512) && row.all (fun x=>decide (x≤2^167)))=true := by
  intro rows hrows
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hrows
  rcases hrows with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals decide +kernel
