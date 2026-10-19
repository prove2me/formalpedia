-- Prove2me | solution 1 for TaoFivePrimes.fft_input_bounds_chunk6
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-18T14:36:22.009136+00:00
-- url     : https://prove2.me/submissions/dd78d5c7-ef77-4d04-b95c-427a899827a2

import Definitions.Def_TaoFivePrimes_RHHighFFTInputR20
import Definitions.Def_TaoFivePrimes_RHHighFFTInputI20
import Definitions.Def_TaoFivePrimes_RHHighFFTInputR21
import Definitions.Def_TaoFivePrimes_RHHighFFTInputI21
import Definitions.Def_TaoFivePrimes_RHHighFFTInputR22
import Definitions.Def_TaoFivePrimes_RHHighFFTInputI22

set_option maxHeartbeats 0
set_option maxRecDepth 10000

theorem solution :
  ∀ rows ∈ [RHHighFFTInputR20.rows,RHHighFFTInputI20.rows,RHHighFFTInputR21.rows,RHHighFFTInputI21.rows,RHHighFFTInputR22.rows,RHHighFFTInputI22.rows],rows.flatten.length=16384 ∧ rows.all (fun row=>decide (row.length=512) && row.all (fun x=>decide (x≤2^167)))=true := by
  intro rows hrows
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hrows
  rcases hrows with rfl | rfl | rfl | rfl | rfl | rfl
  all_goals decide +kernel
