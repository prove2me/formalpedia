-- Prove2me | solution 1 for TaoFivePrimes.fft_input_bounds_chunk5
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-18T14:36:21.370469+00:00
-- url     : https://prove2.me/submissions/5e1d5918-380e-47ec-8d0e-50c28738160d

import Definitions.Def_TaoFivePrimes_RHHighFFTInputR17
import Definitions.Def_TaoFivePrimes_RHHighFFTInputI17
import Definitions.Def_TaoFivePrimes_RHHighFFTInputR18
import Definitions.Def_TaoFivePrimes_RHHighFFTInputI18
import Definitions.Def_TaoFivePrimes_RHHighFFTInputR19
import Definitions.Def_TaoFivePrimes_RHHighFFTInputI19

set_option maxHeartbeats 0
set_option maxRecDepth 10000

theorem solution :
  ∀ rows ∈ [RHHighFFTInputR17.rows,RHHighFFTInputI17.rows,RHHighFFTInputR18.rows,RHHighFFTInputI18.rows,RHHighFFTInputR19.rows,RHHighFFTInputI19.rows],rows.flatten.length=16384 ∧ rows.all (fun row=>decide (row.length=512) && row.all (fun x=>decide (x≤2^167)))=true := by
  intro rows hrows
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hrows
  rcases hrows with rfl | rfl | rfl | rfl | rfl | rfl
  all_goals decide +kernel
