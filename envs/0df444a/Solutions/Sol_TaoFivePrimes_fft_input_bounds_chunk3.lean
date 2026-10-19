-- Prove2me | solution 1 for TaoFivePrimes.fft_input_bounds_chunk3
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-18T14:36:19.770677+00:00
-- url     : https://prove2.me/submissions/0741944e-7a27-493b-86c1-9d0d61117a71

import Definitions.Def_TaoFivePrimes_RHHighFFTInputI10
import Definitions.Def_TaoFivePrimes_RHHighFFTInputR11
import Definitions.Def_TaoFivePrimes_RHHighFFTInputI11
import Definitions.Def_TaoFivePrimes_RHHighFFTInputR12
import Definitions.Def_TaoFivePrimes_RHHighFFTInputI12
import Definitions.Def_TaoFivePrimes_RHHighFFTInputR13
import Definitions.Def_TaoFivePrimes_RHHighFFTInputI13

set_option maxHeartbeats 0
set_option maxRecDepth 10000

theorem solution :
  ∀ rows ∈ [RHHighFFTInputI10.rows,RHHighFFTInputR11.rows,RHHighFFTInputI11.rows,RHHighFFTInputR12.rows,RHHighFFTInputI12.rows,RHHighFFTInputR13.rows,RHHighFFTInputI13.rows],rows.flatten.length=16384 ∧ rows.all (fun row=>decide (row.length=512) && row.all (fun x=>decide (x≤2^167)))=true := by
  intro rows hrows
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hrows
  rcases hrows with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals decide +kernel
