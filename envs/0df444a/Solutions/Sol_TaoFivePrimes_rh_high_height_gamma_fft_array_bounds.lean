-- Prove2me | solution 1 for TaoFivePrimes.rh_high_height_gamma_fft_array_bounds
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-18T14:39:03.928803+00:00
-- url     : https://prove2.me/submissions/306db71b-28ee-4797-b543-1cc29834ec32

import Theorems.Thm_TaoFivePrimes_fft_input_bounds_chunk0
import Theorems.Thm_TaoFivePrimes_fft_input_bounds_chunk1
import Theorems.Thm_TaoFivePrimes_fft_input_bounds_chunk2
import Theorems.Thm_TaoFivePrimes_fft_input_bounds_chunk3
import Theorems.Thm_TaoFivePrimes_fft_input_bounds_chunk4
import Theorems.Thm_TaoFivePrimes_fft_input_bounds_chunk5
import Theorems.Thm_TaoFivePrimes_fft_input_bounds_chunk6
import Theorems.Thm_TaoFivePrimes_fft_input_bounds_chunk7

open TaoFivePrimes

theorem solution :
∀ rows ∈ [RHHighFFTInputR00.rows,RHHighFFTInputI00.rows,RHHighFFTInputR01.rows,RHHighFFTInputI01.rows,RHHighFFTInputR02.rows,RHHighFFTInputI02.rows,RHHighFFTInputR03.rows,RHHighFFTInputI03.rows,RHHighFFTInputR04.rows,RHHighFFTInputI04.rows,RHHighFFTInputR05.rows,RHHighFFTInputI05.rows,RHHighFFTInputR06.rows,RHHighFFTInputI06.rows,RHHighFFTInputR07.rows,RHHighFFTInputI07.rows,RHHighFFTInputR08.rows,RHHighFFTInputI08.rows,RHHighFFTInputR09.rows,RHHighFFTInputI09.rows,RHHighFFTInputR10.rows,RHHighFFTInputI10.rows,RHHighFFTInputR11.rows,RHHighFFTInputI11.rows,RHHighFFTInputR12.rows,RHHighFFTInputI12.rows,RHHighFFTInputR13.rows,RHHighFFTInputI13.rows,RHHighFFTInputR14.rows,RHHighFFTInputI14.rows,RHHighFFTInputR15.rows,RHHighFFTInputI15.rows,RHHighFFTInputR16.rows,RHHighFFTInputI16.rows,RHHighFFTInputR17.rows,RHHighFFTInputI17.rows,RHHighFFTInputR18.rows,RHHighFFTInputI18.rows,RHHighFFTInputR19.rows,RHHighFFTInputI19.rows,RHHighFFTInputR20.rows,RHHighFFTInputI20.rows,RHHighFFTInputR21.rows,RHHighFFTInputI21.rows,RHHighFFTInputR22.rows,RHHighFFTInputI22.rows,RHHighFFTInputR23.rows,RHHighFFTInputI23.rows,RHHighFFTInputR24.rows,RHHighFFTInputI24.rows,RHHighFFTInputR25.rows,RHHighFFTInputI25.rows],rows.flatten.length=16384 ∧ rows.all (fun row=>decide (row.length=512) && row.all (fun x=>decide (x≤2^167)))=true := by
  intro rows hrows
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hrows
  rcases hrows with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact fft_input_bounds_chunk0 _ (by simp)
  · exact fft_input_bounds_chunk0 _ (by simp)
  · exact fft_input_bounds_chunk0 _ (by simp)
  · exact fft_input_bounds_chunk0 _ (by simp)
  · exact fft_input_bounds_chunk0 _ (by simp)
  · exact fft_input_bounds_chunk0 _ (by simp)
  · exact fft_input_bounds_chunk0 _ (by simp)
  · exact fft_input_bounds_chunk1 _ (by simp)
  · exact fft_input_bounds_chunk1 _ (by simp)
  · exact fft_input_bounds_chunk1 _ (by simp)
  · exact fft_input_bounds_chunk1 _ (by simp)
  · exact fft_input_bounds_chunk1 _ (by simp)
  · exact fft_input_bounds_chunk1 _ (by simp)
  · exact fft_input_bounds_chunk1 _ (by simp)
  · exact fft_input_bounds_chunk2 _ (by simp)
  · exact fft_input_bounds_chunk2 _ (by simp)
  · exact fft_input_bounds_chunk2 _ (by simp)
  · exact fft_input_bounds_chunk2 _ (by simp)
  · exact fft_input_bounds_chunk2 _ (by simp)
  · exact fft_input_bounds_chunk2 _ (by simp)
  · exact fft_input_bounds_chunk2 _ (by simp)
  · exact fft_input_bounds_chunk3 _ (by simp)
  · exact fft_input_bounds_chunk3 _ (by simp)
  · exact fft_input_bounds_chunk3 _ (by simp)
  · exact fft_input_bounds_chunk3 _ (by simp)
  · exact fft_input_bounds_chunk3 _ (by simp)
  · exact fft_input_bounds_chunk3 _ (by simp)
  · exact fft_input_bounds_chunk3 _ (by simp)
  · exact fft_input_bounds_chunk4 _ (by simp)
  · exact fft_input_bounds_chunk4 _ (by simp)
  · exact fft_input_bounds_chunk4 _ (by simp)
  · exact fft_input_bounds_chunk4 _ (by simp)
  · exact fft_input_bounds_chunk4 _ (by simp)
  · exact fft_input_bounds_chunk4 _ (by simp)
  · exact fft_input_bounds_chunk5 _ (by simp)
  · exact fft_input_bounds_chunk5 _ (by simp)
  · exact fft_input_bounds_chunk5 _ (by simp)
  · exact fft_input_bounds_chunk5 _ (by simp)
  · exact fft_input_bounds_chunk5 _ (by simp)
  · exact fft_input_bounds_chunk5 _ (by simp)
  · exact fft_input_bounds_chunk6 _ (by simp)
  · exact fft_input_bounds_chunk6 _ (by simp)
  · exact fft_input_bounds_chunk6 _ (by simp)
  · exact fft_input_bounds_chunk6 _ (by simp)
  · exact fft_input_bounds_chunk6 _ (by simp)
  · exact fft_input_bounds_chunk6 _ (by simp)
  · exact fft_input_bounds_chunk7 _ (by simp)
  · exact fft_input_bounds_chunk7 _ (by simp)
  · exact fft_input_bounds_chunk7 _ (by simp)
  · exact fft_input_bounds_chunk7 _ (by simp)
  · exact fft_input_bounds_chunk7 _ (by simp)
  · exact fft_input_bounds_chunk7 _ (by simp)
