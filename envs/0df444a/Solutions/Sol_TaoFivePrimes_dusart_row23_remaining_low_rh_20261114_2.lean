-- Prove2me | solution 2 for TaoFivePrimes.dusart_row23_remaining_low_rh_20261114
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T00:42:19.132792+00:00
-- url     : https://prove2.me/submissions/d0d7cf50-d88c-4881-90f0-6a233a4151f5

import Mathlib
import Definitions.Def_dusart_psi_433_20261014_ZeroSeries
import Theorems.Thm_TaoFivePrimes_zeta_ne_zero_strip_im_two_to_fourteen
import Theorems.Thm_TaoFivePrimes_rh_verified_block_1e2_1e3

open Complex DusartSmoothing
noncomputable section
namespace TaoFivePrimes
end TaoFivePrimes
open TaoFivePrimes

theorem solution : ∀ ρ : NontrivialZetaZero,
  (((224/32:ℝ) < |ρ.val.im| ∧ |ρ.val.im| < (14:ℝ)) ∨
   ((100:ℝ) < |ρ.val.im| ∧ |ρ.val.im| ≤ (121 - 5773/100000:ℝ))) → ρ.val.re = 1/2 := by
  intro ρ h
  obtain ⟨hz, h0, h1⟩ := ρ.property
  -- the conjugate point is again a zero, with the same real part and the opposite height
  have hzc : riemannZeta (starRingEnd ℂ ρ.val) = 0 := by
    rw [riemannZeta_conj, hz, map_zero]
  have hrec : (starRingEnd ℂ ρ.val).re = ρ.val.re := Complex.conj_re _
  have himc : (starRingEnd ℂ ρ.val).im = -ρ.val.im := Complex.conj_im _
  rcases h with ⟨ha, hb⟩ | ⟨ha, hb⟩
  · -- heights between 7 and 14: there is no zero at all
    exfalso
    rcases le_or_gt 0 ρ.val.im with hpos | hneg
    · rw [abs_of_nonneg hpos] at ha hb
      exact TaoFivePrimes.zeta_ne_zero_strip_im_two_to_fourteen ρ.val h0 h1
        (by linarith) (by linarith) hz
    · rw [abs_of_neg hneg] at ha hb
      exact TaoFivePrimes.zeta_ne_zero_strip_im_two_to_fourteen (starRingEnd ℂ ρ.val)
        (by rw [hrec]; exact h0) (by rw [hrec]; exact h1)
        (by rw [himc]; linarith) (by rw [himc]; linarith) hzc
  · -- heights between 100 and 120.94227: inside the verified block from 100 to 1000
    rcases le_or_gt 0 ρ.val.im with hpos | hneg
    · rw [abs_of_nonneg hpos] at ha hb
      exact TaoFivePrimes.rh_verified_block_1e2_1e3 ρ.val hz h0 h1
        (by norm_num; linarith) (by norm_num; linarith)
    · rw [abs_of_neg hneg] at ha hb
      have key := TaoFivePrimes.rh_verified_block_1e2_1e3 (starRingEnd ℂ ρ.val) hzc
        (by rw [hrec]; exact h0) (by rw [hrec]; exact h1)
        (by rw [himc]; norm_num; linarith) (by rw [himc]; norm_num; linarith)
      rw [hrec] at key
      exact key
