-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Bridge50.P04.pureLossReach
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-29T12:59:55.169983+00:00
-- url     : https://prove2.me/submissions/345ba2e5-23b0-4213-a526-42904c9875fc

import Definitions.Def_QAlgorithms_Papers_Independent_Bridge50_P04

open QAlgorithms.Papers.Independent.Bridge50.P04

open QAlgorithms.Papers.Independent.Information100.P63 (logTwo)

open QAlgorithms.Papers.Independent.Frontier30.P24 (bosonicEntropy)

theorem pureLossRate_closed_s110 (tau : ℝ) (h0 : 0 < tau) (h1 : tau < 1) :
    pureLossRate tau = (-(Real.log (1 - tau)) / tau - 1) / Real.log 2 := by
  have ha : 0 < 1 - tau := by linarith
  have hx : ((2 - tau) / tau - 1) / 2 = (1 - tau) / tau := by
    field_simp
    ring
  have hx1 : (1 - tau) / tau + 1 = tau⁻¹ := by
    field_simp
    ring
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  unfold pureLossRate bosonicEntropy logTwo
  rw [hx, hx1, Real.log_inv, Real.log_div ha.ne' h0.ne',
    Real.log_div h0.ne' (by positivity), Real.log_mul ha.ne' (Real.exp_pos 1).ne',
    Real.log_exp]
  field_simp
  ring

theorem solution :
    (∀ tau : ℝ, 0 < tau → tau < 1 → 0 < pureLossRate tau) ∧
      Filter.Tendsto pureLossRate (nhdsWithin (0 : ℝ) (Set.Ioo 0 1)) (nhds 0) := by
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  constructor
  · intro tau h0 h1
    rw [pureLossRate_closed_s110 tau h0 h1]
    apply div_pos _ hl2
    have hlt : Real.log (1 - tau) < (1 - tau) - 1 :=
      Real.log_lt_sub_one_of_pos (by linarith) (by linarith)
    rw [sub_pos, lt_div_iff₀ h0]
    linarith
  · have hd : HasDerivAt (fun t : ℝ => Real.log (1 - t)) (-1) 0 := by
      have := ((hasDerivAt_id (0:ℝ)).const_sub 1).log (by norm_num)
      simpa using this
    have hs := hd.tendsto_slope_zero
    have hs' : Filter.Tendsto (fun t : ℝ => t⁻¹ * Real.log (1 - t))
        (nhdsWithin (0 : ℝ) (Set.Ioo 0 1)) (nhds (-1)) := by
      have := hs.mono_left (nhdsWithin_mono _ (fun t (ht : t ∈ Set.Ioo (0:ℝ) 1) =>
        (show t ≠ 0 from ht.1.ne')))
      simpa using this
    have hlim : Filter.Tendsto (fun t : ℝ => (-(t⁻¹ * Real.log (1 - t)) - 1) / Real.log 2)
        (nhdsWithin (0 : ℝ) (Set.Ioo 0 1)) (nhds ((-(-1) - 1) / Real.log 2)) :=
      ((hs'.neg).sub_const 1).div_const _
    rw [show ((-(-1:ℝ) - 1) / Real.log 2) = 0 by ring] at hlim
    apply hlim.congr'
    filter_upwards [self_mem_nhdsWithin] with t ht
    rw [pureLossRate_closed_s110 t ht.1 ht.2]
    ring
