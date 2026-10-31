-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Bridge50.P24.highLoss_envelope
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-31T00:30:54.264234+00:00
-- url     : https://prove2.me/submissions/71f38a71-0961-44cd-a084-c50fc3953887

import Definitions.Def_QAlgorithms_Papers_Independent_Bridge50_P24

set_option autoImplicit false
open Filter
open scoped Topology
open QAlgorithms.Papers.Independent.Bridge50.P24
open QAlgorithms.Papers.Independent.Gap20.P14

theorem solution (n : ℕ) :
    Tendsto (fun eta : ℝ => pulseRateEnvelope n eta / eta)
      (nhdsWithin 0 (Set.Ioo (0 : ℝ) 1))
      (nhds (4 / (((n : ℝ) + 1) * Real.log 2))) := by
  have hq : HasDerivAt (fun x : ℝ => (1 + x) / (1 - x)) 2 0 := by
    have hn : HasDerivAt (fun x : ℝ => 1 + x) 1 0 := (hasDerivAt_id 0).const_add 1
    have hd : HasDerivAt (fun x : ℝ => 1 - x) (-1) 0 := (hasDerivAt_id 0).const_sub 1
    convert! hn.div hd (by norm_num : (1 : ℝ) - 0 ≠ 0) using 1 <;>
      norm_num [Pi.div_def]
  have hl : HasDerivAt (fun x : ℝ => Real.log ((1 + x) / (1 - x))) 2 0 := by
    simpa using hq.log (by norm_num : ((1 : ℝ) + 0) / (1 - 0) ≠ 0)
  have hr : HasDerivAt (pulseRateEnvelope n)
      (4 / (((n : ℝ) + 1) * Real.log 2)) 0 := by
    unfold pulseRateEnvelope rateLossCurve
    convert! (hl.div_const (Real.log 2)).const_mul (2 / ((n : ℝ) + 1)) using 1 <;>
      simp only [div_eq_mul_inv, mul_inv_rev] <;> ring
  have hlim := hr.tendsto_slope_zero_right
  have hsub : Set.Ioo (0 : ℝ) 1 ⊆ Set.Ioi 0 := fun _ h => h.1
  have hlim' := hlim.mono_left (nhdsWithin_mono (0 : ℝ) hsub)
  simpa [pulseRateEnvelope, rateLossCurve, smul_eq_mul, div_eq_mul_inv, mul_comm] using hlim'

#print axioms solution
