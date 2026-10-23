-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Gap20.P14.highLoss_boundCurves
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-22T09:05:09.982524+00:00
-- url     : https://prove2.me/submissions/d9b86e0b-b27b-41f5-a48a-a5147c6fec97

import Definitions.Def_QAlgorithms_Papers_Independent_Gap20_P14

namespace X6P14

open Filter

lemma slope_lim (f : ℝ → ℝ) (f' : ℝ) (hf : HasDerivAt f f' 0) (h0 : f 0 = 0) :
    Tendsto (fun eta : ℝ => f eta / eta) (nhdsWithin 0 (Set.Ioo (0 : ℝ) 1)) (nhds f') := by
  have := hf.tendsto_slope_zero
  have hsub : nhdsWithin (0 : ℝ) (Set.Ioo 0 1) ≤ nhdsWithin 0 {0}ᶜ :=
    nhdsWithin_mono _ (fun x hx => by simp only [Set.mem_compl_iff, Set.mem_singleton_iff]; exact hx.1.ne')
  refine (this.mono_left hsub).congr (fun t => ?_)
  simp [h0, div_eq_inv_mul]

end X6P14

open Filter QAlgorithms.Papers.Independent.Gap20.P14 X6P14

theorem solution :
    Tendsto (fun eta : ℝ => rateLossCurve eta / eta)
      (nhdsWithin 0 (Set.Ioo (0 : ℝ) 1)) (nhds (2 / Real.log 2)) ∧
    Tendsto (fun eta : ℝ => reverseCoherentCurve eta / eta)
      (nhdsWithin 0 (Set.Ioo (0 : ℝ) 1)) (nhds (1 / Real.log 2)) := by
  constructor
  · apply slope_lim
    · have hq : HasDerivAt (fun x : ℝ => (1 + x) / (1 - x)) 2 0 := by
        have := ((hasDerivAt_id (0:ℝ)).const_add 1).div ((hasDerivAt_id (0:ℝ)).const_sub 1)
          (by norm_num)
        exact (this : HasDerivAt (fun x : ℝ => (1 + x) / (1 - x)) _ 0).congr_deriv (by norm_num)
      have := (hq.log (by norm_num)).div_const (Real.log 2)
      exact (this : HasDerivAt rateLossCurve _ 0).congr_deriv (by norm_num)
    · simp [rateLossCurve]
  · apply slope_lim
    · have h1 : HasDerivAt (fun x : ℝ => 1 - x) (-1) 0 := by
        simpa using (hasDerivAt_id (0:ℝ)).const_sub 1
      have := ((h1.log (by norm_num)).neg).div_const (Real.log 2)
      exact (this : HasDerivAt reverseCoherentCurve _ 0).congr_deriv (by norm_num)
    · simp [reverseCoherentCurve]
