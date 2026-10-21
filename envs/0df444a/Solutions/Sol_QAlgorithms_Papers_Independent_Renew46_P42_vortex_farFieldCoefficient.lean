-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Renew46.P42.vortex_farFieldCoefficient
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-21T00:05:29.557653+00:00
-- url     : https://prove2.me/submissions/e53c0699-fc4d-41a1-91c5-c935c25d776a

import Definitions.Def_QAlgorithms_Papers_Independent_Renew46_P42
open QAlgorithms.Papers.Independent.Renew46.P42

noncomputable section

open scoped BigOperators

open Filter Set MeasureTheory

-- Reuse the pinned accepted real quadratic form (arbitrary finite real matrices).

open QAlgorithms.Papers.Independent.Information100.P37 (quadratic)


/-- PDF p.9, (78)–(79): the inverse-radius quadratic coefficient of the full
relativistic-vortex radial symbol; the extra n^2 multiplying W^2 is retained. -/
theorem solution (c n W l : ℝ)
    (hc : 0 < c) (hn : 1 ≤ n) (hW : 0 < W) :
    Tendsto (fun r => r ^ 2 * (radialF c n (vortexSpeed c W) r l - n ^ 2)) atTop
      (nhds (-(angularAB c n W l) ^ 2 + (n ^ 2 - 1) * n ^ 2 * W ^ 2 / c ^ 2)) := by
  have hc2 : 0 < c ^ 2 := by positivity
  set γ := fun r => vortexGamma c W r with hγdef
  have hg : Tendsto (fun r : ℝ => vortexGamma c W r) atTop (nhds 1) := by
    have h0 : Tendsto (fun r : ℝ => W ^ 2 / (c ^ 2 * r ^ 2)) atTop (nhds 0) := by
      apply Tendsto.div_atTop tendsto_const_nhds
      exact (tendsto_pow_atTop (by norm_num : (2:ℕ) ≠ 0)).const_mul_atTop hc2
    have := ((h0.const_add 1).sqrt)
    simpa [vortexGamma] using this
  have hr2 : Tendsto (fun r : ℝ => W ^ 2 * l ^ 2 / (c ^ 2 * r ^ 2)) atTop (nhds 0) := by
    apply Tendsto.div_atTop tendsto_const_nhds
    exact (tendsto_pow_atTop (by norm_num : (2:ℕ) ≠ 0)).const_mul_atTop hc2
  have hlim : Tendsto (fun r => -l ^ 2 + (n ^ 2 - 1) * W ^ 2 / c ^ 2 -
      2 * (n ^ 2 - 1) * W * l / c * vortexGamma c W r +
      (n ^ 2 - 1) * (W ^ 2 * l ^ 2 / (c ^ 2 * r ^ 2))) atTop
      (nhds (-l ^ 2 + (n ^ 2 - 1) * W ^ 2 / c ^ 2 - 2 * (n ^ 2 - 1) * W * l / c * 1 +
        (n ^ 2 - 1) * 0)) :=
    ((tendsto_const_nhds.sub (hg.const_mul _)).add (hr2.const_mul _))
  have hv : -l ^ 2 + (n ^ 2 - 1) * W ^ 2 / c ^ 2 - 2 * (n ^ 2 - 1) * W * l / c * 1 +
        (n ^ 2 - 1) * 0 = -(angularAB c n W l) ^ 2 + (n ^ 2 - 1) * n ^ 2 * W ^ 2 / c ^ 2 := by
    simp only [angularAB]; field_simp; ring
  rw [hv] at hlim
  refine hlim.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with r hr
  have hγ2 : vortexGamma c W r ^ 2 = 1 + W ^ 2 / (c ^ 2 * r ^ 2) := by
    rw [vortexGamma, Real.sq_sqrt (by positivity)]
  have hγ2' : vortexGamma c W r ^ 2 * (c ^ 2 * r ^ 2) = c ^ 2 * r ^ 2 + W ^ 2 := by
    rw [hγ2]; field_simp
  have hγp : 0 < vortexGamma c W r := by rw [vortexGamma]; positivity
  have hA : 1 - vortexSpeed c W r ^ 2 / c ^ 2 = 1 / vortexGamma c W r ^ 2 := by
    rw [vortexSpeed]; field_simp; linear_combination hγ2'
  simp only [radialF]
  rw [hA]
  have hB : vortexSpeed c W r = W / (vortexGamma c W r * r) := rfl
  rw [hB]
  generalize vortexGamma c W r = g at hγ2' hγp
  field_simp
  linear_combination -(n ^ 2 - 1) * r ^ 2 * hγ2'


end

