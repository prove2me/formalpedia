-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Bridge50.P04.zeroExcessNoiseOptimum
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-29T13:14:25.127418+00:00
-- url     : https://prove2.me/submissions/a94ee2d9-5ce3-4383-a937-3d7fd0e77944

import Definitions.Def_QAlgorithms_Papers_Independent_Bridge50_P04
namespace QAlgorithms.Papers.Independent.Bridge50.P04

open QAlgorithms.Papers.Independent.Information100.P63 (logTwo)

open QAlgorithms.Papers.Independent.Frontier30.P24 (bosonicEntropy)

noncomputable def s110zH (c y : ℝ) : ℝ :=
  c * (1 + y) * Real.log (c * (1 + y) + 1) - c * (1 + y) * Real.log (c * (1 + y)) -
    (y + 1) * Real.log (y + 1) + y * Real.log y

theorem s110z_rate_eq (tau e : ℝ) (h0 : 0 < tau) (h1 : tau < 1) (he : 0 ≤ e) :
    analyticRate tau e =
      (s110zH ((1 - tau) / tau) (tau * e / (2 * (1 - tau ^ 2))) - 1 - Real.log (1 - tau)) /
        Real.log 2 := by
  have h1t : 0 < 1 - tau := by linarith
  have h1t2 : 0 < 1 - tau ^ 2 := by nlinarith
  set c := (1 - tau) / tau with hc
  set y := tau * e / (2 * (1 - tau ^ 2)) with hy
  have hcpos : 0 < c := by positivity
  have hy0 : 0 ≤ y := by positivity
  have hA : ((equivalentNoise tau e / (1 + tau) - 1) - 1) / 2 = c * (1 + y) := by
    simp only [equivalentNoise, lossNoise, hc, hy]
    field_simp
    ring
  have hB : (((tau * equivalentNoise tau e - (1 + tau) ^ 2) / (1 - tau ^ 2)) - 1) / 2 = y := by
    simp only [equivalentNoise, lossNoise, hy]
    field_simp
    ring
  have hchi : equivalentNoise tau e = 2 * (1 + tau) * (c * (1 + y) + 1) := by
    rw [← hA]; field_simp; ring
  have hxpos : 0 < c * (1 + y) + 1 := by positivity
  have hlog : Real.log (2 * (1 + tau) / (Real.exp 1 * (1 - tau) * equivalentNoise tau e)) =
      -1 - Real.log (1 - tau) - Real.log (c * (1 + y) + 1) := by
    have le : Real.log (Real.exp 1 * (1 - tau)) = 1 + Real.log (1 - tau) := by
      rw [Real.log_mul (by positivity) h1t.ne', Real.log_exp]
    have l2 : Real.log (2 * (1 + tau) * (c * (1 + y) + 1)) =
        Real.log (2 * (1 + tau)) + Real.log (c * (1 + y) + 1) :=
      Real.log_mul (by positivity) (by positivity)
    have l3 : Real.log (Real.exp 1 * (1 - tau) * (2 * (1 + tau) * (c * (1 + y) + 1))) =
        Real.log (Real.exp 1 * (1 - tau)) + Real.log (2 * (1 + tau) * (c * (1 + y) + 1)) :=
      Real.log_mul (by positivity) (by positivity)
    rw [hchi, Real.log_div (by positivity) (by positivity), l3, le, l2]
    ring
  simp only [analyticRate, bosonicEntropy, logTwo]
  rw [hA, hB, hlog]
  simp only [s110zH]
  field_simp
  ring

theorem s110z_anti (c : ℝ) (hc : 0 < c) : AntitoneOn (s110zH c) (Set.Ici 0) := by
  have hint : interior (Set.Ici (0 : ℝ)) = Set.Ioi 0 := interior_Ici
  apply antitoneOn_of_hasDerivWithinAt_nonpos (convex_Ici 0)
    (f' := fun y => c * (Real.log (c * (1 + y) + 1) - Real.log (c * (1 + y)) -
      1 / (c * (1 + y) + 1)) - (Real.log (y + 1) - Real.log y))
  · -- continuity
    have hu : ∀ y ∈ Set.Ici (0 : ℝ), 0 < c * (1 + y) := fun y hy => by
      simp at hy; positivity
    have cu : ContinuousOn (fun y : ℝ => c * (1 + y)) (Set.Ici 0) := by fun_prop
    have p1 : ContinuousOn (fun y : ℝ => c * (1 + y) * Real.log (c * (1 + y) + 1)) (Set.Ici 0) :=
      cu.mul ((cu.add continuousOn_const).log (fun y hy => by have := hu y hy; exact ne_of_gt (by show 0 < c * (1 + y) + 1; linarith)))
    have p2 : ContinuousOn (fun y : ℝ => c * (1 + y) * Real.log (c * (1 + y))) (Set.Ici 0) :=
      cu.mul (cu.log (fun y hy => (hu y hy).ne'))
    have p3 : ContinuousOn (fun y : ℝ => (y + 1) * Real.log (y + 1)) (Set.Ici 0) :=
      (continuous_id.add continuous_const).continuousOn.mul
        ((continuous_id.add continuous_const).continuousOn.log
          (fun y hy => by simp at hy; simp; linarith))
    have p4 : ContinuousOn (fun y : ℝ => y * Real.log y) (Set.Ici 0) :=
      Real.continuous_mul_log.continuousOn
    exact ((p1.sub p2).sub p3).add p4
  · intro y hy
    rw [hint] at hy ⊢
    simp at hy
    apply HasDerivAt.hasDerivWithinAt
    have hu : 0 < c * (1 + y) := by positivity
    have d1 : HasDerivAt (fun y : ℝ => c * (1 + y)) c y := by
      simpa using ((hasDerivAt_id y).const_add 1).const_mul c
    have d2 : HasDerivAt (fun y : ℝ => c * (1 + y) + 1) c y := d1.add_const 1
    have q1 := d1.mul (d2.log (by linarith))
    have q2 := d1.mul (d1.log hu.ne')
    have d3 : HasDerivAt (fun y : ℝ => y + 1) 1 y := (hasDerivAt_id y).add_const 1
    have q3 := d3.mul (d3.log (by linarith))
    have q4 := (hasDerivAt_id y).mul ((hasDerivAt_id y).log hy.ne')
    have := ((q1.sub q2).sub q3).add q4
    convert this using 1
    · funext z; simp only [s110zH, Pi.add_apply, Pi.sub_apply, Pi.mul_apply, id]
    simp only [id]
    have hu1 : c * (1 + y) + 1 ≠ 0 := by linarith
    field_simp
    ring
  · intro y hy
    rw [hint] at hy
    simp at hy
    have hu : 0 < c * (1 + y) := by positivity
    have l1 : Real.log (c * (1 + y) + 1) - Real.log (c * (1 + y)) ≤ 1 / (c * (1 + y)) := by
      rw [← Real.log_div (by linarith) hu.ne']
      have := Real.log_le_sub_one_of_pos (x := (c * (1 + y) + 1) / (c * (1 + y)))
        (by positivity)
      have e : (c * (1 + y) + 1) / (c * (1 + y)) - 1 = 1 / (c * (1 + y)) := by
        field_simp; ring
      linarith
    have l2 : 1 / (y + 1) ≤ Real.log (y + 1) - Real.log y := by
      have := Real.log_le_sub_one_of_pos (x := y / (y + 1)) (by positivity)
      rw [Real.log_div hy.ne' (by linarith)] at this
      have e : y / (y + 1) - 1 = -(1 / (y + 1)) := by field_simp; ring
      linarith
    have l3 : c * (1 / (c * (1 + y))) = 1 / (y + 1) := by field_simp; ring
    have l4 : 0 ≤ 1 / (c * (1 + y) + 1) := by positivity
    have : c * (Real.log (c * (1 + y) + 1) - Real.log (c * (1 + y)) -
        1 / (c * (1 + y) + 1)) ≤ c * (1 / (c * (1 + y))) := by
      apply mul_le_mul_of_nonneg_left _ hc.le
      linarith
    show _ ≤ (0:ℝ)
    linarith

end QAlgorithms.Papers.Independent.Bridge50.P04

open QAlgorithms.Papers.Independent.Bridge50.P04 in
theorem solution (tau excess : ℝ)
    (hTauPos : 0 < tau) (hTauLt : tau < 1) (hExcess : 0 ≤ excess) :
    analyticRate tau excess ≤ analyticRate tau 0 := by
  rw [s110z_rate_eq tau excess hTauPos hTauLt hExcess, s110z_rate_eq tau 0 hTauPos hTauLt le_rfl]
  have h1t2 : 0 < 1 - tau ^ 2 := by nlinarith
  apply div_le_div_of_nonneg_right _ (Real.log_pos (by norm_num)).le
  have := s110z_anti ((1 - tau) / tau) (by apply div_pos <;> linarith)
    (a := 0) (b := tau * excess / (2 * (1 - tau ^ 2))) (by simp)
    (by simp only [Set.mem_Ici]; positivity) (by positivity)
  simp only [mul_zero, zero_div] at this ⊢
  linarith
