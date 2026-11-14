-- Prove2me | solution 1 for ZeroFreeRRG.Hardcore.coloring_degree_monotonicity_from_convexity
-- status  : ACCEPTED   (prove)
-- author  : @wcysai
-- created : 2026-11-13T06:17:54.449517+00:00
-- url     : https://prove2.me/submissions/bd2cf9db-7016-4a58-953e-f4cc2410ec4d

import Theorems.Thm_ZeroFreeRRG_Hardcore_coloring_bethe_low_degrees
import Mathlib
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
open scoped Classical
open Set ZeroFreeRRG.Hardcore

theorem solution (q : ℕ) (hq : 2 ≤ q)
    (ν : MeasureTheory.ProbabilityMeasure ((.potts q : Model).Spin → ℝ))
    (hν : ν ∈ cavityLaws (.potts q) 0) (hne : ν ≠ diracPi (.potts q) 0)
    (hconv : ConvexOn ℝ (Ici 0) (fun t => betheR (.potts q) 0 t ν))
    (r s : ℝ) (hs : 0 ≤ s) (hsr : s ≤ r) (hr : betheR (.potts q) 0 r ν ≤ 0) :
    betheR (.potts q) 0 s ν ≤ 0 := by
  let f : ℝ → ℝ := fun t => betheR (.potts q) 0 t ν
  have hzero : f 0 = 0 := (coloring_bethe_low_degrees q hq ν hν hne).1
  by_cases hr0 : r = 0
  · have hs0 : s=0 := by linarith
    simpa [hs0] using hzero.le
  · have hrpos : 0 < r := lt_of_le_of_ne (le_trans hs hsr) (Ne.symm hr0)
    let b := s/r
    let a := 1-b
    have hb0 : 0 ≤ b := div_nonneg hs (le_of_lt hrpos)
    have hb1 : b ≤ 1 := (div_le_one hrpos).2 hsr
    have ha : 0 ≤ a := sub_nonneg.mpr hb1
    have hab : a+b=1 := by dsimp [a]; ring
    have heq : a*0+b*r=s := by
      dsimp [a,b]
      field_simp
      <;> ring
    have hf := hconv.2 (show (0:ℝ) ∈ Ici 0 by norm_num)
      (show r ∈ Ici 0 from le_of_lt hrpos) ha hb0 hab
    change f (a*0+b*r) ≤ a*f 0+b*f r at hf
    rw [heq,hzero] at hf
    have hle : b*f r ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hb0 hr
    linarith
