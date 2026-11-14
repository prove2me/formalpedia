-- Prove2me | solution 1 for ZeroFreeRRG.Hardcore.coloring_strictness_from_degree_convexity
-- status  : ACCEPTED   (prove)
-- author  : @wcysai
-- created : 2026-11-13T06:14:23.31542+00:00
-- url     : https://prove2.me/submissions/bf435885-1916-42a0-951e-2bb80d8243ad

import Theorems.Thm_ZeroFreeRRG_Hardcore_coloring_bethe_low_degrees
import Mathlib
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
open scoped Classical
open Set ZeroFreeRRG.Hardcore

theorem solution (d q : ℕ) (hd : 3 ≤ d) (hq : 2 ≤ q) (r : ℝ) (hr : (d:ℝ) < r)
    (hconv : ∀ ν ∈ cavityLaws (.potts q) 0, ν ≠ diracPi (.potts q) 0 →
      ConvexOn ℝ (Ici 0) (fun s => betheR (.potts q) 0 s ν))
    (hrs : ∀ ν ∈ cavityLaws (.potts q) 0, betheR (.potts q) 0 r ν ≤ 0) :
    Condition1 (.potts q) d 0 := by
  intro ν hν hne
  let f : ℝ → ℝ := fun s => betheR (.potts q) 0 s ν
  have hd' : (3:ℝ) ≤ d := by exact_mod_cast hd
  have hden : 0 < r-1 := by linarith
  let a := (r-(d:ℝ))/(r-1)
  let b := ((d:ℝ)-1)/(r-1)
  have ha : 0 < a := div_pos (by linarith) hden
  have hb : 0 ≤ b := div_nonneg (by linarith) hden.le
  have hab : a+b=1 := by
    dsimp [a,b]
    field_simp
    <;> ring
  have hcombine : a*1+b*r=(d:ℝ) := by
    dsimp [a,b]
    field_simp
    <;> ring
  have hr0 : r ∈ Ici (0:ℝ) := by
    change 0 ≤ r
    linarith
  have hf := (hconv ν hν hne).2 (show (1:ℝ) ∈ Ici 0 by norm_num)
    hr0 (le_of_lt ha) hb hab
  change f (a*1+b*r) ≤ a*f 1+b*f r at hf
  rw [hcombine] at hf
  have hneg : f 1 < 0 := (coloring_bethe_low_degrees q hq ν hν hne).2
  have hnonpos : f r ≤ 0 := hrs ν hν
  have hstrict : a*f 1+b*f r < 0 := by
    have h1 := mul_neg_of_pos_of_neg ha hneg
    have h2 := mul_nonpos_of_nonneg_of_nonpos hb hnonpos
    linarith
  have hfin : f (d:ℝ) < 0 := lt_of_le_of_lt hf hstrict
  have hint : f (d:ℝ) = betheK (.potts q) 0 d ν := by
    dsimp [f,betheR]
    simp
  rwa [hint] at hfin
