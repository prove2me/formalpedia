-- Prove2me | solution 1 for WorkbookSource.plus_15891
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T09:56:17.040713+00:00
-- url     : https://prove2.me/submissions/9ab5a740-aedc-44b6-8cd3-4232e1a42626

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096
theorem solution (a b : ℝ) (ha : 0 < a) (hb : 0 < b) (hab : a + b = 4) : a^2 * b^2 * (a^2 + b^2) ≤ 128   := by
  have helim : b = (4 - a) := by linarith only [hab]
  have hw0 : 0 ≤ (a) := by
    have hh := ha
    try simp only [helim] at hh
    linarith only [hh]
  have hw1 : 0 ≤ (4 - a) := by
    have hh := hb
    try simp only [helim] at hh
    linarith only [hh]
  have hsum : 0 ≤ (88/35 : ℝ) * (1) * (13*a^3/88 - 57*a^2/176 - 39*a/88 + 1)^2 + (4143/12320 : ℝ) * (1) * (-2038*a^3/4143 + a^2 - 134*a/4143)^2 + (2192/20715 : ℝ) * (1) * (-a^3/4 + a)^2 + (1098/35 : ℝ) * ((4 - a)) * (-103*a^2/1098 - 343*a/1098 + 1)^2 + (106/2745 : ℝ) * ((4 - a)) * (-a^2/2 + a)^2 + (31 : ℝ) * ((a) * (4 - a)) * (-57*a^2/217 + a - 206/217)^2 + (96/1519 : ℝ) * ((a) * (4 - a)) * (1 - a^2/4)^2 := by positivity
  have hid : ( 128   ) - ( a^2 * b^2 * (a^2 + b^2) ) = (88/35 : ℝ) * (1) * (13*a^3/88 - 57*a^2/176 - 39*a/88 + 1)^2 + (4143/12320 : ℝ) * (1) * (-2038*a^3/4143 + a^2 - 134*a/4143)^2 + (2192/20715 : ℝ) * (1) * (-a^3/4 + a)^2 + (1098/35 : ℝ) * ((4 - a)) * (-103*a^2/1098 - 343*a/1098 + 1)^2 + (106/2745 : ℝ) * ((4 - a)) * (-a^2/2 + a)^2 + (31 : ℝ) * ((a) * (4 - a)) * (-57*a^2/217 + a - 206/217)^2 + (96/1519 : ℝ) * ((a) * (4 - a)) * (1 - a^2/4)^2 := by
    try simp only [helim]
    <;> ring
  linarith only [hsum, hid]
example : (∀ (a b : ℝ) (ha : 0 < a) (hb : 0 < b) (hab : a + b = 4), a^2 * b^2 * (a^2 + b^2) ≤ 128) := @solution
#print axioms solution
