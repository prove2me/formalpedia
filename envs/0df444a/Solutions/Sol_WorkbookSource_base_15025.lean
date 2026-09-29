-- Prove2me | solution 1 for WorkbookSource.base_15025
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T10:32:26.589768+00:00
-- url     : https://prove2.me/submissions/e06da22a-843d-4d3e-ab62-c7fc6b6f2ace

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096
theorem solution (a b c d e f : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d) (he : 0 < e) (hf : 0 < f) (habcdef : a + b + c + d + e + f = 1) : a * b * c + b * c * d + c * d * e + d * e * f + e * f * a + f * a * b ≤ 1 / 27  := by
  have helim : f = (-a - b - c - d - e + 1) := by linarith only [habcdef]
  have hw0 : 0 ≤ (a) := by
    have hh := ha
    try simp only [helim] at hh
    linarith only [hh]
  have hw1 : 0 ≤ (b) := by
    have hh := hb
    try simp only [helim] at hh
    linarith only [hh]
  have hw2 : 0 ≤ (c) := by
    have hh := hc
    try simp only [helim] at hh
    linarith only [hh]
  have hw3 : 0 ≤ (d) := by
    have hh := hd
    try simp only [helim] at hh
    linarith only [hh]
  have hw4 : 0 ≤ (e) := by
    have hh := he
    try simp only [helim] at hh
    linarith only [hh]
  have hw5 : 0 ≤ (-a - b - c - d - e + 1) := by
    have hh := hf
    try simp only [helim] at hh
    linarith only [hh]
  have hsum : 0 ≤ (1/9 : ℝ) * (1) * (a/2 + b + d/2 + e - 1/2)^2 + (1/12 : ℝ) * (1) * (a + d - 1/3)^2 + (1/9 : ℝ) * ((-a - b - c - d - e + 1)) * (-a + b - d + e)^2 + (4/9 : ℝ) * ((e)) * (a + b/2 + d + e/2 - 1/2)^2 + (4/9 : ℝ) * ((d)) * (a/2 + b + d/2 + e - 1/2)^2 + (1/9 : ℝ) * ((c)) * (-a + b - d + e)^2 + (4/9 : ℝ) * ((b)) * (a + b/2 + d + e/2 - 1/2)^2 + (1 : ℝ) * ((b) * (d) * (-a - b - c - d - e + 1)) * (1)^2 + (4/9 : ℝ) * ((a)) * (a/2 + b + d/2 + e - 1/2)^2 + (1 : ℝ) * ((a) * (c) * (e)) * (1)^2 := by positivity
  have hid : ( 1 / 27  ) - ( a * b * c + b * c * d + c * d * e + d * e * f + e * f * a + f * a * b ) = (1/9 : ℝ) * (1) * (a/2 + b + d/2 + e - 1/2)^2 + (1/12 : ℝ) * (1) * (a + d - 1/3)^2 + (1/9 : ℝ) * ((-a - b - c - d - e + 1)) * (-a + b - d + e)^2 + (4/9 : ℝ) * ((e)) * (a + b/2 + d + e/2 - 1/2)^2 + (4/9 : ℝ) * ((d)) * (a/2 + b + d/2 + e - 1/2)^2 + (1/9 : ℝ) * ((c)) * (-a + b - d + e)^2 + (4/9 : ℝ) * ((b)) * (a + b/2 + d + e/2 - 1/2)^2 + (1 : ℝ) * ((b) * (d) * (-a - b - c - d - e + 1)) * (1)^2 + (4/9 : ℝ) * ((a)) * (a/2 + b + d/2 + e - 1/2)^2 + (1 : ℝ) * ((a) * (c) * (e)) * (1)^2 := by
    try simp only [helim]
    ring
  linarith only [hsum, hid]
example : (∀ (a b c d e f : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d) (he : 0 < e) (hf : 0 < f) (habcdef : a + b + c + d + e + f = 1), a * b * c + b * c * d + c * d * e + d * e * f + e * f * a + f * a * b ≤ 1 / 27) := @solution
#print axioms solution
