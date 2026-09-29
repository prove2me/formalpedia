-- Prove2me | solution 1 for WorkbookSource.plus_15874
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T09:56:16.257967+00:00
-- url     : https://prove2.me/submissions/6208a188-06b6-4049-b4a0-9b7787f38d08

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096
theorem solution (a b c d : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d) (hab : a + b + c + d = 4) : a * b * c + b * c * d + c * d * a + d * a * b ≤ 4   := by
  have helim : d = (-a - b - c + 4) := by linarith only [hab]
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
  have hw3 : 0 ≤ (-a - b - c + 4) := by
    have hh := hd
    try simp only [helim] at hh
    linarith only [hh]
  have hsum : 0 ≤ (15/7 : ℝ) * (1) * (-67*a/180 - 53*b/180 - c/3 + 1)^2 + (19/126 : ℝ) * (1) * (-31*a/76 - 45*b/76 + c)^2 + (38443/574560 : ℝ) * (1) * (-a + b)^2 + (13/28 : ℝ) * ((-a - b - c + 4)) * (-32*a/117 - 85*b/234 - 85*c/234 + 1)^2 + (6347/29484 : ℝ) * ((-a - b - c + 4)) * (a - b/2 - c/2)^2 + (17/126 : ℝ) * ((-a - b - c + 4)) * (-b + c)^2 + (817/252 : ℝ) * ((c)) * (-284*a/817 - 631*b/1634 - 435*c/1634 + 1)^2 + (8431/51471 : ℝ) * ((c)) * (a - 15389*b/16862 - 1473*c/16862)^2 + (17921/944272 : ℝ) * ((c)) * (-b + c)^2 + (775/252 : ℝ) * ((b)) * (-284*a/775 - 207*b/775 - 284*c/775 + 1)^2 + (6961/48825 : ℝ) * ((b)) * (-6214*a/6961 - 747*b/6961 + c)^2 + (1411/48727 : ℝ) * ((b)) * (-a + b)^2 + (775/252 : ℝ) * ((a)) * (-207*a/775 - 284*b/775 - 284*c/775 + 1)^2 + (6961/48825 : ℝ) * ((a)) * (-747*a/6961 - 6214*b/6961 + c)^2 + (1411/48727 : ℝ) * ((a)) * (-a + b)^2 := by positivity
  have hid : ( 4   ) - ( a * b * c + b * c * d + c * d * a + d * a * b ) = (15/7 : ℝ) * (1) * (-67*a/180 - 53*b/180 - c/3 + 1)^2 + (19/126 : ℝ) * (1) * (-31*a/76 - 45*b/76 + c)^2 + (38443/574560 : ℝ) * (1) * (-a + b)^2 + (13/28 : ℝ) * ((-a - b - c + 4)) * (-32*a/117 - 85*b/234 - 85*c/234 + 1)^2 + (6347/29484 : ℝ) * ((-a - b - c + 4)) * (a - b/2 - c/2)^2 + (17/126 : ℝ) * ((-a - b - c + 4)) * (-b + c)^2 + (817/252 : ℝ) * ((c)) * (-284*a/817 - 631*b/1634 - 435*c/1634 + 1)^2 + (8431/51471 : ℝ) * ((c)) * (a - 15389*b/16862 - 1473*c/16862)^2 + (17921/944272 : ℝ) * ((c)) * (-b + c)^2 + (775/252 : ℝ) * ((b)) * (-284*a/775 - 207*b/775 - 284*c/775 + 1)^2 + (6961/48825 : ℝ) * ((b)) * (-6214*a/6961 - 747*b/6961 + c)^2 + (1411/48727 : ℝ) * ((b)) * (-a + b)^2 + (775/252 : ℝ) * ((a)) * (-207*a/775 - 284*b/775 - 284*c/775 + 1)^2 + (6961/48825 : ℝ) * ((a)) * (-747*a/6961 - 6214*b/6961 + c)^2 + (1411/48727 : ℝ) * ((a)) * (-a + b)^2 := by
    try simp only [helim]
    <;> ring
  linarith only [hsum, hid]
example : (∀ (a b c d : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d) (hab : a + b + c + d = 4), a * b * c + b * c * d + c * d * a + d * a * b ≤ 4) := @solution
#print axioms solution
