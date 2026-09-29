-- Prove2me | solution 1 for PachDeZeeuw.Algebraic.totalDegree_pderiv_le
-- status  : ACCEPTED   (prove)
-- author  : @mysticflounder
-- created : 2026-09-17T01:43:55.703718+00:00
-- url     : https://prove2.me/submissions/1d0fe307-ac24-45a4-a489-1828de38a9f6

import Mathlib
import Definitions.Def_PdzPrelim
import Theorems.Thm_PachDeZeeuw_Algebraic_totalDegree_pderiv_le_sub_one

open EuclideanGeometry
open scoped Topology
open PachDeZeeuw.Algebraic
open PachDeZeeuw.Algebraic.PlaneCurve

open PachDeZeeuw.Algebraic in
theorem solution (h : MvPolynomial (Fin 2) ℝ) (i : Fin 2) :
    (MvPolynomial.pderiv i h).totalDegree ≤ h.totalDegree := by
  by_cases hpos : 0 < h.totalDegree
  · have hle := totalDegree_pderiv_le_sub_one h i hpos
    omega
  · have hdeg0 : h.totalDegree = 0 := by omega
    have hC : h = MvPolynomial.C (MvPolynomial.coeff 0 h) := by
      exact (MvPolynomial.totalDegree_eq_zero_iff_eq_C).mp hdeg0
    rw [hC]
    simp
