-- Prove2me | solution 1 for ProblemSpec.Equilibrium.eq_A_5
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-26T01:38:08.751066+00:00
-- url     : https://prove2.me/submissions/34271c55-88dd-4cc1-96a7-5d3c94e59bfa

import Mathlib
import Definitions.Def_ProblemSpec_Equilibrium_Model

namespace Aux_eqA5
open ProblemSpec.Equilibrium

theorem sym_win (P : Params) (Sr N : ℝ) (hN : 1 < N) (r m : ℝ) (hm : 0 < m) :
    winProb P Sr N r m r m = 1 / N := by
  unfold winProb
  have he := Real.exp_pos (quality P Sr r / P.μ)
  have hN0 : N ≠ 0 := by intro h; rw [h] at hN; linarith
  have hme : m * Real.exp (quality P Sr r / P.μ) ≠ 0 := (mul_pos hm he).ne'
  set a := m * Real.exp (quality P Sr r / P.μ) with ha
  have : (N - 1) * m * Real.exp (quality P Sr r / P.μ) = (N - 1) * a := by rw [ha]; ring
  rw [this]
  have h2 : a + (N - 1) * a = N * a := by ring
  rw [h2]
  field_simp

theorem closed (P : Params) (hP : P.Standing) (Sr Sg N : ℝ) (hSg : 0 ≤ Sg)
    (hN : 1 < N) :
      entryUtility P Sr Sg N =
        P.A / N ^ 2 - P.cg * max (rstar P N Sr - Sr) 0 - P.c1 * Sr
          - P.c2 * (1 / P.p) ^ rstar P N Sr := by
  have hh : 0 < P.h Sg := hP.2.2.2.2.2.2.2.2.1 Sg hSg
  have hN0 : N ≠ 0 := by intro h; rw [h] at hN; linarith
  have hN1 : 0 < N - 1 := by linarith
  have hA : 0 < P.A := hP.1
  have hw := sym_win P Sr N hN (rstar P N Sr) (mstar P Sg N) (by
    unfold mstar
    positivity)
  unfold entryUtility payoff
  rw [hw]
  unfold cost mstar
  field_simp
  ring

end Aux_eqA5

open ProblemSpec.Equilibrium in
theorem solution (P : Params) (hP : P.Standing) (Sr Sg N : ℝ) (hSr : 0 ≤ Sr) (hSg : 0 ≤ Sg)
    (hN : 1 < N) (hI : rstar P N Sr = Sr) :
    entryUtility P Sr Sg N = P.s ↔ N = N1closed P Sr := by
  rw [Aux_eqA5.closed P hP Sr Sg N hSg hN, hI]
  have hA : 0 < P.A := hP.1
  have hs : 0 < P.s := hP.2.2.2.2.2.2.2.1
  have hc1 : 0 ≤ P.c1 := hP.2.2.2.2.2.1.1
  have hc2 : 0 < P.c2 := hP.2.2.2.1
  have hp : 0 < P.p := hP.2.2.2.2.2.2.1.1
  have hpow : 0 < (1 / P.p) ^ Sr := Real.rpow_pos_of_pos (by positivity) Sr
  have hD : 0 < P.s + P.c1 * Sr + P.c2 * (1 / P.p) ^ Sr := by positivity
  have hN0 : 0 < N := by linarith
  have hm : max (Sr - Sr) 0 = 0 := by simp
  rw [hm]
  unfold N1closed
  set D := P.s + P.c1 * Sr + P.c2 * (1 / P.p) ^ Sr with hDdef
  constructor
  · intro h
    have h1 : P.A / N ^ 2 = D := by rw [hDdef]; linarith
    have h2 : N ^ 2 = P.A / D := by
      rw [← h1]; field_simp
    rw [← h2, Real.sqrt_sq hN0.le]
  · intro h
    have h2 : N ^ 2 = P.A / D := by
      rw [h, Real.sq_sqrt (by positivity)]
    rw [h2]
    have : P.A / (P.A / D) = D := by field_simp
    rw [this, hDdef]; ring
