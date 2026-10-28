-- Prove2me | solution 1 for ProblemSpec.Equilibrium.region0_utility_increases
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-26T01:36:30.888088+00:00
-- url     : https://prove2.me/submissions/4cc30144-8b7c-44e9-8e71-452e4ba3a68a

import Mathlib
import Definitions.Def_ProblemSpec_Equilibrium_Model

namespace Aux_region0
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

end Aux_region0

open ProblemSpec.Equilibrium in
theorem solution (P : Params) (hP : P.Standing) (Sr Sr' Sg N : ℝ)
    (hSr : 0 ≤ Sr) (hlt : Sr < Sr') (hSg : 0 ≤ Sg) (hN : 1 < N) (hG : Guessing P N Sr') :
    entryUtility P Sr Sg N < entryUtility P Sr' Sg N := by
  have hG0 : Guessing P N Sr := ⟨hG.1, lt_trans hlt hG.2⟩
  rw [Aux_region0.closed P hP Sr Sg N hSg hN, Aux_region0.closed P hP Sr' Sg N hSg hN]
  have e1 : rstar P N Sr = rg P N := by unfold rstar; rw [if_pos hG0]
  have e2 : rstar P N Sr' = rg P N := by unfold rstar; rw [if_pos hG]
  rw [e1, e2, max_eq_left (by linarith [hG.2]), max_eq_left (by linarith [hG.2])]
  have hcg : P.c1 < P.cg := hP.2.2.2.2.2.1.2
  nlinarith
