-- Prove2me | solution 2 for ProblemSpec.Equilibrium.sym_win_prob_entry_utility
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-26T01:21:59.368296+00:00
-- url     : https://prove2.me/submissions/d897a873-58bd-4899-aa9e-8e22593c7d50

import Mathlib
import Definitions.Def_ProblemSpec_Equilibrium_Model

namespace Aux_sym_win_prob
open ProblemSpec.Equilibrium

theorem sym_win_prob_aux (P : Params) (Sr N : ℝ) (hN : 1 < N) (r m : ℝ) (hm : 0 < m) :
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

end Aux_sym_win_prob

open ProblemSpec.Equilibrium in
theorem solution (P : Params) (hP : P.Standing) (Sr Sg N : ℝ) (hSg : 0 ≤ Sg)
    (hN : 1 < N) :
    (∀ r m : ℝ, 0 < m → winProb P Sr N r m r m = 1 / N) ∧
      entryUtility P Sr Sg N =
        P.A / N ^ 2 - P.cg * max (rstar P N Sr - Sr) 0 - P.c1 * Sr
          - P.c2 * (1 / P.p) ^ rstar P N Sr := by
  refine ⟨fun r m hm => Aux_sym_win_prob.sym_win_prob_aux P Sr N hN r m hm, ?_⟩
  have hh : 0 < P.h Sg := hP.2.2.2.2.2.2.2.2.1 Sg hSg
  have hN0 : N ≠ 0 := by intro h; rw [h] at hN; linarith
  have hN1 : 0 < N - 1 := by linarith
  have hA : 0 < P.A := hP.1
  have hw := Aux_sym_win_prob.sym_win_prob_aux P Sr N hN (rstar P N Sr) (mstar P Sg N) (by
    unfold mstar
    positivity)
  unfold entryUtility payoff
  rw [hw]
  unfold cost mstar
  have hmx : max (rstar P N Sr - Sr) 0 = max (rstar P N Sr - Sr) 0 := rfl
  field_simp
  ring
