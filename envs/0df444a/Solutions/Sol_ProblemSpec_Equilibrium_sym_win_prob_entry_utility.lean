-- Prove2me | solution 1 for ProblemSpec.Equilibrium.sym_win_prob_entry_utility
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-26T01:21:10.200024+00:00
-- url     : https://prove2.me/submissions/2892f1e1-1332-41f3-928e-5739a4af24d0

import Mathlib
import Definitions.Def_ProblemSpec_Equilibrium_Model

namespace ProblemSpec.Equilibrium

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

end ProblemSpec.Equilibrium

open ProblemSpec.Equilibrium in
theorem solution (P : Params) (hP : P.Standing) (Sr Sg N : ℝ) (hSg : 0 ≤ Sg)
    (hN : 1 < N) :
    (∀ r m : ℝ, 0 < m → winProb P Sr N r m r m = 1 / N) ∧
      entryUtility P Sr Sg N =
        P.A / N ^ 2 - P.cg * max (rstar P N Sr - Sr) 0 - P.c1 * Sr
          - P.c2 * (1 / P.p) ^ rstar P N Sr := by
  refine ⟨fun r m hm => sym_win_prob_aux P Sr N hN r m hm, ?_⟩
  have hh : 0 < P.h Sg := hP.2.2.2.2.2.2.2.2.1 Sg hSg
  have hN0 : N ≠ 0 := by intro h; rw [h] at hN; linarith
  have hw := sym_win_prob_aux P Sr N hN (rstar P N Sr) (mstar P Sg N) (by
    unfold mstar
    have : 0 < P.A := hP.1
    positivity)
  unfold entryUtility payoff
  rw [hw]
  unfold cost mstar
  field_simp
  ring
