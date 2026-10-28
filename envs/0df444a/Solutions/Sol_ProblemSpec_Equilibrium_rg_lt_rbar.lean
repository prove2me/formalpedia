-- Prove2me | solution 1 for ProblemSpec.Equilibrium.rg_lt_rbar
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-26T01:34:52.524772+00:00
-- url     : https://prove2.me/submissions/6d76f200-1b85-4d79-887e-4b57fbd7db80

import Mathlib
import Definitions.Def_ProblemSpec_Equilibrium_Model

open ProblemSpec.Equilibrium in
theorem solution (P : Params) (hP : P.Standing) (N : ℝ) (hN : 1 < N) (hg : 0 < rgArg P N) :
    rg P N < rbar P N := by
  obtain ⟨hA, hw, hμ, hc2, ⟨hν0, hν1⟩, ⟨hc1, hcg⟩, ⟨hp0, hp1⟩, hs, _, _⟩ := hP
  have hL : 0 < L P := by
    unfold L
    apply Real.log_pos
    rw [lt_one_div (by norm_num) hp0]; simpa using hp1
  have hN1 : 0 < N - 1 := by linarith
  have hX : 0 < (N - 1) / N ^ 2 * (P.w / P.μ) * (P.A / P.c2) * (1 / L P) := by positivity
  have hcgpos : 0 < P.cg / P.c2 * (1 / L P) := by
    have : 0 < P.cg := by linarith
    positivity
  have hlt : rgArg P N < rbarArg P N := by
    unfold rgArg rbarArg
    have e : (N - 1) / N ^ 2 * (P.ν * P.w / P.μ) * (P.A / P.c2) * (1 / L P)
        = P.ν * ((N - 1) / N ^ 2 * (P.w / P.μ) * (P.A / P.c2) * (1 / L P)) := by
      rw [mul_div_assoc]; ring
    rw [e]
    nlinarith
  unfold rg rbar
  apply div_lt_div_of_pos_right _ hL
  exact Real.log_lt_log hg hlt
