-- Prove2me | solution 1 for ProblemSpec.Equilibrium.eq_A_3
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T17:07:32.50204+00:00
-- url     : https://prove2.me/submissions/55c0fc40-0468-448a-9d16-69c025a4f753

import Mathlib
import Definitions.Def_ProblemSpec_Equilibrium_Model
set_option autoImplicit false
open ProblemSpec.Equilibrium

theorem solution (P : Params) (hP : P.Standing) (Sr Sg N r m : ℝ) (hSg : 0 ≤ Sg) (hN : 1 < N)
    (hm : 0 < m) :
    HasDerivAt (fun x => payoff P Sr Sg N r x r m)
        (P.A * ((N - 1) * m / (m * N) ^ 2) - P.h Sg) m ∧
      (P.A * ((N - 1) * m / (m * N) ^ 2) - P.h Sg = 0 ↔ m = mstar P Sg N) := by
  obtain ⟨hA, -, -, -, -, -, -, -, hh, -⟩ := hP
  have hhS : 0 < P.h Sg := hh Sg hSg
  set E := Real.exp (quality P Sr r / P.μ) with hE
  have hEpos : 0 < E := Real.exp_pos _
  have hN1 : 0 < N - 1 := by linarith
  have hden : m * E + (N - 1) * m * E ≠ 0 := by positivity
  have h1 : HasDerivAt (fun x : ℝ => x * E) E m := by simpa using (hasDerivAt_id m).mul_const E
  have h2 : HasDerivAt (fun x : ℝ => x * E + (N - 1) * m * E) E m := h1.add_const _
  have h3 := h1.div h2 hden
  have h4 := (h3.mul_const P.A).sub (((hasDerivAt_id m).const_mul (P.h Sg)).const_add (P.cg * max (r - Sr) 0 + P.c1 * Sr + P.c2 * (1 / P.p) ^ r))
  have hval : (E * (m * E + (N - 1) * m * E) - m * E * E) / (m * E + (N - 1) * m * E) ^ 2 * P.A - P.h Sg * 1
      = P.A * ((N - 1) * m / (m * N) ^ 2) - P.h Sg := by
    field_simp
    ring
  have hD : HasDerivAt (fun x => payoff P Sr Sg N r x r m)
        (P.A * ((N - 1) * m / (m * N) ^ 2) - P.h Sg) m := by
    have h5 : HasDerivAt (fun x : ℝ => x * E / (x * E + (N - 1) * m * E) * P.A -
        (P.cg * max (r - Sr) 0 + P.c1 * Sr + P.c2 * (1 / P.p) ^ r + P.h Sg * x))
        ((E * (m * E + (N - 1) * m * E) - m * E * E) / (m * E + (N - 1) * m * E) ^ 2 * P.A - P.h Sg * 1) m := h4
    rw [hval] at h5
    exact h5
  refine ⟨hD, ?_⟩
  unfold mstar
  have hN0 : N ≠ 0 := by positivity
  have hm0 : m ≠ 0 := hm.ne'
  have e : P.A * ((N - 1) * m / (m * N) ^ 2) = P.A * (N - 1) / (m * N ^ 2) := by
    field_simp
  rw [e, sub_eq_zero, eq_div_iff (by positivity), div_eq_iff (by positivity)]
  constructor <;> intro h <;> nlinarith
