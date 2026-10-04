-- Prove2me | solution 1 for SMHiggsPotential.scalarLagrangian_tadpole
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-04T03:23:56.419363+00:00
-- url     : https://prove2.me/submissions/a484f7ff-7e09-4758-8a67-c489d3e213bd

import Mathlib
import Definitions.Def_SMHiggsPotential_Defs
open Complex

open SMHiggsPotential in
theorem solution (g M mh βh : ℝ) :
    HasDerivAt (fun H : ℝ => scalarLagrangian g M mh βh H 0 0) (-(2 * M / g) * βh) 0 := by
  have e : (fun H : ℝ => scalarLagrangian g M mh βh H 0 0) = fun H : ℝ =>
      ((-(βh * (2 * M ^ 2 / g ^ 2)) + 2 * M ^ 4 / g ^ 2 * alphaH M mh)
        + (-(βh * (2 * M / g))) * H + (-(1 / 2) * mh ^ 2 - βh / 2) * H ^ 2
        + (-(g * M * alphaH M mh)) * H ^ 3 + (-(1 / 8) * g ^ 2 * alphaH M mh) * H ^ 4) := by
    funext H
    simp only [scalarLagrangian, map_zero]
    ring
  rw [e]
  have h := ((((hasDerivAt_const (0:ℝ) ((-(βh * (2 * M ^ 2 / g ^ 2)) + 2 * M ^ 4 / g ^ 2 * alphaH M mh))).add
      ((hasDerivAt_id (0:ℝ)).const_mul (-(βh * (2 * M / g))))).add
      ((hasDerivAt_pow 2 (0:ℝ)).const_mul (-(1 / 2) * mh ^ 2 - βh / 2))).add
      ((hasDerivAt_pow 3 (0:ℝ)).const_mul (-(g * M * alphaH M mh)))).add
      ((hasDerivAt_pow 4 (0:ℝ)).const_mul (-(1 / 8) * g ^ 2 * alphaH M mh))
  exact h.congr_deriv (by norm_num <;> ring)
