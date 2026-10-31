-- Prove2me | solution 1 for PermLimits.Cauchy.density_stepLimit_close
-- status  : ACCEPTED   (prove)
-- author  : @Nihal
-- created : 2026-10-30T21:40:54.223702+00:00
-- url     : https://prove2.me/submissions/49e6014e-e166-49c9-998f-2e08d14edd1e

import Theorems.Thm_PermLimits_Existence_density_stepLimit_close

import Mathlib
import Definitions.Def_PermLimits_Shared_PermDensity
import Definitions.Def_PermLimits_Shared_LimitMeasure
import Definitions.Def_PermLimits_Shared_StepLimit
open PermLimits.Shared

theorem solution {k n : ℕ} (τ : Equiv.Perm (Fin k)) (π : Equiv.Perm (Fin n))
    (hk : 0 < k) (hkn : k ≤ n) :
    |permDensity τ π - limitDensity τ (stepLimit π)| ≤ (1 / (n : ℝ)) * (Nat.choose k 2 : ℝ) :=
  PermLimits.Existence.density_stepLimit_close τ π hk hkn
