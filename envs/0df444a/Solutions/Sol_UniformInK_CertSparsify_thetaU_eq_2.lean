-- Prove2me | solution 2 for UniformInK.CertSparsify.thetaU_eq
-- status  : ACCEPTED   (prove)
-- author  : @nonlocally
-- created : 2026-11-05T18:24:46.467084+00:00
-- url     : https://prove2.me/submissions/56ecd8d9-d786-4b3a-88b5-1f4b662e8a5f

import Definitions.Def_UniformInK_Spars_Defs

set_option autoImplicit false

open UniformInK

theorem solution (τ i : ℕ) : thetaU τ i = if i = 0 then 1 else 4 * τ ^ (2 * i - 1) := by
  cases i with
  | zero => rfl
  | succ i => simp [thetaU, show 2 * (i + 1) - 1 = 2 * i + 1 by omega]
