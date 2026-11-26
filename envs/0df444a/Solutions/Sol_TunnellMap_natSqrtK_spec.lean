-- Prove2me | solution 1 for TunnellMap.natSqrtK_spec
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:37:52.73093+00:00
-- url     : https://prove2.me/submissions/8a33adac-7bbf-4232-84ef-47f36d6c08c1

import Mathlib
import Definitions.Def_TunnellMap_KernelArith
import Theorems.Thm_TunnellMap_sqrtBSAux_spec

set_option autoImplicit true
open TunnellMap
namespace TunnellMap
theorem _root_.solution (n : ℕ) :
    natSqrtK n * natSqrtK n ≤ n ∧ n < (natSqrtK n + 1) * (natSqrtK n + 1) := by
  refine sqrtBSAux_spec n (n + 1) 0 (n + 1) (by omega) (by omega) (by omega) ?_
  nlinarith
end TunnellMap
