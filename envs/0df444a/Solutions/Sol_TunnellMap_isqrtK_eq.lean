-- Prove2me | solution 1 for TunnellMap.isqrtK_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:40:30.574108+00:00
-- url     : https://prove2.me/submissions/8d91a558-2d05-426a-8f98-35c59d05eaca

import Mathlib
import Definitions.Def_TunnellMap_KernelArith
import Theorems.Thm_TunnellMap_natSqrtK_eq

set_option autoImplicit true
open TunnellMap
namespace TunnellMap
theorem _root_.solution (z : ℤ) : isqrtK z = Int.sqrt z := by
  rw [isqrtK, natSqrtK_eq, Int.sqrt]
end TunnellMap
