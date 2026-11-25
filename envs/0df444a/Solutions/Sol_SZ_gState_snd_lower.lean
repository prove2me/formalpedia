-- Prove2me | solution 1 for SZ.gState_snd_lower
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T02:36:39.83878+00:00
-- url     : https://prove2.me/submissions/6f333919-624e-4951-a780-54fb78a47ece

import Definitions.Def_SZ_SqrtThree
import Mathlib.Algebra.AlgebraicCard
import Mathlib.SetTheory.Cardinal.Continuum
import Definitions.Def_SZ_CoverTree
import Theorems.Thm_SZ_runState_snd_lower
import Theorems.Thm_SZ_runState_gDigit
import Theorems.Thm_SZ_gIsRun

set_option autoImplicit false
open SZ
open Filter Topology
namespace SZ
theorem _root_.solution {s : ℤ × ℤ} (h : GStart s) (k : ℕ) :
    3 ^ k * (s.2 - 3) + 3 ≤ (gState s k).2 := by
  have := runState_snd_lower (gIsRun h) k
  rwa [runState_gDigit] at this
end SZ
