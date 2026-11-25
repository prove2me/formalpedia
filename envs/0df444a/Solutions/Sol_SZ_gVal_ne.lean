-- Prove2me | solution 1 for SZ.gVal_ne
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T02:37:04.205646+00:00
-- url     : https://prove2.me/submissions/cb44768e-f9dc-46ae-8f2a-376702ad9a60

import Definitions.Def_SZ_SqrtThree
import Mathlib.Algebra.AlgebraicCard
import Mathlib.SetTheory.Cardinal.Continuum
import Definitions.Def_SZ_CoverTree
import Theorems.Thm_SZ_runVal_ne
import Theorems.Thm_SZ_runState_gDigit
import Theorems.Thm_SZ_gIsRun

set_option autoImplicit false
open SZ
open Filter Topology
namespace SZ
theorem _root_.solution {s : ℤ × ℤ} (h : GStart s) (k : ℕ) {p q : ℤ} (hq : q ≤ 3) :
    valS (gState s k) ≠ (p : ℝ) + (q : ℝ) * Real.sqrt 3 := by
  have := runVal_ne (gIsRun h) h.2.2 k (p := p) (q := q) hq
  rwa [runState_gDigit] at this
end SZ
