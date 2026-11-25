-- Prove2me | solution 1 for SZ.run_coupling
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T03:18:23.577972+00:00
-- url     : https://prove2.me/submissions/0ce764b7-4f7b-421e-8a96-21eb6c3e6d6a

import Definitions.Def_SZ_SqrtThree
import Mathlib.Algebra.AlgebraicCard
import Mathlib.SetTheory.Cardinal.Continuum
import Definitions.Def_SZ_CoverTree
import Theorems.Thm_SZ_run_translate
import Theorems.Thm_SZ_digitReal_runY

set_option autoImplicit false
open SZ
open Filter Topology
namespace SZ
theorem _root_.solution {d : ℕ → ℤ × ℤ} (hrun : IsRun (-12, 9) d) :
    4 + digitReal 3 (fun i => (d i).1) = Real.sqrt 3 * (2 + digitReal 3 (runY d)) := by
  have h := run_translate hrun
  rw [digitReal_runY hrun]
  have hs : Real.sqrt 3 * Real.sqrt 3 = 3 := Real.mul_self_sqrt (by norm_num)
  nlinarith [h, hs]
end SZ
