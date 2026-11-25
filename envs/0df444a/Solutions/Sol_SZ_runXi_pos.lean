-- Prove2me | solution 1 for SZ.runXi_pos
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T03:00:01.8256+00:00
-- url     : https://prove2.me/submissions/bfc041e1-1ed5-4dfb-b369-c1535be55293

import Definitions.Def_SZ_SqrtThree
import Mathlib.Algebra.AlgebraicCard
import Mathlib.SetTheory.Cardinal.Continuum
import Definitions.Def_SZ_CoverTree
import Theorems.Thm_SZ_runXi_mem

set_option autoImplicit false
open SZ
open Filter Topology
namespace SZ
theorem _root_.solution {s₀ : ℤ × ℤ} {d : ℕ → ℤ × ℤ} (hrun : IsRun s₀ d) : 0 < runXi d :=
  lt_of_lt_of_le (by norm_num) (runXi_mem hrun).1
end SZ
