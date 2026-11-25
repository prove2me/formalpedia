-- Prove2me | solution 1 for SZ.isDigits_run_snd
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T02:23:25.218095+00:00
-- url     : https://prove2.me/submissions/15d375b0-f03f-47c9-b442-3733e53e1d14

import Definitions.Def_SZ_SqrtThree
import Mathlib.Algebra.AlgebraicCard
import Mathlib.SetTheory.Cardinal.Continuum
import Definitions.Def_SZ_CoverTree

set_option autoImplicit false
open SZ
open Filter Topology
namespace SZ
theorem _root_.solution {s₀ : ℤ × ℤ} {d : ℕ → ℤ × ℤ} (hrun : IsRun s₀ d) :
    IsDigits 3 (fun i => (d i).2) :=
  { two_le := by norm_num
    nonneg := fun i => by rcases (hrun i).1.2 with h | h <;> omega
    le_sub_one := fun i => by rcases (hrun i).1.2 with h | h <;> omega }
end SZ
