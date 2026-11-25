-- Prove2me | solution 1 for SZ.isDigits_run_fst
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T01:12:10.933853+00:00
-- url     : https://prove2.me/submissions/d71a6680-56b5-4ee9-abca-0885fe089b75

import Definitions.Def_SZ_SqrtThree
import Mathlib.Algebra.AlgebraicCard
import Mathlib.SetTheory.Cardinal.Continuum
import Definitions.Def_SZ_CoverTree

set_option autoImplicit false
open SZ
open Filter Topology
namespace SZ
theorem _root_.solution {s₀ : ℤ × ℤ} {d : ℕ → ℤ × ℤ} (hrun : IsRun s₀ d) :
    IsDigits 3 (fun i => (d i).1) :=
  { two_le := by norm_num
    nonneg := fun i => by rcases (hrun i).1.1 with h | h <;> omega
    le_sub_one := fun i => by rcases (hrun i).1.1 with h | h <;> omega }
end SZ
