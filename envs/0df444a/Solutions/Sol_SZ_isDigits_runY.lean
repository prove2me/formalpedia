-- Prove2me | solution 1 for SZ.isDigits_runY
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T02:59:55.520421+00:00
-- url     : https://prove2.me/submissions/12ab2138-a1ad-4c36-bf25-32d385bb90b7

import Definitions.Def_SZ_SqrtThree
import Mathlib.Algebra.AlgebraicCard
import Mathlib.SetTheory.Cardinal.Continuum
import Definitions.Def_SZ_CoverTree

set_option autoImplicit false
open SZ
open Filter Topology
namespace SZ
theorem _root_.solution {s₀ : ℤ × ℤ} {d : ℕ → ℤ × ℤ} (hrun : IsRun s₀ d) :
    IsDigits 3 (runY d) :=
  { two_le := by norm_num
    nonneg := fun i => by rcases (hrun i).1.2 with h | h <;> simp [runY, h]
    le_sub_one := fun i => by rcases (hrun i).1.2 with h | h <;> simp [runY, h] }
end SZ
