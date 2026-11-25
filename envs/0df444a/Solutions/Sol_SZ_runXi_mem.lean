-- Prove2me | solution 1 for SZ.runXi_mem
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T02:25:21.385794+00:00
-- url     : https://prove2.me/submissions/7df5ffef-4c2a-40b7-8506-dad7d86ed8d0

import Definitions.Def_SZ_SqrtThree
import Mathlib.Algebra.AlgebraicCard
import Mathlib.SetTheory.Cardinal.Continuum
import Definitions.Def_SZ_CoverTree
import Theorems.Thm_SZ_isDigits_run_fst
import Theorems.Thm_SZ_digitReal_le_one
import Theorems.Thm_SZ_digitReal_nonneg


set_option autoImplicit false
open SZ
open Filter Topology
namespace SZ
theorem _root_.solution {s₀ : ℤ × ℤ} {d : ℕ → ℤ × ℤ} (hrun : IsRun s₀ d) :
    4 / 3 ≤ runXi d ∧ runXi d ≤ 5 / 3 := by
  have h0 := digitReal_nonneg (isDigits_run_fst hrun)
  have h1 := digitReal_le_one (isDigits_run_fst hrun)
  constructor <;> · rw [runXi]; linarith
end SZ
