-- Prove2me | solution 1 for SymPolyOpt.PowerSumLB.hankel_succ_posSemidef
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T03:27:36.85144+00:00
-- url     : https://prove2.me/submissions/167e5ef6-8f07-48a7-8fc0-24fd7be2f4b2

import Mathlib
import Definitions.Def_SymPolyOpt_PowerSumLB_Setting

set_option autoImplicit false
open SymPolyOpt.PowerSumLB

theorem solution (n : ℕ) :
    ∀ (s : ℕ → ℝ) (r : ℕ), r + 1 ≤ n → (hankel n s).PosSemidef →
      (hankel (r + 1) s).PosSemidef := by
  intro s r hr h
  have := h.submatrix (Fin.castLE hr)
  convert this using 1
  ext i j
  simp [hankel]
