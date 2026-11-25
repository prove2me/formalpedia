-- Prove2me | solution 1 for SZ.W_ne_val
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T02:32:17.368476+00:00
-- url     : https://prove2.me/submissions/e616316e-eebe-4b66-a04c-1eecd3ed9c9c

import Definitions.Def_SZ_DigitParity
import Mathlib.NumberTheory.Real.Irrational
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Definitions.Def_SZ_CoverGame
import Theorems.Thm_SZ_val_inj
import Theorems.Thm_SZ_coverState_snd_ge_nine

set_option autoImplicit false
open SZ
open Filter Topology
namespace SZ
theorem _root_.solution (k : ℕ) {p q : ℤ} (hq : q < 9) :
    W k ≠ (p : ℝ) + (q : ℝ) * Real.sqrt 3 := by
  intro h
  have h1 := (val_inj h).2
  have h2 := coverState_snd_ge_nine k
  omega
end SZ
