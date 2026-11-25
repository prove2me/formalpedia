-- Prove2me | solution 1 for SZ.runVal_ne
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T02:32:23.585944+00:00
-- url     : https://prove2.me/submissions/5eceb7e6-2f5a-4e7a-8b8c-eeabb51ca9bf

import Definitions.Def_SZ_SqrtThree
import Mathlib.Algebra.AlgebraicCard
import Mathlib.SetTheory.Cardinal.Continuum
import Definitions.Def_SZ_CoverTree
import Theorems.Thm_SZ_runState_snd_lower
import Theorems.Thm_SZ_val_inj


set_option autoImplicit false
open SZ
open Filter Topology
namespace SZ
theorem _root_.solution {s₀ : ℤ × ℤ} {d : ℕ → ℤ × ℤ} (hrun : IsRun s₀ d) (hq : 4 ≤ s₀.2)
    (k : ℕ) {p q : ℤ} (hqle : q ≤ 3) :
    valS (runState s₀ d k) ≠ (p : ℝ) + (q : ℝ) * Real.sqrt 3 := by
  intro h
  have hb := runState_snd_lower hrun k
  have h1 : (1 : ℤ) ≤ 3 ^ k := one_le_pow₀ (by norm_num)
  have h2 : (runState s₀ d k).2 = q := (val_inj h).2
  have h4 : (1 : ℤ) ≤ s₀.2 - 3 := by omega
  have h5 : (1 : ℤ) * 1 ≤ 3 ^ k * (s₀.2 - 3) :=
    mul_le_mul h1 h4 zero_le_one (by positivity)
  omega
end SZ
