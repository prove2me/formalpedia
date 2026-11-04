-- Prove2me | solution 1 for WeightedCache.recover_zeta
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T06:29:02.966208+00:00
-- url     : https://prove2.me/submissions/0d371623-7b5d-4837-a07e-eab20d82c516

import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Real.Basic
import Mathlib.Data.Fin.VecNotation
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Definitions.Def_Submission_Weighted_Cache
import Theorems.Thm_WeightedCache_zeta_euler
import Theorems.Thm_WeightedCache_recover_correct

set_option autoImplicit false
open WeightedCache
open Finset
namespace WeightedCache
theorem _root_.solution {N h : ℕ} (B : Finset (Word N))
    (hbase : ∀ R, rank R ≤ h → R ∈ B) (f values : Word N → ℤ)
    (hf : ∀ A, f A ≠ 0 → rank A = h)
    (hbank : ∀ R ∈ B, values R = zeta f R) (R : Word N) :
    recover B values h (rank R) R = zeta f R :=
  recover_correct B hbase values (zeta f) hbank (zeta_euler f h hf) _ _ le_rfl
end WeightedCache
