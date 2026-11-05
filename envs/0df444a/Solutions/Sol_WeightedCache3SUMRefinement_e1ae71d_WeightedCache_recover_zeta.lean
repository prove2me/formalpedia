-- Prove2me | solution 1 for WeightedCache3SUMRefinement_e1ae71d.WeightedCache.recover_zeta
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T10:09:02.306142+00:00
-- url     : https://prove2.me/submissions/e1e5ca1d-4e7b-4538-b83d-9969432c8dff

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
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Cache
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_WeightedCache_zeta_euler
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_WeightedCache_recover_correct

set_option autoImplicit false
open WeightedCache3SUMRefinement_e1ae71d
open WeightedCache3SUMRefinement_e1ae71d.WeightedCache
open Finset
namespace WeightedCache3SUMRefinement_e1ae71d.WeightedCache
theorem _root_.solution {N h : ℕ} (B : Finset (Word N))
    (hbase : ∀ R, rank R ≤ h → R ∈ B) (f values : Word N → ℤ)
    (hf : ∀ A, f A ≠ 0 → rank A = h)
    (hbank : ∀ R ∈ B, values R = zeta f R) (R : Word N) :
    recover B values h (rank R) R = zeta f R :=
  recover_correct B hbase values (zeta f) hbank (zeta_euler f h hf) _ _ le_rfl
end WeightedCache3SUMRefinement_e1ae71d.WeightedCache
