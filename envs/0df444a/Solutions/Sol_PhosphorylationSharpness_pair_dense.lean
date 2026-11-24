-- Prove2me | solution 1 for PhosphorylationSharpness.pair_dense
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T07:26:12.653441+00:00
-- url     : https://prove2.me/submissions/6c1e203c-8ec9-4715-a126-9bda38b6e585

import Mathlib
import Definitions.Def_proofs_PhosphorylationSharpness_Recurrence
import Theorems.Thm_PhosphorylationSharpness_dense_constant
import Theorems.Thm_PhosphorylationSharpness_next_dense

set_option autoImplicit true
open PhosphorylationSharpness
noncomputable section
open Polynomial
namespace PhosphorylationSharpness
theorem _root_.solution (m : ℕ) :
    DensePositive (pair m).1 m ∧ DensePositive (pair m).2 m := by
  induction m with
  | zero =>
    exact ⟨by simpa [pair] using dense_constant 1 (by norm_num),
      by simpa [pair] using dense_constant (1/2) (by norm_num)⟩
  | succ m ih =>
    exact next_dense ih.1 ih.2 (by nlinarith [Nat.cast_nonneg (α := ℝ) m])
      (by nlinarith [Nat.cast_nonneg (α := ℝ) m])
end PhosphorylationSharpness
