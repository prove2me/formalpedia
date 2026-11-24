-- Prove2me | solution 1 for PhosphorylationSharpness.DensePositive.nonneg
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T07:20:28.220272+00:00
-- url     : https://prove2.me/submissions/f01a8e5f-7f35-45d3-9234-4f422e5aee12

import Mathlib
import Definitions.Def_proofs_PhosphorylationSharpness_Recurrence

set_option autoImplicit true
open PhosphorylationSharpness
noncomputable section
open Polynomial
namespace PhosphorylationSharpness
namespace DensePositive
theorem _root_.solution {p : ℝ[X]} {m : ℕ} (h : DensePositive p m) (i : ℕ) :
    0 ≤ p.coeff i := by
  by_cases hi : i ≤ m
  · exact (h.1 i hi).le
  · rw [h.2 i (by omega)]
end DensePositive
end PhosphorylationSharpness
