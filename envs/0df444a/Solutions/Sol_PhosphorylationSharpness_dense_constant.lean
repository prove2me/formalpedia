-- Prove2me | solution 1 for PhosphorylationSharpness.dense_constant
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T07:23:09.602368+00:00
-- url     : https://prove2.me/submissions/1a0912ea-ad5e-45d4-b478-71bc2dc30abc

import Mathlib
import Definitions.Def_proofs_PhosphorylationSharpness_Recurrence

set_option autoImplicit true
open PhosphorylationSharpness
noncomputable section
open Polynomial
namespace PhosphorylationSharpness
theorem _root_.solution (c : ℝ) (hc : 0 < c) : DensePositive (C c) 0 := by
  constructor
  · intro i hi
    have : i = 0 := by omega
    subst i
    simpa using hc
  · intro i hi
    simp [coeff_C, show i ≠ 0 by omega]
end PhosphorylationSharpness
