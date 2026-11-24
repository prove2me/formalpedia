-- Prove2me | solution 1 for PhosphorylationSharpness.ratio_injective
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T07:23:17.508977+00:00
-- url     : https://prove2.me/submissions/84da6649-54b0-439a-a43a-2e343f61caf5

import Mathlib
import Definitions.Def_proofs_PhosphorylationSharpness_Recurrence

set_option autoImplicit true
open PhosphorylationSharpness
noncomputable section
open Polynomial
namespace PhosphorylationSharpness
theorem _root_.solution {x y : ℝ} (hx : 1 < x) (hy : 1 < y)
    (h : ratio x = ratio y) : x = y := by
  dsimp [ratio] at h
  nlinarith
end PhosphorylationSharpness
