-- Prove2me | solution 1 for PhosphorylationSharpness.ratio_pos
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T07:20:28.817136+00:00
-- url     : https://prove2.me/submissions/89e7caf8-6d64-4f42-b8e5-9513e2f28e04

import Mathlib
import Definitions.Def_proofs_PhosphorylationSharpness_Recurrence

set_option autoImplicit true
open PhosphorylationSharpness
noncomputable section
open Polynomial
namespace PhosphorylationSharpness
theorem _root_.solution {x : ℝ} (hx : 1 < x) : 0 < ratio x := by
  dsimp [ratio]
  nlinarith
end PhosphorylationSharpness
