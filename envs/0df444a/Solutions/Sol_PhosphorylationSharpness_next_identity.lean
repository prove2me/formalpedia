-- Prove2me | solution 1 for PhosphorylationSharpness.next_identity
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T07:23:13.817862+00:00
-- url     : https://prove2.me/submissions/aceac7ee-eb9d-4fd0-99a9-6bf53978df82

import Mathlib
import Definitions.Def_proofs_PhosphorylationSharpness_Recurrence

set_option autoImplicit true
open PhosphorylationSharpness
noncomputable section
open Polynomial
namespace PhosphorylationSharpness
theorem _root_.solution (a b x : ℝ) (p q : ℝ[X]) :
    (x-1)*(nextN a b p q).eval (ratio x) - 2*(nextJ a b p q).eval (ratio x) =
    (x-a)*(x-b)*((x-1)*p.eval (ratio x)-2*q.eval (ratio x)) := by
  simp only [nextN, nextJ, eval_add, eval_mul, eval_C, eval_X]
  dsimp [ratio]
  ring
end PhosphorylationSharpness
