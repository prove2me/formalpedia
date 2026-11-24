-- Prove2me | solution 1 for PhosphorylationSharpness.conversion_root
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T07:23:49.523147+00:00
-- url     : https://prove2.me/submissions/d2403af3-aada-47d2-874e-cf036aad33a0

import Definitions.Def_proofs_PhosphorylationSharpness_Recurrence
import Definitions.Def_proofs_PhosphorylationSharpness_Conversion
import Theorems.Thm_PhosphorylationSharpness_quotient_identity

set_option autoImplicit true
open PhosphorylationSharpness
noncomputable section
open Polynomial Filter
open scoped Topology
namespace PhosphorylationSharpness
theorem _root_.solution (p q : ℝ[X]) (r x : ℝ)
    (hx : (x-1)*p.eval (ratio x)-2*q.eval (ratio x)=0) :
    (x-1)*((rawB p q r).eval (ratio x)-r*(rawD p q r).eval (ratio x)) =
      2*(r-ratio x)*(rawD p q r).eval (ratio x) := by
  have h := congrArg (fun z : ℝ[X] => z.eval (ratio x)) (quotient_identity p q r)
  simp only [eval_mul, eval_sub, eval_X, eval_C, conversionNumerator] at h
  simp only [rawB, rawD, eval_add, eval_sub, eval_mul, eval_C]
  dsimp [ratio] at h hx ⊢
  linear_combination 8*h + (q.eval r*x+4*r*p.eval r-q.eval r)*hx
end PhosphorylationSharpness
