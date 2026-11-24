-- Prove2me | solution 1 for PhosphorylationSharpness.root_totals
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T07:25:56.497601+00:00
-- url     : https://prove2.me/submissions/60b79613-c7e9-49d6-a902-501959551ca7

import Definitions.Def_proofs_PhosphorylationSharpness_Conversion
import Definitions.Def_proofs_PhosphorylationSharpness_Source
import Definitions.Def_proofs_PhosphorylationSharpness_Assembly
import Theorems.Thm_PhosphorylationSharpness_ratio_pos


set_option autoImplicit true
open PhosphorylationSharpness
noncomputable section
open Polynomial Filter
open scoped Topology BigOperators
namespace PhosphorylationSharpness
theorem _root_.solution (x r b d : ℝ) (hx : 1 < x) (hd : 0 < d)
    (hrel : (x-1)*(b-r*d)=2*(r-ratio x)*d) :
    ratio x*rootF x*(1+rootS x d*b)=2*r ∧
    rootF x*(1+rootS x d*ratio x*d)=2 ∧
    rootS x d*((1+ratio x)*d)+ratio x*rootS x d*rootF x*(b+d)=2*(r+1) := by
  have hu := ratio_pos hx
  have hx1 : x+1 ≠ 0 := by linarith
  have hx2 : x^2-1 ≠ 0 := by nlinarith
  have hd0 := ne_of_gt hd
  dsimp [rootS, rootF, ratio] at hrel ⊢
  constructor
  · field_simp
    nlinarith [hrel]
  constructor
  · field_simp
    ring
  · field_simp
    nlinarith [hrel]
end PhosphorylationSharpness
