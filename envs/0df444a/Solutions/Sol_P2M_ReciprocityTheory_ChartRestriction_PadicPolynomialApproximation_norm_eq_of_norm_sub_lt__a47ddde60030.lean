-- Prove2me | solution 1 for P2M_ReciprocityTheory_ChartRestriction_PadicPolynomialApproximation_norm_eq_of_norm_sub_lt__a47ddde60030
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:42:16.069839+00:00
-- url     : https://prove2.me/submissions/f5fd4594-ec6d-416e-9980-6dd07bca2706

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_NormEqOfNormSubLt

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.PadicPolynomialApproximation
open Polynomial Finset
variable (l : ℕ) [Fact l.Prime]
namespace ReciprocityTheory.ChartRestriction.PadicPolynomialApproximation
theorem _root_.solution {a b : ℂ_[l]} (h : ‖a - b‖ < ‖b‖) : ‖a‖ = ‖b‖ := by
  have := IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm (x := a - b) (y := b) h.ne
  rwa [sub_add_cancel, max_eq_right h.le] at this
end ReciprocityTheory.ChartRestriction.PadicPolynomialApproximation
