-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.conj_projPerp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-27T05:31:53.45146+00:00
-- url     : https://prove2.me/submissions/b930a31e-c023-4c79-8a6e-f1525ee89d93

import Mathlib
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_SkodaWeights_Matrix
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_projPerp_apply

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Complex ComplexConjugate
open ReciprocityTheory ReciprocityTheory.L2DbarEstimates
variable {p : ℕ}
namespace ReciprocityTheory.L2DbarEstimates
theorem _root_.solution (g : Fin p → ℂ) (i l : Fin p) :
    conj (projPerp g i l) = projPerp g l i := by
  rw [projPerp_apply, projPerp_apply]
  simp only [map_sub, map_mul, map_inv₀, Complex.conj_ofReal, Complex.conj_conj,
    apply_ite (starRingEnd ℂ), map_one, map_zero]
  by_cases h : i = l
  · subst h
    simp only [if_pos rfl]
    ring
  · rw [if_neg h, if_neg (Ne.symm h)]
    ring
end ReciprocityTheory.L2DbarEstimates
