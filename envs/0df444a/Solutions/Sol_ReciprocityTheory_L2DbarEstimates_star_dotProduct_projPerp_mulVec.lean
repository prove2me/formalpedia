-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.star_dotProduct_projPerp_mulVec
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:33:07.990863+00:00
-- url     : https://prove2.me/submissions/1b56022d-de0d-4b5f-8a00-238e852d3f59

import Mathlib
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_SkodaWeights_Matrix
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_sqNorm_pos
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_star_dotProduct_self
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_projPerp_mulVec

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
theorem _root_.solution {g : Fin p → ℂ} (hg : g ≠ 0) (w : Fin p → ℂ) :
    star g ⬝ᵥ (projPerp g *ᵥ w) = 0 := by
  have hs : ((sqNorm g : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (sqNorm_pos hg).ne'
  rw [projPerp_mulVec, dotProduct_sub, dotProduct_smul, star_dotProduct_self, smul_eq_mul]
  field_simp
  ring
end ReciprocityTheory.L2DbarEstimates
