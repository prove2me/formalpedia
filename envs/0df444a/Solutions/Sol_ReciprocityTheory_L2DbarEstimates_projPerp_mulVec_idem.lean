-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.projPerp_mulVec_idem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T14:25:39.55062+00:00
-- url     : https://prove2.me/submissions/37bf5666-6de0-42a8-be6f-2629352f6695

import Mathlib
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_SkodaWeights_Matrix
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_projPerp_mulVec
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_star_dotProduct_projPerp_mulVec

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
    projPerp g *ᵥ (projPerp g *ᵥ w) = projPerp g *ᵥ w := by
  rw [projPerp_mulVec g (projPerp g *ᵥ w), star_dotProduct_projPerp_mulVec hg, mul_zero,
    zero_smul, sub_zero]
end ReciprocityTheory.L2DbarEstimates
