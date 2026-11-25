-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.projPerp_sqNorm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T14:25:48.415007+00:00
-- url     : https://prove2.me/submissions/8266ed43-3621-4d1b-8815-05350232dbab

import Mathlib
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_SkodaWeights_Matrix
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_star_dotProduct_self
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_projPerp_mulVec
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_star_dotProduct_projPerp_mulVec
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open Matrix Complex ComplexConjugate
namespace ReciprocityTheory.L2DbarEstimates
variable {p : ℕ}
private theorem sqNorm_projPerp_mulVec {g : Fin p → ℂ} (hg : g ≠ 0) (w : Fin p → ℂ) :
    sqNorm (projPerp g *ᵥ w) = sqNorm w - Complex.normSq (star g ⬝ᵥ w) / sqNorm g := by
  have key : ((sqNorm (projPerp g *ᵥ w) : ℝ) : ℂ) =
      ((sqNorm w : ℝ) : ℂ) - ((Complex.normSq (star g ⬝ᵥ w) : ℝ) : ℂ) / ((sqNorm g : ℝ) : ℂ) := by
    rw [← star_dotProduct_self (projPerp g *ᵥ w), ← star_dotProduct_self w]
    have hst : star (projPerp g *ᵥ w) =
        star w - star (((sqNorm g : ℝ) : ℂ)⁻¹ * (star g ⬝ᵥ w)) • star g := by
      rw [projPerp_mulVec, star_sub, star_smul]
    rw [hst, sub_dotProduct, smul_dotProduct, star_dotProduct_projPerp_mulVec hg, smul_zero,
      sub_zero, projPerp_mulVec, dotProduct_sub, dotProduct_smul, smul_eq_mul,
      Matrix.star_dotProduct w g, Complex.star_def, mul_assoc, Complex.mul_conj]
    ring
  exact_mod_cast key
end ReciprocityTheory.L2DbarEstimates
end

set_option autoImplicit false
open Matrix Complex ComplexConjugate
open ReciprocityTheory ReciprocityTheory.L2DbarEstimates
variable {p : ℕ}
namespace ReciprocityTheory.L2DbarEstimates
theorem _root_.solution : ProjPerpNormStatement := by
  intro p g w hg
  exact sqNorm_projPerp_mulVec hg w
end ReciprocityTheory.L2DbarEstimates
