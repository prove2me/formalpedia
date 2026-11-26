-- Prove2me | solution 1 for SharpIntermediateSubgroupBounds.oddGaussianConstant_lt_sharpConstant
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T06:04:24.434444+00:00
-- url     : https://prove2.me/submissions/49232929-12ea-4373-b149-6eddf2076d57

import Definitions.Def_SharpIntermediateSubgroupBounds_QBinomial
import Definitions.Def_SharpIntermediateSubgroupBounds_Theta
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Analysis.Normed.Group.Tannery
import Definitions.Def_SharpIntermediateSubgroupBounds_Gaussian
import Theorems.Thm_SharpIntermediateSubgroupBounds_eulerC_pos
import Theorems.Thm_SharpIntermediateSubgroupBounds_shiftedTheta_lt_of_not_integer


set_option autoImplicit true
open SharpIntermediateSubgroupBounds
open scoped BigOperators Topology
open Filter Finset Real
namespace SharpIntermediateSubgroupBounds
theorem _root_.solution {p : ℝ} (hp : 2 ≤ p) :
    oddGaussianConstant p < sharpConstant p := by
  have hhalf : ¬ ∃ z : ℤ, (z : ℝ) = (1 / 2 : ℝ) := by
    rintro ⟨z, hz⟩
    have hz' : (2 : ℝ) * (z : ℝ) = 1 := by rw [hz]; norm_num
    have hzInt : (2 : ℤ) * z = 1 := by exact_mod_cast hz'
    omega
  have htheta := shiftedTheta_lt_of_not_integer (p := p) (x := (1 / 2 : ℝ))
    (by linarith) hhalf
  simpa [oddGaussianConstant, sharpConstant] using
    mul_lt_mul_of_pos_left htheta (eulerC_pos hp)
end SharpIntermediateSubgroupBounds
