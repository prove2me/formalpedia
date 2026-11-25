-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_ChartKernel_pow_mul_aeval_eq_0699d72cc976
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T04:00:35.150372+00:00
-- url     : https://prove2.me/submissions/d2c99d8d-a40f-40de-97b9-8c64909e705b

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_ImportsBis
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_PChartKernel
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChartKernel_aeval_smul_of_isHomogeneous_28aad74d1df1

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MvPolynomial
noncomputable section
open GroundTheory.Heights₂.Heights.ChartKernel
variable {F : Type} [Field F] {n : ℕ}
namespace GroundTheory.Heights₂.Heights.ChartKernel
theorem _root_.solution {K : Type*} [Field K] [Algebra F K] (t : Fin n → F) (ξ : Fin n → K)
    (hτ : aeval ξ (linForm t) ≠ 0) (g : MvPolynomial (Fin n) F) :
    aeval ξ (linForm t) ^ g.totalDegree * aeval ((aeval ξ (linForm t))⁻¹ • ξ) g =
      aeval ξ (∑ d ∈ Finset.range (g.totalDegree + 1),
        linForm t ^ (g.totalDegree - d) * homogeneousComponent d g) := by
  conv_lhs => arg 2; rw [← sum_homogeneousComponent g]
  rw [map_sum, Finset.mul_sum, map_sum]
  refine Finset.sum_congr rfl fun d hd => ?_
  have hd' : d ≤ g.totalDegree := Nat.lt_succ_iff.mp (Finset.mem_range.mp hd)
  have key := aeval_smul_of_isHomogeneous (homogeneousComponent_isHomogeneous d g) (aeval ξ (linForm t))
    ((aeval ξ (linForm t))⁻¹ • ξ)
  rw [smul_smul, mul_inv_cancel₀ hτ, one_smul] at key
  rw [map_mul, map_pow, key, ← mul_assoc, ← pow_add, Nat.sub_add_cancel hd']
end GroundTheory.Heights₂.Heights.ChartKernel
