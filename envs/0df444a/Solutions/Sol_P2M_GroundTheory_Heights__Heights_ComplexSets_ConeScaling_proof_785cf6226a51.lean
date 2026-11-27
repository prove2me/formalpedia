-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_ComplexSets_ConeScaling_proof_785cf6226a51
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-27T04:54:08.923399+00:00
-- url     : https://prove2.me/submissions/6d46b8a2-56a7-4086-8771-597785552365

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PConeScaling
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ComplexSets_eval_smul_of_isHomogeneous_a2658f884797

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.ComplexSets
open MvPolynomial Pointwise
attribute [local instance] MvPolynomial.gradedAlgebra
namespace GroundTheory.Heights₂.Heights.ComplexSets
namespace ConeScaling
theorem _root_.solution : ConeScaling.Statement := by
  intro n J hJ t ht
  have key : ∀ s : ℂ, s • zeroSet J ⊆ zeroSet J := by
    rintro s _ ⟨x, hx, rfl⟩
    show ∀ q ∈ J, eval (s • x) q = 0
    intro q hq
    rw [← sum_homogeneousComponent q, map_sum]
    refine Finset.sum_eq_zero fun i _ => ?_
    rw [eval_smul_of_isHomogeneous (homogeneousComponent_isHomogeneous i q),
      hx _ (homogeneousComponent_mem_of_mem hJ hq i), mul_zero]
  refine (key t).antisymm fun x hx => ?_
  exact ⟨t⁻¹ • x, key _ (Set.smul_mem_smul_set hx), smul_inv_smul₀ ht x⟩
end ConeScaling
end GroundTheory.Heights₂.Heights.ComplexSets
