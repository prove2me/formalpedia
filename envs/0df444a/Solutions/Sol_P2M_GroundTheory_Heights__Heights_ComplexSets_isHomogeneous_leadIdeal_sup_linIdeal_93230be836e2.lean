-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_ComplexSets_isHomogeneous_leadIdeal_sup_linIdeal_93230be836e2
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T03:51:49.643132+00:00
-- url     : https://prove2.me/submissions/8c598a59-3db3-4f3c-a63f-29fd5a34d43a

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StConeAvoidsOpen
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PConeAvoidsOpen

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
open MvPolynomial
noncomputable section
attribute [local instance] MvPolynomial.gradedAlgebra
variable {n d : ℕ}
namespace GroundTheory.Heights₂.Heights.ComplexSets
theorem _root_.solution (J : Ideal (MvPolynomial (Fin n) ℂ))
    (A : Matrix (Fin d) (Fin n) ℂ) :
    (leadIdeal J ⊔ linIdeal A).IsHomogeneous (homogeneousSubmodule (Fin n) ℂ) := by
  refine Ideal.IsHomogeneous.sup (Ideal.homogeneous_span _ _ ?_) (Ideal.homogeneous_span _ _ ?_)
  · rintro _ ⟨f, -, rfl⟩
    exact ⟨f.totalDegree, homogeneousComponent_mem _ _⟩
  · rintro _ ⟨i, rfl⟩
    exact ⟨1, (mem_homogeneousSubmodule _ _).2
      (IsHomogeneous.sum _ _ _ fun j _ => isHomogeneous_C_mul_X _ _)⟩
end GroundTheory.Heights₂.Heights.ComplexSets
