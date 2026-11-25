-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_ComplexSets_cone_isHomogeneous_dd28bfd9371f
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T03:51:08.226011+00:00
-- url     : https://prove2.me/submissions/c8632997-054a-40ae-b29e-2fb261286f0e

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_Statements

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
noncomputable section
variable {n d : ℕ}
attribute [local instance] MvPolynomial.gradedAlgebra
namespace GroundTheory.Heights₂.Heights.ComplexSets
theorem _root_.solution : coneIdeal.IsHomogeneous (homogeneousSubmodule (Fin 3) ℂ) := by
  apply Ideal.homogeneous_span
  intro x hx
  rw [Set.mem_singleton_iff] at hx
  subst hx
  refine ⟨2, (mem_homogeneousSubmodule 2 coneEq).mpr ?_⟩
  exact (isHomogeneous_X_pow (0 : Fin 3) 2).sub ((isHomogeneous_X ℂ (1 : Fin 3)).mul
    (isHomogeneous_X ℂ (2 : Fin 3)))
end GroundTheory.Heights₂.Heights.ComplexSets
