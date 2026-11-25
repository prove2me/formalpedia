-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_ComplexSets_linIdeal_isHomogeneous_08c43b14a20c
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T03:52:12.604669+00:00
-- url     : https://prove2.me/submissions/2cc4cf21-e2dd-459b-8f23-4ed0ce4d8b8a

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StConeAvoidsExists
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StLeadIdealDim
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StLinearFormCut
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StHomogDimZeroPow
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PConeAvoidsExists

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
variable {n : ℕ}
namespace GroundTheory.Heights₂.Heights.ComplexSets
theorem _root_.solution {d : ℕ} (A : Matrix (Fin d) (Fin n) ℂ) :
    (linIdeal A).IsHomogeneous (homogeneousSubmodule (Fin n) ℂ) :=
  Ideal.homogeneous_span _ _ (by
    rintro _ ⟨i, rfl⟩
    exact ⟨1, (mem_homogeneousSubmodule _ _).2
      (IsHomogeneous.sum _ _ _ (fun j _ => (isHomogeneous_X ℂ j).C_mul (A i j)))⟩)
end GroundTheory.Heights₂.Heights.ComplexSets
