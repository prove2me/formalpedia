-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_ComplexSets_ConeScaling_hypotheses_inhabited_3ec3ee98400d
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T04:26:14.056951+00:00
-- url     : https://prove2.me/submissions/98e89a66-80e1-4437-990a-9464ea8c49f6

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_Statements
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ComplexSets_cone_isHomogeneous_dd28bfd9371f

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
namespace ConeScaling
theorem _root_.solution :
    coneIdeal.IsHomogeneous (homogeneousSubmodule (Fin 3) ℂ) ∧ (2 : ℂ) ≠ 0 :=
  ⟨cone_isHomogeneous, two_ne_zero⟩
end ConeScaling
end GroundTheory.Heights₂.Heights.ComplexSets
