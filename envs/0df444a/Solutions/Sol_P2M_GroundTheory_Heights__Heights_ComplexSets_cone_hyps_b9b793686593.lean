-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_ComplexSets_cone_hyps_b9b793686593
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T06:14:22.346988+00:00
-- url     : https://prove2.me/submissions/59b860c7-4977-47b5-96f5-b36d3af072ee

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_Statements
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ComplexSets_cone_isPrime_a6929b93aaa1
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ComplexSets_cone_dim_44deeb4b2e7b
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ComplexSets_cone_isFiniteProjection_a2859d45cc1d

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
namespace GroundTheory.Heights₂.Heights.ComplexSets
theorem _root_.solution : coneIdeal.IsPrime ∧ ringKrullDim (MvPolynomial (Fin 3) ℂ ⧸ coneIdeal) = (2 : ℕ) ∧
    IsFiniteProjection coneIdeal coneProj :=
  ⟨cone_isPrime, cone_dim, cone_isFiniteProjection⟩
end GroundTheory.Heights₂.Heights.ComplexSets
