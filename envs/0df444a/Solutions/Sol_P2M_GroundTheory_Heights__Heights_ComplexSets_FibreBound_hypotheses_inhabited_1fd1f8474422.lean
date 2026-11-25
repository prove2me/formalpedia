-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_ComplexSets_FibreBound_hypotheses_inhabited_1fd1f8474422
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T06:29:31.454796+00:00
-- url     : https://prove2.me/submissions/d4f918ca-81bd-4d76-9938-cf8da2e8a965

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_Statements
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ComplexSets_cone_hyps_b9b793686593
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ComplexSets_line_hyps_79c8a84da216

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
namespace FibreBound
theorem _root_.solution :
    (coneIdeal.IsPrime ∧ ringKrullDim (MvPolynomial (Fin 3) ℂ ⧸ coneIdeal) = (2 : ℕ) ∧
      IsFiniteProjection coneIdeal coneProj) ∧
    ((⊥ : Ideal (MvPolynomial (Fin 1) ℂ)).IsPrime ∧
      ringKrullDim (MvPolynomial (Fin 1) ℂ ⧸ (⊥ : Ideal (MvPolynomial (Fin 1) ℂ))) = (1 : ℕ) ∧
      IsFiniteProjection (⊥ : Ideal (MvPolynomial (Fin 1) ℂ)) (1 : Matrix (Fin 1) (Fin 1) ℂ)) :=
  ⟨cone_hyps, line_hyps⟩
end FibreBound
end GroundTheory.Heights₂.Heights.ComplexSets
