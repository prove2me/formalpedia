-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_ComplexSets_line_hyps_79c8a84da216
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T05:13:05.71477+00:00
-- url     : https://prove2.me/submissions/cec1e429-4d31-42a4-b306-bec98af37ee9

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_Statements
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ComplexSets_line_isPrime_436d65e07351
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ComplexSets_line_dim_69b0ee92cc8e
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ComplexSets_line_isFiniteProjection_3268c8fd7565

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
theorem _root_.solution : (⊥ : Ideal (MvPolynomial (Fin 1) ℂ)).IsPrime ∧
    ringKrullDim (MvPolynomial (Fin 1) ℂ ⧸ (⊥ : Ideal (MvPolynomial (Fin 1) ℂ))) = (1 : ℕ) ∧
    IsFiniteProjection (⊥ : Ideal (MvPolynomial (Fin 1) ℂ)) (1 : Matrix (Fin 1) (Fin 1) ℂ) :=
  ⟨line_isPrime, line_dim, line_isFiniteProjection⟩
end GroundTheory.Heights₂.Heights.ComplexSets
