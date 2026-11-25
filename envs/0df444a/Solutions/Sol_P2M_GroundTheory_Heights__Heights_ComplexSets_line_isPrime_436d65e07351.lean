-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_ComplexSets_line_isPrime_436d65e07351
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T03:52:41.743914+00:00
-- url     : https://prove2.me/submissions/8fefa48d-14c4-4366-9f26-b315f6fcd923

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
namespace GroundTheory.Heights₂.Heights.ComplexSets
theorem _root_.solution : (⊥ : Ideal (MvPolynomial (Fin 1) ℂ)).IsPrime := Ideal.isPrime_bot
end GroundTheory.Heights₂.Heights.ComplexSets
