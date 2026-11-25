-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_FinGradedSub_eq_of_piece_eq_7de61d87ab1c
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T03:29:35.339019+00:00
-- url     : https://prove2.me/submissions/86d96c7a-0cf1-4064-8b92-d887cb2ef4a2

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_Objects
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_StepTwoFiltGraded

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Kleiman
open MvPolynomial
noncomputable section
universe u v w
variable {S : Type u} [CommRing S] {Ω : Type w} [Field Ω] [Algebra S Ω] {N : ℕ}
variable {x : Fin (N + 1) → Ω} {E : Type v} [AddCommGroup E] [Module Ω E] [Module S E]
  [IsScalarTower S Ω E]
namespace GroundTheory.Heights₂.Heights.Kleiman
namespace FinGradedSub
theorem _root_.solution {A B : FinGradedSub (S := S) (x := x) E} (h : A.piece = B.piece) :
    A = B := by
  cases A
  cases B
  cases h
  rfl
end FinGradedSub
end GroundTheory.Heights₂.Heights.Kleiman
