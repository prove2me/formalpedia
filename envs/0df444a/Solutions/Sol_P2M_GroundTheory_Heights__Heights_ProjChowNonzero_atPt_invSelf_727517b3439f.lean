-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_ProjChowNonzero_atPt_invSelf_727517b3439f
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T04:47:48.088228+00:00
-- url     : https://prove2.me/submissions/242e491f-39b8-4f44-933a-67f6abad3fff

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsProjChowNonzero
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PIncidenceZeroLocus
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PProjChowNonzero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MvPolynomial
noncomputable section
open GroundTheory.Heights₂.Heights.ProjChowNonzero
namespace GroundTheory.Heights₂.Heights.ProjChowNonzero
theorem _root_.solution (e : ℕ) :
    atPt e (IsLocalization.Away.invSelf (X 0 : MvPolynomial (Fin (e + 1)) ℂ)) = 1 := by
  have h := congrArg (atPt e) (IsLocalization.Away.mul_invSelf (S := Loc e) (X 0 : MvPolynomial (Fin (e + 1)) ℂ))
  rw [map_mul, map_one] at h
  unfold atPt at h ⊢
  rw [IsLocalization.Away.lift_eq] at h
  simpa [pt] using h
end GroundTheory.Heights₂.Heights.ProjChowNonzero
