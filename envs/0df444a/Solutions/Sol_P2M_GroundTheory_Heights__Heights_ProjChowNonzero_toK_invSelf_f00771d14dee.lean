-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_ProjChowNonzero_toK_invSelf_f00771d14dee
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T04:47:52.315795+00:00
-- url     : https://prove2.me/submissions/ddee97bd-0430-478c-af65-f73cf777d85c

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
    toK e (IsLocalization.Away.invSelf (X 0 : MvPolynomial (Fin (e + 1)) ℂ)) = (projVar e 0)⁻¹ := by
  have h := congrArg (toK e) (IsLocalization.Away.mul_invSelf (S := Loc e) (X 0 : MvPolynomial (Fin (e + 1)) ℂ))
  rw [map_mul, map_one, toK, IsLocalization.Away.lift_eq] at h
  exact (eq_inv_of_mul_eq_one_right h)
end GroundTheory.Heights₂.Heights.ProjChowNonzero
