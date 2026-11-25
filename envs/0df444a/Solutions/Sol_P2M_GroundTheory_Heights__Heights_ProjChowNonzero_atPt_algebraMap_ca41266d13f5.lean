-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_ProjChowNonzero_atPt_algebraMap_ca41266d13f5
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T04:47:46.053557+00:00
-- url     : https://prove2.me/submissions/b84310c9-1d9a-4304-9c4a-3e820f6a5495

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
theorem _root_.solution (e : ℕ) (a : ℂ) :
    atPt e (algebraMap ℂ (Loc e) a) = algebraMap ℂ (AlgebraicClosure ℂ) a := by
  rw [IsScalarTower.algebraMap_apply ℂ (MvPolynomial (Fin (e + 1)) ℂ) (Loc e), atPt,
    IsLocalization.Away.lift_eq]
  simp
end GroundTheory.Heights₂.Heights.ProjChowNonzero
