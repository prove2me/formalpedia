-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_ProjChowNonzero_toK_algebraMap_cb6f25d46c78
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T04:47:50.70505+00:00
-- url     : https://prove2.me/submissions/f49e509f-7f69-42fc-a185-30522cecab9c

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
    toK e (algebraMap ℂ (Loc e) a) = algebraMap ℂ (FractionRing (MvPolynomial (Fin (e + 1)) ℂ)) a := by
  rw [IsScalarTower.algebraMap_apply ℂ (MvPolynomial (Fin (e + 1)) ℂ) (Loc e), toK,
    IsLocalization.Away.lift_eq, ← IsScalarTower.algebraMap_apply]
end GroundTheory.Heights₂.Heights.ProjChowNonzero
