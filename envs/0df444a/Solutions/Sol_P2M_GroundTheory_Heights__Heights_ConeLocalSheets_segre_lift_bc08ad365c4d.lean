-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_ConeLocalSheets_segre_lift_bc08ad365c4d
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:05:36.685553+00:00
-- url     : https://prove2.me/submissions/3e1f2a50-6246-45d7-9dce-eafbe1ab8b6e

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsConeLocalSheets
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsQuasiFiniteSheets
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterFib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PConeLocalSheets

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MvPolynomial
open ReciprocityTheory.ChartRestriction.G.Geo (MRing PBlk IsArithVar IsGoodProj mcPts fibre segre)
open Matrix
open GroundTheory.Heights₂.Heights.ConeLocalSheets
variable {n e : ℕ}
namespace GroundTheory.Heights₂.Heights.ConeLocalSheets
theorem _root_.solution (z : Fin n → ℂ) : segre (lift z) = fun i => z (i ()) := by
  funext i
  simp [segre, lift]
end GroundTheory.Heights₂.Heights.ConeLocalSheets
