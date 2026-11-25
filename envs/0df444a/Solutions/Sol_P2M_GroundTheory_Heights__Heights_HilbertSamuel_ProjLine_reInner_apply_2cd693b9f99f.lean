-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_HilbertSamuel_ProjLine_reInner_apply_2cd693b9f99f
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T03:55:42.403069+00:00
-- url     : https://prove2.me/submissions/fd8e966f-310d-406d-85ce-5eea4d85c0bd

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ArithmeticHilbertSamuelLowerBound
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_IsSmoothPts
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_ArithModel

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.HilbertSamuel
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
noncomputable section
set_option linter.unusedSectionVars false
open GroundTheory.Heights₂.Heights.HilbertSamuel.ProjLine
open scoped Topology
variable {J : Type} [Fintype J]
namespace GroundTheory.Heights₂.Heights.HilbertSamuel.ProjLine
theorem _root_.solution (y v : J → ℂ) : reInner y v = inner ℝ (eL y) (eL v) := rfl
end GroundTheory.Heights₂.Heights.HilbertSamuel.ProjLine
