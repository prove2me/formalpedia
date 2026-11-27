-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Targets_FibreCurve_isMultiHomogIdeal_3254568b8d6d
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-27T05:10:42.403379+00:00
-- url     : https://prove2.me/submissions/5feefa59-2610-46ba-bb0c-77bf457de56a

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_QuotientMapImageZInjective
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PCoordConeArithVar
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_ArithModel
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_FibreCurve
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_CoordinateConeArithVar_isMultiHomogIdeal_e52032a6c383


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
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Targets GroundTheory.Heights₂.Heights.Targets.FibreCurve
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4
variable {Ω : Type} [Field Ω]
namespace GroundTheory.Heights₂.Heights.Targets.FibreCurve
theorem _root_.solution (u : Ω) : IsMultiHomogIdeal (mCoordIdeal (pt u)) :=
  CoordinateConeArithVar.isMultiHomogIdeal _
end GroundTheory.Heights₂.Heights.Targets.FibreCurve
