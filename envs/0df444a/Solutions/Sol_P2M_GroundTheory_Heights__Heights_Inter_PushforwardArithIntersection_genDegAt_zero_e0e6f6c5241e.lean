-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Inter_PushforwardArithIntersection_genDegAt_zero_e0e6f6c5241e
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T04:14:29.506042+00:00
-- url     : https://prove2.me/submissions/c50e26d9-8283-4403-80e0-fff9839225ab

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_IsFieldIntersectionNoBlockFam
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_IsMultiHomogRenameCoordPow

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
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Inter
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4
open GroundTheory.Heights₂.Heights.Inter.PushforwardArithIntersection
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
  {K' : Type} [Fintype K'] {ι' : K' → Type} [∀ k, Fintype (ι' k)]
namespace GroundTheory.Heights₂.Heights.Inter.PushforwardArithIntersection
theorem _root_.solution (h0 : ArithVarZeroStatement) (I : AllFam) : GenDegAt I 0 := by
  intro K _ ι _ K' _ ι' _ κ v P' G J L L' _ hP'
  exact absurd hP' (h0 K' ι' P')
end GroundTheory.Heights₂.Heights.Inter.PushforwardArithIntersection
