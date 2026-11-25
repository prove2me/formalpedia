-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Inter_PushforwardArithIntersection_proof_f5a8d74a2887
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T05:55:30.023516+00:00
-- url     : https://prove2.me/submissions/ee6ba95a-518e-414e-b7f5-1223f6daa1f4

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_IsFieldIntersectionNoBlockFam
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_IsMultiHomogRenameCoordPow
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_PushforwardArithIntersection_genDegAt_zero_e0e6f6c5241e
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_PushforwardArithIntersection_genDegAt_succ_b0303846c0e1

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
namespace GroundTheory.Heights₂.Heights.Inter
namespace PushforwardArithIntersection
theorem _root_.solution (h0 : ArithVarZeroStatement) (hRat : RatR.Statement) (hCyc : ArithmeticIntersectionCycle.Statement)
    (hInt : ArithmeticIntersectionIntegral.Statement) : PushforwardArithIntersection.Statement := by
  unfold PushforwardArithIntersection.Statement GenDegStatement
  intro I hI K _ ι _ K' _ ι' _ κ v P' d G J L L' hv hP' hP hJ hL hLL'
  have key : ∀ n, GenDegAt I n := fun n =>
    Nat.rec (PushforwardArithIntersection.genDegAt_zero h0 I) (fun n ih => PushforwardArithIntersection.genDegAt_succ hRat hCyc hInt I hI n ih) n
  exact key d K ι K' ι' κ v P' G J L L' hv hP' hP hJ hL hLL'
end PushforwardArithIntersection
end GroundTheory.Heights₂.Heights.Inter
