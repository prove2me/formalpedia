-- Prove2me | solution 1 for P2M_GlobalTheory_IntBall_DetLe_re_det_one_sub_le_of_unique__1c5d5c652355
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T04:09:53.207608+00:00
-- url     : https://prove2.me/submissions/62104010-fd9a-411a-adde-b0a3fe4136a3

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_NmatEqLowMat
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_PoincareCuspForms_ExhaustionFrames
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_IsOrth
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_DetOneSubOffDiagonalBlockGramLeOneBall
import Theorems.Thm_GlobalTheory_IntBall_DetLe_re_det_one_sub_le_of_unique

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates MeasureTheory GlobalTheory.IndefiniteRowSideFullHecke.ExhaustionFrames GlobalTheory.IntBall
open scoped ENNReal Matrix
open GlobalTheory GlobalTheory.IntBall GlobalTheory.IntBall.DetLe
namespace GlobalTheory.IntBall.DetLe
theorem _root_.solution {κ ι : Type} [Fintype κ] [Fintype ι] [DecidableEq ι]
    [DecidableEq κ] [Unique κ] (Z : Matrix κ ι ℂ) : ((1 - Zᴴ * Z).det).re ≤ 1 := by
  rw [Matrix.det_one_sub_mul_comm]
  have := re_det_one_sub_le_of_unique (Zᴴ)
  rwa [Matrix.conjTranspose_conjTranspose] at this
end GlobalTheory.IntBall.DetLe
