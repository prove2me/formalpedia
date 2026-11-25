-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Inter_DiagonalFormDivisor_prod_wblk_dd968f239759
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T03:58:47.077897+00:00
-- url     : https://prove2.me/submissions/f320c2a6-71a1-4334-9cdb-d5e16457a11e

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StatementsDiagFormDiv
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StatementsChartFormsRational
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PMobiusAlgIndep
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PDiagFormDiv

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Inter
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI
noncomputable section
open GroundTheory.Heights₂.Heights.Inter.DiagonalFormDivisor
set_option linter.unusedSectionVars false
namespace GroundTheory.Heights₂.Heights.Inter.DiagonalFormDivisor
theorem _root_.solution {M : Type} [CommMonoid M] (g : T.WBlk → M) :
    ∏ k, g k = g .base * g .det * g .line0 * g .line1 := by
  rw [show (Finset.univ : Finset T.WBlk) = {.base, .det, .line0, .line1} from rfl]
  simp [Finset.prod_insert, mul_assoc]
end GroundTheory.Heights₂.Heights.Inter.DiagonalFormDivisor
