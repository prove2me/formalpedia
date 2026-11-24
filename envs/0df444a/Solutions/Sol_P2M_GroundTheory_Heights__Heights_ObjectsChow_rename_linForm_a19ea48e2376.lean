-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_ObjectsChow_rename_linForm_a19ea48e2376
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:00:42.411622+00:00
-- url     : https://prove2.me/submissions/390e792c-f15d-4e36-8ec4-03773d98768c

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_SpecFirstDetFormNeZero
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_IsMultiHomogOfIsChowForm

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
open GroundTheory.Heights₂.Heights.ObjectsChow
open MvPolynomial
open ReciprocityTheory.ChartRestriction.G.Geo (MRing PBlk Xc IsMultihomog)
variable {n : ℕ}
namespace GroundTheory.Heights₂.Heights.ObjectsChow
theorem _root_.solution (u : Fin n → ℤ) :
    rename (blk n) (linForm u) = IndefiniteRowSideFullHecke.ArithBezout.linForm u := by
  simp [linForm, IndefiniteRowSideFullHecke.ArithBezout.linForm, map_sum, blk, Xc]
end GroundTheory.Heights₂.Heights.ObjectsChow
