-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_ObjectsChow_linForm_mem_finIdeal_f754094b0af3
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:12:37.245097+00:00
-- url     : https://prove2.me/submissions/abd42299-4c64-4863-82f7-34ac45bda4b7

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_SpecFirstDetFormNeZero
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_IsMultiHomogOfIsChowForm
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ObjectsChow_rename_linForm_a19ea48e2376

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
theorem _root_.solution (P : Ideal (MRing (PBlk n))) (u : Fin n → ℤ) :
    linForm u ∈ IndefiniteRowSideFullHecke.ArithBezout.finIdeal P ↔ IndefiniteRowSideFullHecke.ArithBezout.linForm u ∈ P := by
  rw [IndefiniteRowSideFullHecke.ArithBezout.finIdeal, Ideal.mem_comap, ← rename_linForm]
  rfl
end GroundTheory.Heights₂.Heights.ObjectsChow
