-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_ObjectsChow_DivCycleGeneric_algebraMap_linForm_2ec74aa66477
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T04:45:03.353565+00:00
-- url     : https://prove2.me/submissions/8454d123-43fa-48e5-ba23-29c5881c9f57

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_ImportsAlt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PObjectsDivCycleGeneric
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ObjectsChow_DivCycleGeneric_blkEquiv_apply_b5c60a5abd6f
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ObjectsChow_DivCycleGeneric_algebraMap_generic_8829ce0fabef

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
open GroundTheory.Heights₂.Heights.ObjectsChow.DivCycleGeneric
open MvPolynomial
variable {n : ℕ}
attribute [local instance] genericAlgebra
namespace GroundTheory.Heights₂.Heights.ObjectsChow.DivCycleGeneric
theorem _root_.solution (u : Fin n → ℤ) :
    algebraMap _ (MvPolynomial (Fin n) ℚ) (IndefiniteRowSideFullHecke.ArithBezout.linForm u) = linForm fun j => (u j : ℚ) := by
  simp [algebraMap_generic, toGeneric, IndefiniteRowSideFullHecke.ArithBezout.linForm, linForm, blkEquiv_apply,
    ReciprocityTheory.ChartRestriction.G.Geo.Xc]
end GroundTheory.Heights₂.Heights.ObjectsChow.DivCycleGeneric
