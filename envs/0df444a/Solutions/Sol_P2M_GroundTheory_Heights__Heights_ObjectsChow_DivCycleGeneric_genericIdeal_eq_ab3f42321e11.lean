-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_ObjectsChow_DivCycleGeneric_genericIdeal_eq_ab3f42321e11
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T04:45:07.064166+00:00
-- url     : https://prove2.me/submissions/8053cbbc-bc49-42a2-8b6d-45326d6ebd5d

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_ImportsAlt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PObjectsDivCycleGeneric
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
theorem _root_.solution (W : Ideal (ReciprocityTheory.ChartRestriction.G.Geo.MRing (ReciprocityTheory.ChartRestriction.G.Geo.PBlk n))) :
    genericIdeal W = W.map (algebraMap _ (MvPolynomial (Fin n) ℚ)) := by
  have h : IndefiniteRowSideFullHecke.ArithBezout.finIdeal W = W.map (renameEquiv ℤ (blkEquiv n)).toRingEquiv := by
    rw [IndefiniteRowSideFullHecke.ArithBezout.finIdeal, ← Ideal.comap_symm]
    rfl
  rw [genericIdeal, h]
  show Ideal.map _ (Ideal.map (rename (R := ℤ) (blkEquiv n)).toRingHom W) = _
  rw [Ideal.map_map, algebraMap_generic]
  rfl
end GroundTheory.Heights₂.Heights.ObjectsChow.DivCycleGeneric
