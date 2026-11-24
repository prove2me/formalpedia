-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ArithBezout_finIdeal_bot_609cd897da2d
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T03:54:47.113399+00:00
-- url     : https://prove2.me/submissions/ef7e07a7-f85d-4da1-b2f8-e1a49675877a

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_LatticePointLogCount
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_SpecFirstDetFormNeZero

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
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ArithBezout
open MvPolynomial MeasureTheory ReciprocityTheory.ChartRestriction.G.Geo Matrix
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ArithBezout
theorem _root_.solution (n : ℕ) : finIdeal (⊥ : Ideal (MRing (PBlk n))) = ⊥ := by
  refine Ideal.comap_bot_of_injective _ (rename_injective _ fun a b h => ?_)
  simpa using h
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ArithBezout
