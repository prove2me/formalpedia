-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ArithBezout_linForm_ne_zero_922cf3447b3b
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T03:54:47.836299+00:00
-- url     : https://prove2.me/submissions/83ba3be5-c419-41a6-a09a-6695b7ec31fc

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
theorem _root_.solution : linForm (![1, 0] : Fin 2 → ℤ) ∉ (⊥ : Ideal (MRing (PBlk 2))) := by
  rw [Submodule.mem_bot]
  simp [linForm, Fin.sum_univ_two, Xc, X_ne_zero]
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ArithBezout
