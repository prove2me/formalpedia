-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ArithBezout_mem_conePts_bot_8cd7c8de083b
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T03:54:48.008318+00:00
-- url     : https://prove2.me/submissions/5d70d603-6eb9-4864-8d57-402c4b78c6a4

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
theorem _root_.solution {n : ℕ} (z : Fin n → ℂ) :
    z ∈ conePts (Int.castRingHom ℂ) (⊥ : Ideal (MvPolynomial (Fin n) ℤ)) ↔ z ≠ 0 := by
  simp [conePts]
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ArithBezout
