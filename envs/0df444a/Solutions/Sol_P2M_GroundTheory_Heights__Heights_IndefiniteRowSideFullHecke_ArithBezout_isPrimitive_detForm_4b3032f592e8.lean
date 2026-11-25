-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ArithBezout_isPrimitive_detForm_4b3032f592e8
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T03:56:13.315419+00:00
-- url     : https://prove2.me/submissions/a28b3f88-a0ce-4efa-8fbb-840637501c5c

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
theorem _root_.solution : IsPrimitive (detForm ℤ) := by
  classical
  intro c hc
  have h := hc (Finsupp.single (0, 0) 1 + Finsupp.single (1, 1) 1)
  have hne : (Finsupp.single ((0 : Fin (1 + 1)), (1 : Fin 2)) 1 + Finsupp.single (1, 0) 1 :
      Fin (1 + 1) × Fin 2 →₀ ℕ) ≠ Finsupp.single (0, 0) 1 + Finsupp.single (1, 1) 1 := by
    intro h
    have h' := DFunLike.congr_fun h (0, 1)
    simp at h'
  have h1 : (detForm ℤ).coeff (Finsupp.single (0, 0) 1 + Finsupp.single (1, 1) 1) = 1 := by
    simp [detForm, X, monomial_mul, coeff_monomial, hne]
  rw [h1] at h
  exact isUnit_of_dvd_one h
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ArithBezout
