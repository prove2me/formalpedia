-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ArithBezout_squarefree_detForm_5f14a536d456
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T04:30:43.770733+00:00
-- url     : https://prove2.me/submissions/82b2eb6f-38b3-4ac7-815d-42061016d52d

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_LatticePointLogCount
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_SpecFirstDetFormNeZero
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ArithBezout_detForm_ne_zero_b96a0e200ace
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ArithBezout_degreeOf_detForm_le_28d9852374cf

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
theorem _root_.solution : Squarefree (detForm ℂ) := by
  rintro a ⟨b, hb⟩
  have ha : a ≠ 0 := by
    rintro rfl
    exact detForm_ne_zero (by simpa using hb)
  have hb0 : b ≠ 0 := by
    rintro rfl
    exact detForm_ne_zero (by simpa using hb)
  have hdeg : ∀ x, degreeOf x a = 0 := by
    intro x
    have h1 := degreeOf_detForm_le x
    rw [hb, degreeOf_mul_eq (mul_ne_zero ha ha) hb0, degreeOf_mul_eq ha ha] at h1
    omega
  have hC : a = C (a.coeff 0) := by
    ext m
    rw [coeff_C]
    split_ifs with hm
    · rw [← hm]
    · by_contra hne
      apply hm
      ext x
      have h2 := monomial_le_degreeOf x (mem_support_iff.mpr hne)
      rw [hdeg x] at h2
      simp only [Finsupp.coe_zero, Pi.zero_apply]
      omega
  have hc : a.coeff 0 ≠ 0 := fun h0 => ha (by rw [hC, h0, map_zero])
  rw [hC]
  exact (isUnit_iff_ne_zero.mpr hc).map C
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ArithBezout
