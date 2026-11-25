-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ArithBezout_isMultihomog_detForm_ae74412cb508
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T03:56:12.217087+00:00
-- url     : https://prove2.me/submissions/6828ef59-aca4-44be-b5a3-e7a0fed036d8

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
theorem _root_.solution (R : Type*) [CommRing R] [Nontrivial R] :
    IsMultihomog (detForm R) 1 := by
  classical
  intro m hm k
  have hX : ∀ a b : Fin (1 + 1) × Fin 2, (X a * X b : MvPolynomial (Fin (1 + 1) × Fin 2) R) =
      monomial (Finsupp.single a 1 + Finsupp.single b 1) 1 := by
    intro a b
    simp [X, monomial_mul]
  rcases Finset.mem_union.mp (support_sub _ _ _ hm) with h | h <;>
  · rw [hX] at h
    have h' := support_monomial_subset h
    rw [Finset.mem_singleton] at h'
    subst h'
    fin_cases k <;> simp [Finsupp.single_apply]
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ArithBezout
