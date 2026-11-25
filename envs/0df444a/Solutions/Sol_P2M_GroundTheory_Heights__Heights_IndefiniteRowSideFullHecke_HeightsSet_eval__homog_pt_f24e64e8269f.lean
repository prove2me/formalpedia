-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_HeightsSet_eval__homog_pt_f24e64e8269f
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T03:56:38.686912+00:00
-- url     : https://prove2.me/submissions/39e80841-1039-4cc9-b08c-0f9ce02cf1cb

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ArithmeticHilbertSamuelLowerBound
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterNamed
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithDegree
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightsOfSets_IsSaturatedFirstCoordinateLine
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_HeightsSet_subsingleton_pt_2e0858fe9b58

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
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.HeightsSet
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4
open NumberField
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.HeightsSet
theorem _root_.solution {R : Type*} [CommRing R] (f : ℤ →+* R) (z : (Σ _ : Unit, PBlk 1 ()) → R)
    (g : MRing (PBlk 1)) (d : Unit → ℕ) (hg : IsMultiHomog g d) :
    eval₂ f z g = f (∑ m ∈ g.support, g.coeff m) * z ⟨(), 0⟩ ^ d () := by
  have := subsingleton_pt
  rw [eval₂_eq', map_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun m hm ↦ ?_
  rw [Fintype.prod_subsingleton _ ⟨(), 0⟩]
  have := hg m hm ()
  simp only [Fin.sum_univ_one] at this
  rw [this]
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.HeightsSet
