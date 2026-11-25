-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_HeightsSet_noCommonZero_one_32569d64e5bc
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T03:56:42.294972+00:00
-- url     : https://prove2.me/submissions/5d3784eb-9a08-4fca-a036-2b49ba632f49

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ArithmeticHilbertSamuelLowerBound
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterNamed
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithDegree
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightsOfSets_IsSaturatedFirstCoordinateLine

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
theorem _root_.solution :
    NoCommonZero (mCoordIdeal (ι := PBlk 1) yPt) yPt (fsLine 1).a ![(1 : ℚ)] := by
  intro z hz
  refine ⟨0, fun _ ↦ 1, fun _ ↦ 0, X ⟨(), 0⟩, 1, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro m hm k
    rw [support_X, Finset.mem_singleton] at hm
    subst hm
    simp
  · intro m hm k
    rw [support_one, Finset.mem_singleton] at hm
    subst hm
    simp
  · intro k
    simp [fsLine, HermLine.ofMetrics]
  · simp [yPt]
  · obtain ⟨i, hi⟩ := hz.1 ()
    simpa [Subsingleton.elim i 0] using hi
  · simp
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.HeightsSet
