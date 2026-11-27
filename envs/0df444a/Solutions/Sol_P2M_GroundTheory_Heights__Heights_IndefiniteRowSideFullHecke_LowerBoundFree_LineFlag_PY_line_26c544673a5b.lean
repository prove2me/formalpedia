-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_LowerBoundFree_LineFlag_PY_line_26c544673a5b
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-27T05:08:48.037558+00:00
-- url     : https://prove2.me/submissions/03a826c2-f00a-4d82-a709-23edacedb80e

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HodgeLowerBound_PlueckerCoordinates_IsPlueckerCoord
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HodgeLowerBound_PlueckerCoordinates_FlagLine
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_LowerBoundFree_LineFlag_mem_flagPts_line_1444423326b9

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
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.LowerBoundFree GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.LowerBoundFree.LineFlag
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo GroundTheory.Heights₂.Heights.LowerBoundFree GroundTheory.Heights₂.Heights.LowerBoundFree.Line
open scoped Matrix
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.LowerBoundFree.LineFlag
theorem _root_.solution : PY PL = ⊥ := by
  rw [eq_bot_iff]
  intro f hf
  rw [Ideal.mem_bot]
  have hvan : ∀ u ∈ flagPts PL, eval u (map (Int.castRingHom ℂ) f) = 0 := by
    intro u hu
    have := (Submodule.mem_iInf _).1 ((Submodule.mem_iInf _).1 hf u) hu
    simpa using this
  have hzero : map (Int.castRingHom ℂ) f = 0 := by
    refine funext_set (fun _ => ({0}ᶜ : Set ℂ)) (fun _ => (Set.finite_singleton (0 : ℂ)).infinite_compl) ?_
    intro u hu
    rw [map_zero, hvan u (mem_flagPts_line u ⟨0, hu _ trivial⟩ ⟨0, hu _ trivial⟩ (hu _ trivial))]
  exact MvPolynomial.map_injective _ (Int.castRingHom ℂ).injective_int (by rw [hzero, map_zero])
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.LowerBoundFree.LineFlag
