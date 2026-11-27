-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_HeightsSet_FlagDegreeBound_hyps_inhabited_96aa0b1f8cc9
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-27T04:58:35.65864+00:00
-- url     : https://prove2.me/submissions/92bef770-1f35-4434-802e-92344e2945c2

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ArithmeticHilbertSamuelLowerBound
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterNamed
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithDegree
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightsOfSets_IsSaturatedFirstCoordinateLine
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_HeightsSet_isSaturated_firstCoordinateLine_9fe2fc0c34b2
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_HeightsSet_isSaturated_bot_76c7b2af8e06
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_HeightsSet_isSaturated_top_5352420a8723
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_HeightsSet_finrank_firstCoordinateLine_a321a353a3ad

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
namespace FlagDegreeBound
theorem _root_.solution :
    Monotone flagE ∧ (∀ i, IsSaturated (HermitianBundle.standard ℚ 2) (flagE i)) ∧
      ∀ i : Fin (2 + 1), Module.finrank (𝓞 ℚ) (flagE i) = (i : ℕ) := by
  refine ⟨Fin.monotone_iff_le_succ.mpr fun i ↦ ?_, fun i ↦ ?_, fun i ↦ ?_⟩
  · fin_cases i
    · exact bot_le
    · exact le_top
  · fin_cases i
    · exact isSaturated_bot
    · exact isSaturated_firstCoordinateLine
    · exact isSaturated_top
  · fin_cases i
    · change Module.finrank (𝓞 ℚ) (⊥ : Submodule (𝓞 ℚ) (Fin 2 → 𝓞 ℚ)) = 0
      exact finrank_bot _ _
    · exact finrank_firstCoordinateLine
    · change Module.finrank (𝓞 ℚ) (⊤ : Submodule (𝓞 ℚ) (Fin 2 → 𝓞 ℚ)) = 2
      rw [finrank_top, Module.finrank_fin_fun]
end FlagDegreeBound
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.HeightsSet
