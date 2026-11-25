-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Inter_yyBlockMap_thm_f8e8aa12a09d
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T03:59:57.394296+00:00
-- url     : https://prove2.me/submissions/f736e4ac-bf31-4793-9c3c-3c7ed27aeff2

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_APrime
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StatementsAntisym
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_ProjLineRankTwoPushforwardHypotheses
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PAPrime

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Inter
open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4
namespace GroundTheory.Heights₂.Heights.Inter
theorem _root_.solution : YYBlockMapStatement := by
  intro ι ν κ j
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro a b h
    fin_cases j <;> cases a <;> cases b <;> simp_all [diagonalBlockIndex]
  · rintro ⟨a, x⟩ ⟨b, y⟩ h
    fin_cases j <;> cases a <;> cases b <;> simp [T.yyEmb] at h <;> injection h with h1 h2 <;>
      first | (cases h2; rfl) | cases h1
  · rintro ⟨a, x⟩
    fin_cases j <;> cases a <;> rfl
  · rintro ⟨b, y⟩ ⟨a, ha⟩
    fin_cases j <;> cases a <;> cases b <;>
      first
        | (refine ⟨⟨.base, y⟩, ?_⟩; simp [T.yyEmb]; done)
        | (refine ⟨⟨.det, y⟩, ?_⟩; simp [T.yyEmb]; done)
        | (refine ⟨⟨.line, y⟩, ?_⟩; simp [T.yyEmb]; done)
        | simp [diagonalBlockIndex] at ha
end GroundTheory.Heights₂.Heights.Inter
