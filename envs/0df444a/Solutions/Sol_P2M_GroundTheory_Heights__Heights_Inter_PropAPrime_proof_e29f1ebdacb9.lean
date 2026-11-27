-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Inter_PropAPrime_proof_e29f1ebdacb9
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-27T05:08:16.538122+00:00
-- url     : https://prove2.me/submissions/c057fd0a-a052-4cc1-b53a-943204673fb7

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_APrime
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StatementsAntisym
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_ProjLineRankTwoPushforwardHypotheses
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PAPrime
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_yyBlockMap_thm_f8e8aa12a09d
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Inter_isPullHerm_pullHerm_924295e2684a
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AI_aPrime_thm


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
namespace PropAPrime
theorem _root_.solution (h₁ : ToFibreSquare.Statement) (h₂ : FibreInt.Statement) : PropAPrime.Statement := by
  intro I hI D S X A hX hAs hAb k hk hkD
  have hb := yyBlockMap_thm S.ι S.ν S.κ
  have p0 := IndefiniteRowSideFullHecke.Inter.isPullHerm_pullHerm (hb 0) X
  have p1 := IndefiniteRowSideFullHecke.Inter.isPullHerm_pullHerm (hb 1) X
  have pA := IndefiniteRowSideFullHecke.Inter.isPullHerm_pullHerm (hb 0) A
  obtain ⟨F, hFI, hFΦ⟩ := h₁ I hI D S X A _ _ _ hX hAs hAb p0 p1 pA
  have hfib := h₂ D S X A _ _ _ hX hAs hAb p0 p1 pA k hk hkD
  have hF := aPrime_thm D F k hk hkD
  rw [hFI (2 * k) (by omega),
    Finset.sum_congr rfl (fun i hi => hFΦ k i hk hkD (Finset.mem_range.1 hi)), ← Finset.mul_sum, hfib,
    ← mul_neg] at hF
  exact mul_left_cancel₀ (by positivity) hF
end PropAPrime
end GroundTheory.Heights₂.Heights.Inter
