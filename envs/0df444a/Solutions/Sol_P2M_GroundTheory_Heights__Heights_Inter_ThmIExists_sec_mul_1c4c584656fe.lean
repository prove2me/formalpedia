-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Inter_ThmIExists_sec_mul_1c4c584656fe
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T13:46:25.984344+00:00
-- url     : https://prove2.me/submissions/5b2d51f8-f92f-4cdd-84a6-358810939066

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StatementsArith
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_IsMultiHomogXpow
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_ThmIExistsFamily
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_ArakelovGeometry_isMultiHomog_mul


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
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I2
noncomputable section
open GroundTheory.Heights₂.Heights.Inter.ThmIExists
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
namespace GroundTheory.Heights₂.Heights.Inter.ThmIExists
theorem _root_.solution {P : Ideal (MRing ι)} (hpr : P.IsPrime) {A B : HermLine ι} {s t : MRing ι}
    (hs : IsSectionOn P A s) (ht : IsSectionOn P B t) : IsSectionOn P (A.tensor B) (s * t) := by
  obtain ⟨a, ha, has, hsP⟩ := hs
  obtain ⟨b, hb, hbt, htP⟩ := ht
  refine ⟨a + b, fun k => ?_, ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.isMultiHomog_mul has hbt, fun h => ?_⟩
  · simp [HermLine.tensor, ha, hb]
  · rcases hpr.mem_or_mem h with h | h
    exacts [hsP h, htP h]
end GroundTheory.Heights₂.Heights.Inter.ThmIExists
