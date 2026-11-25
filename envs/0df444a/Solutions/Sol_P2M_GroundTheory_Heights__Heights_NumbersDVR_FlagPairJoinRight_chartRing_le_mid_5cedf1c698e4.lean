-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_NumbersDVR_FlagPairJoinRight_chartRing_le_mid_5cedf1c698e4
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T08:48:02.207043+00:00
-- url     : https://prove2.me/submissions/8467c271-808d-40d4-9086-499e47b0b122

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_ImportsBisTail
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_ImportsMoreAlt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PTwinFlagPairJoinRight
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_FlagPairJoinRight_midChart_extChart_037092772d6a
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_FlagPairJoinRight_wChart_extChart_34eac10a37d9
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_FlagPairJoinRight_mseg_mid_c88feac68b08
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_NumbersDVR_Bundles_joinCoord_midVar_3ed08dc9bce4


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
set_option linter.unusedSectionVars false
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.NumbersDVR
open MvPolynomial
open ReciprocityTheory.ChartRestriction.G.Geo (ChartBundle chartRing div_mem_chartRing)
open IndefiniteRowSideFullHecke.NumbersDVR.Bundles (mseg joinCoord restrictChart chartMon IsGradedFrame IsUnitOn FlagPair IsPull
  midDeg midVar joinCoord_midVar)
open GroundTheory.Heights₂.Heights.NumbersDVR.FlagPairJoinRight
variable {Ω : Type*} [Field Ω] {K K' K₂ : Type} [Fintype K] [Fintype K'] [Fintype K₂]
  {ι : K → Type} {ι' : K' → Type} {ι₂ : K₂ → Type}
variable (O : Type*) [CommRing O] [Algebra O Ω]
namespace GroundTheory.Heights₂.Heights.NumbersDVR.FlagPairJoinRight
theorem _root_.solution (x : (Σ k, ι k) → Ω) (z : (Σ k, ι' k) → Ω) (w : (Σ k, ι₂ k) → Ω)
    (s : ∀ k : K ⊕ (K₂ ⊕ K'), Sum.elim ι (Sum.elim ι₂ ι') k)
    (hs : mseg (joinCoord x (joinCoord w z)) s ≠ 0) :
    chartRing O (mseg (joinCoord x z)) (midChart s) ≤ chartRing O (mseg (joinCoord x (joinCoord w z))) s := by
  have hw : mseg w (wChart s) ≠ 0 := by
    rw [mseg_mid] at hs
    exact right_ne_zero_of_mul hs
  unfold chartRing
  apply Algebra.adjoin_le
  rintro _ ⟨t', rfl⟩
  have h : mseg (joinCoord x z) t' / mseg (joinCoord x z) (midChart s) =
      mseg (joinCoord x (joinCoord w z)) (extChart t' (wChart s)) /
        mseg (joinCoord x (joinCoord w z)) s := by
    rw [mseg_mid x z w (extChart t' (wChart s)), mseg_mid x z w s, midChart_extChart, wChart_extChart,
      mul_div_mul_right _ _ hw]
  simp only
  rw [h]
  exact div_mem_chartRing (o := O) _ _ _
end GroundTheory.Heights₂.Heights.NumbersDVR.FlagPairJoinRight
