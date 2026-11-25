-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_NumbersDVR_FlagPairJoinRight_lat_le_mid_be997bb743ad
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T08:59:35.14135+00:00
-- url     : https://prove2.me/submissions/5b937890-0704-493f-bdea-5068c36af97c

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_ImportsBisTail
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_ImportsMoreAlt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PTwinFlagPairJoinRight
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_FlagPairJoinRight_mseg_mid_c88feac68b08
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_FlagPairJoinRight_chartRing_le_mid_5cedf1c698e4
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
variable (O : Type*) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {Ω : Type*} [Field Ω] [Algebra O Ω]
variable {K K' K₂ : Type} [Fintype K] [Fintype K'] [Fintype K₂] {ι : K → Type} {ι' : K' → Type}
  {ι₂ : K₂ → Type} [∀ k, Fintype (ι k)] [∀ k, Fintype (ι' k)] [∀ k, Fintype (ι₂ k)]
variable {N : ℕ} {V : Type*} [AddCommGroup V] [Module Ω V]
namespace GroundTheory.Heights₂.Heights.NumbersDVR.FlagPairJoinRight
theorem _root_.solution (x : (Σ k, ι k) → Ω) (z : (Σ k, ι' k) → Ω) (w : (Σ k, ι₂ k) → Ω)
    {E : ChartBundle O (mseg x) N V} {EF : ChartBundle O (mseg (joinCoord x z)) N V}
    {EB : ChartBundle O (mseg (joinCoord x (joinCoord w z))) N V} (hF : IsPull O x z E EF)
    (hB : IsPull O x (joinCoord w z) E EB) (s : ∀ k : K ⊕ (K₂ ⊕ K'), Sum.elim ι (Sum.elim ι₂ ι') k)
    (hs : mseg (joinCoord x (joinCoord w z)) s ≠ 0) :
    EF.lat (midChart s) ≤ EB.lat s := by
  have hsF : mseg (joinCoord x z) (midChart s) ≠ 0 := by
    rw [mseg_mid] at hs
    exact left_ne_zero_of_mul hs
  rw [hF _ hsF, hB s hs]
  apply AddSubgroup.closure_mono
  rintro _ ⟨a, ha, e, he, rfl⟩
  exact ⟨a, chartRing_le_mid O x z w s hs ha, e, he, rfl⟩
end GroundTheory.Heights₂.Heights.NumbersDVR.FlagPairJoinRight
