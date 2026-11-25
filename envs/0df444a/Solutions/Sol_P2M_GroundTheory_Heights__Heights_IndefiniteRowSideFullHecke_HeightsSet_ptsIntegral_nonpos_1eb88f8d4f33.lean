-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_HeightsSet_ptsIntegral_nonpos_1eb88f8d4f33
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T08:25:33.450363+00:00
-- url     : https://prove2.me/submissions/31f192dc-af4e-491d-9d67-d9866eaaccc4

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightsOfSets_MemMCoordIdealIffOfIsWeightedHomogeneous
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightsOfSets_Imports
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightsOfSets_IsSmoothHermConstLine
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_HeightsSet_maDensity_fin_zero_86460df5dcd1
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_HeightsSet_finsum_nonpos__f0098eb00e49

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
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.HeightsSet
open MvPolynomial MeasureTheory ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.HeightsSet
theorem _root_.solution (P : Ideal (MRing ι)) (φ : Fin 0 → ((Σ k, ι k) → ℂ) → ℝ)
    {g : ((Σ k, ι k) → ℂ) → ℝ} (hg : ∀ z ∈ mcPts P, g z ≤ 0) : ptsIntegral P φ g ≤ 0 := by
  unfold ptsIntegral ptsIntegralAt
  split_ifs with hΨ
  · refine integral_nonpos fun y ↦ finsum_nonpos' fun w ↦ finsum_nonpos' fun _ ↦ ?_
    unfold sheetDensity
    split_ifs with hγ
    · rw [maDensity_fin_zero, mul_one]
      exact hg _ hγ.choose_spec.2.self_of_nhds.2.1
    · exact le_rfl
  · exact le_rfl
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.HeightsSet
