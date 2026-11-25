-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Inter_linSubst_linForm_d475c9bb2ba4
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T04:03:16.871717+00:00
-- url     : https://prove2.me/submissions/66c7ffb3-842d-4db0-91e1-b58c88d31eb5

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StProjBundleFibre
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_IsSmoothHermOfIsPullHermInl
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PProjBundleFibre
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Inter_sum_C_mul_linForm_340fe0b4ae9c

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
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4
variable {Φ : Type} [Field Φ] {σ : Type} [Fintype σ] {n : ℕ}
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter
theorem _root_.solution (ℓ : σ → Fin n → Φ) (μ : σ → Φ) :
    linSubst ℓ (∑ q, C (μ q) * X q) = ∑ b, C (∑ q, μ q * ℓ q b) * X b := by
  rw [← sum_C_mul_linForm μ ℓ]
  simp only [linSubst, map_sum, map_mul, aeval_C, aeval_X, MvPolynomial.algebraMap_eq]
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter
