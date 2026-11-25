-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Inter_ptsIntegral_comp_perm_91c7c4e989fe
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T05:19:45.634597+00:00
-- url     : https://prove2.me/submissions/f7f04d6f-ae41-420a-b72d-87e9d39d2d2f

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StatementsSwap
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterDivSupp
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_NotLtLtOfMemMinimalPrimes
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_maDensity_comp_perm_7216a3acf8bf

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
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo
noncomputable section
variable {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)]
omit [∀ k, Fintype (ι k)]
namespace GroundTheory.Heights₂.Heights.Inter
theorem _root_.solution (P : Ideal (MRing ι)) {e : ℕ} (φ : Fin e → ((Σ k, ι k) → ℂ) → ℝ)
    (σ : Equiv.Perm (Fin e)) (g : ((Σ k, ι k) → ℂ) → ℝ) :
    ptsIntegral P (φ ∘ σ) g = ptsIntegral P φ g := by
  unfold ptsIntegral
  split_ifs with h
  · unfold ptsIntegralAt
    congr 1
    funext y
    refine finsum_congr fun w => finsum_congr fun _ => ?_
    unfold sheetDensity
    split_ifs with hγ
    · congr 1
      exact maDensity_comp_perm (fun j y' => φ j (hγ.choose y')) σ y
    · rfl
  · rfl
end GroundTheory.Heights₂.Heights.Inter
