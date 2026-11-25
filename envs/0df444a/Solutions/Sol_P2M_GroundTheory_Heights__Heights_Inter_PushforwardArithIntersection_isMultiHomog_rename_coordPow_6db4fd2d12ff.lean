-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Inter_PushforwardArithIntersection_isMultiHomog_rename_coordPow_6db4fd2d12ff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T04:53:58.576482+00:00
-- url     : https://prove2.me/submissions/d0f960fc-fbef-4d74-8375-2757a008f381

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_IsFieldIntersectionNoBlockFam
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_IsMultiHomogRenameCoordPow
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_PushforwardArithIntersection_isMultiHomog_of_wh_ff3f0ecada1f
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_PushforwardArithIntersection_sum_single_eq_extend_60ee0a6ba5cd
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_PushforwardArithIntersection_wh_prod_X_pow_7859ccdd4b43

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
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Inter
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4
open GroundTheory.Heights₂.Heights.Inter.PushforwardArithIntersection
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
  {K' : Type} [Fintype K'] {ι' : K' → Type} [∀ k, Fintype (ι' k)]
omit [∀ k, Fintype (ι k)]
namespace GroundTheory.Heights₂.Heights.Inter.PushforwardArithIntersection
theorem _root_.solution {κ : K → K'} {v : (Σ k, ι k) → (Σ k', ι' k')} (hv : IsBlockMap κ v)
    (i : ∀ k, ι k) (α : K → ℕ) :
    IsMultiHomog (rename v (∏ k, (X ⟨k, i k⟩ : MRing ι) ^ α k)) (Function.extend κ α 0) := by
  have h := wh_prod_X_pow (ι := ι') (fun k => v ⟨k, i k⟩) α
  have e : (∑ k, α k • blkW (ι := ι') (v ⟨k, i k⟩)) = Function.extend κ α 0 := by
    simp only [blkW, hv.2.2.1]
    exact sum_single_eq_extend κ hv.1 α
  rw [e] at h
  simp only [map_prod, map_pow, rename_X]
  exact isMultiHomog_of_wh h
end GroundTheory.Heights₂.Heights.Inter.PushforwardArithIntersection
