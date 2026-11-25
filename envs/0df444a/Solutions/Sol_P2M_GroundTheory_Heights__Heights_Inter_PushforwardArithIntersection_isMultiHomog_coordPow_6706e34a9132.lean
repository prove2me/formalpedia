-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Inter_PushforwardArithIntersection_isMultiHomog_coordPow_6706e34a9132
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T04:14:30.406694+00:00
-- url     : https://prove2.me/submissions/06811bb0-a606-47d3-aef8-fbc833fafb16

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_IsFieldIntersectionNoBlockFam
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_IsMultiHomogRenameCoordPow
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_PushforwardArithIntersection_isMultiHomog_of_wh_ff3f0ecada1f
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
namespace GroundTheory.Heights₂.Heights.Inter.PushforwardArithIntersection
theorem _root_.solution (i : ∀ k, ι k) (α : K → ℕ) :
    IsMultiHomog (∏ k, (X ⟨k, i k⟩ : MRing ι) ^ α k) α := by
  have h := wh_prod_X_pow (ι := ι) (fun k => ⟨k, i k⟩) α
  have e : (∑ k, α k • blkW (ι := ι) ⟨k, i k⟩) = α := by
    funext k
    simp only [blkW, Finset.sum_apply]
    rw [Finset.sum_eq_single k]
    · simp
    · intro b _ hb
      simp [Ne.symm hb]
    · simp
  rw [e] at h
  exact isMultiHomog_of_wh h
end GroundTheory.Heights₂.Heights.Inter.PushforwardArithIntersection
