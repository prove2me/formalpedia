-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Inter_PushforwardArithIntersection_sum_single_eq_extend_60ee0a6ba5cd
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T04:14:56.160647+00:00
-- url     : https://prove2.me/submissions/472c3ea7-745e-4d1d-89d3-955a21b92489

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_IsFieldIntersectionNoBlockFam
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_IsMultiHomogRenameCoordPow

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
omit [Fintype K]
open Classical
namespace GroundTheory.Heights₂.Heights.Inter.PushforwardArithIntersection
theorem _root_.solution {K₀ : Type} [Fintype K₀] (κ : K₀ → K) (hκ : Function.Injective κ) (α : K₀ → ℕ) :
    (∑ k, α k • (Pi.single (κ k) 1 : K → ℕ)) = Function.extend κ α 0 := by
  funext k'
  rw [Finset.sum_apply]
  by_cases h : ∃ k, κ k = k'
  · obtain ⟨k, rfl⟩ := h
    rw [hκ.extend_apply, Finset.sum_eq_single k]
    · simp
    · intro b _ hb
      simp [hκ.ne hb]
    · simp
  · rw [Function.extend_apply' _ _ _ h]
    refine Finset.sum_eq_zero fun k _ => ?_
    have hk : k' ≠ κ k := fun e => h ⟨k, e.symm⟩
    simp [hk]
end GroundTheory.Heights₂.Heights.Inter.PushforwardArithIntersection
