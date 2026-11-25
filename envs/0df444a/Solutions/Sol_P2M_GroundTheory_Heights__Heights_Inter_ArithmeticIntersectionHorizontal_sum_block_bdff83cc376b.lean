-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Inter_ArithmeticIntersectionHorizontal_sum_block_bdff83cc376b
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T04:13:24.462018+00:00
-- url     : https://prove2.me/submissions/f34a6425-d793-498a-8abd-1909e0133088

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_IsHorizontalSpanXb
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_IsHorizontalImageZ

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
open GroundTheory.Heights₂.Heights.Inter.ArithmeticIntersectionHorizontal
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
  {K' : Type} [Fintype K'] {ι' : K' → Type} [∀ k, Fintype (ι' k)]
omit [Fintype K] [∀ k, Fintype (ι k)]
open Classical
namespace GroundTheory.Heights₂.Heights.Inter.ArithmeticIntersectionHorizontal
theorem _root_.solution (F : (Σ k', ι' k') → ℕ) (k' : K') :
    ∑ i, F ⟨k', i⟩ = ∑ q, if q.1 = k' then F q else 0 := by
  classical
  rw [Fintype.sum_sigma, Finset.sum_eq_single k']
  · simp
  · intro b _ hb
    simp [hb]
  · simp
end GroundTheory.Heights₂.Heights.Inter.ArithmeticIntersectionHorizontal
