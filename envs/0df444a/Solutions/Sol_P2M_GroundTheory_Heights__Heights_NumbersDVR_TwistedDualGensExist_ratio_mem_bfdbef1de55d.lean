-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_NumbersDVR_TwistedDualGensExist_ratio_mem_bfdbef1de55d
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T04:41:01.164266+00:00
-- url     : https://prove2.me/submissions/32b3bc47-e141-45b3-a36f-b1112009e813

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsTwistedDualGensExist
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PTwistedDualGensExist

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.NumbersDVR
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo
noncomputable section
variable {O : Type*} [CommRing O] {Ω : Type*} [Field Ω] [Algebra O Ω]
  {K : Type*} [Fintype K] [DecidableEq K] {ι : K → Type*}
namespace GroundTheory.Heights₂.Heights.NumbersDVR
namespace TwistedDualGensExist
theorem _root_.solution (y : (Σ k, ι k) → Ω) {c : ∀ k, ι k} (hc : segreVec y c ≠ 0)
    (k : K) (j : ι k) : y ⟨k, j⟩ / y ⟨k, c k⟩ ∈ chartRing O (segreVec y) c := by
  have hy : ∀ k', y ⟨k', c k'⟩ ≠ 0 := fun k' => (Finset.prod_ne_zero_iff.1 hc) k' (Finset.mem_univ _)
  have h := div_mem_chartRing (o := O) (segreVec y) c (Function.update c k j)
  have e1 : segreVec y (Function.update c k j) =
      y ⟨k, j⟩ * ∏ k' ∈ Finset.univ.erase k, y ⟨k', c k'⟩ := by
    rw [segreVec, ← Finset.mul_prod_erase _ _ (Finset.mem_univ k)]
    congr 1
    · simp
    · refine Finset.prod_congr rfl fun k' hk' => ?_
      rw [Function.update_of_ne (Finset.ne_of_mem_erase hk')]
  have e2 : segreVec y c = y ⟨k, c k⟩ * ∏ k' ∈ Finset.univ.erase k, y ⟨k', c k'⟩ := by
    rw [segreVec, ← Finset.mul_prod_erase _ _ (Finset.mem_univ k)]
  have hP : ∏ k' ∈ Finset.univ.erase k, y ⟨k', c k'⟩ ≠ 0 :=
    Finset.prod_ne_zero_iff.2 fun k' _ => hy k'
  rw [e1, e2, mul_div_mul_right _ _ hP] at h
  exact h
end TwistedDualGensExist
end GroundTheory.Heights₂.Heights.NumbersDVR
