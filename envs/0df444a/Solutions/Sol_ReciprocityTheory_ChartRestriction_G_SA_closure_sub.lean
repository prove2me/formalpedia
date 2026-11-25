-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.SA.closure_sub
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T14:05:41.392994+00:00
-- url     : https://prove2.me/submissions/672d2447-448a-465e-9dd2-dc722e39c11a

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_StrongApproximation_EichPreserves
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_StrongApproximation_EichAlongSub
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_SA_eichSet_sub
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_SA_mem_SU_iff


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.SA
open Matrix
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {R : Type*} [CommRing R] {σ : R →+* R}
  {J : Matrix ι ι R}
variable (hσ : ∀ x, σ (σ x) = x) (hJ : Jᵀ = J.map σ)
include hσ hJ
variable {e f : ι → R} (he : hf σ J e e = 0) (hff : hf σ J f f = 0)
include he hff
namespace ReciprocityTheory.ChartRestriction.G.SA
theorem _root_.solution : (Submonoid.closure (eichSet σ J e f) : Set (Matrix ι ι R)) ⊆ SU σ J := by
  intro M hM
  rw [SetLike.mem_coe] at hM
  induction hM using Submonoid.closure_induction with
  | mem x hx => exact eichSet_sub hσ hJ he hff hx
  | one =>
    rw [mem_SU_iff]
    exact ⟨Matrix.det_one, fun x y => by simp⟩
  | mul x y _ _ hx hy =>
    rw [mem_SU_iff] at hx hy ⊢
    refine ⟨by rw [Matrix.det_mul, hx.1, hy.1, one_mul], fun a b => ?_⟩
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hx.2, hy.2]
end ReciprocityTheory.ChartRestriction.G.SA
