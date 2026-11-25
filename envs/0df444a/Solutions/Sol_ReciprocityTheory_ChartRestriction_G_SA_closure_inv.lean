-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.SA.closure_inv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T14:03:07.813646+00:00
-- url     : https://prove2.me/submissions/c8b426ea-109d-442d-890e-0dfe928f6a6f

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_StrongApproximation_EichPreserves
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_StrongApproximation_EichAlongSub
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_SA_eichAlong_inv

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
theorem _root_.solution {M : Matrix ι ι R} (hM : M ∈ Submonoid.closure (eichSet σ J e f)) :
    ∃ M' ∈ Submonoid.closure (eichSet σ J e f), M' * M = 1 ∧ M * M' = 1 := by
  induction hM using Submonoid.closure_induction with
  | mem x hx =>
    rcases hx with hx | hx
    · obtain ⟨M', hM', h1, h2⟩ := eichAlong_inv hσ hJ he hx
      exact ⟨M', Submonoid.subset_closure (Or.inl hM'), h1, h2⟩
    · obtain ⟨M', hM', h1, h2⟩ := eichAlong_inv hσ hJ hff hx
      exact ⟨M', Submonoid.subset_closure (Or.inr hM'), h1, h2⟩
  | one => exact ⟨1, Submonoid.one_mem _, mul_one 1, mul_one 1⟩
  | mul x y _ _ hx hy =>
    obtain ⟨x', hx'm, hx1, hx2⟩ := hx
    obtain ⟨y', hy'm, hy1, hy2⟩ := hy
    refine ⟨y' * x', Submonoid.mul_mem _ hy'm hx'm, ?_, ?_⟩
    · rw [mul_assoc, ← mul_assoc x' x y, hx1, one_mul, hy1]
    · rw [mul_assoc, ← mul_assoc y y' x', hy2, one_mul, hx2]
end ReciprocityTheory.ChartRestriction.G.SA
