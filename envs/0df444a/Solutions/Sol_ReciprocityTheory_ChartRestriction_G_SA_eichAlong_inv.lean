-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.SA.eichAlong_inv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T13:55:42.268837+00:00
-- url     : https://prove2.me/submissions/8943c19a-5481-46b1-8ccf-b03cc67452c9

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_StrongApproximation_EichPreserves
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_StrongApproximation_EichAlongSub
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_SA_eich_inv
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_SA_hf_neg_left
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_SA_hf_neg_right


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
namespace ReciprocityTheory.ChartRestriction.G.SA
theorem _root_.solution {e f : ι → R} (he : hf σ J e e = 0) {M : Matrix ι ι R}
    (hM : M ∈ eichAlong σ J e f) : ∃ M' ∈ eichAlong σ J e f, M' * M = 1 ∧ M * M' = 1 := by
  obtain ⟨u, c, hue, huf, hc, rfl⟩ := hM
  have hue' : hf σ J (-u) e = 0 := by rw [hf_neg_left, hue, neg_zero]
  have huf' : hf σ J (-u) f = 0 := by rw [hf_neg_left, huf, neg_zero]
  have hc' : σ c + σ (σ c) + hf σ J (-u) (-u) = 0 := by
    rw [hσ, hf_neg_left, hf_neg_right, neg_neg]
    linear_combination hc
  refine ⟨eich σ J e (-u) (σ c), ⟨-u, σ c, hue', huf', hc', rfl⟩, eich_inv hσ hJ he hue hc, ?_⟩
  have h := eich_inv hσ hJ he hue' hc'
  rwa [neg_neg, hσ] at h
end ReciprocityTheory.ChartRestriction.G.SA
