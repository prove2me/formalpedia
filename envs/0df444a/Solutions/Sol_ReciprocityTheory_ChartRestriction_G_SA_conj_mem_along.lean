-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.SA.conj_mem_along
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T14:06:42.540491+00:00
-- url     : https://prove2.me/submissions/59553d72-1763-43e0-953b-1b78cf001da6

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_StrongApproximation_UnitaryTransvectionZeroSecondMemClosure
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_StrongApproximation_ConjMemEichSet
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_SA_tor_conj_e
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_SA_hf_smul_left
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_SA_hf_smul_right


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
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {K : Type*} [CommRing K] {σ : K →+* K}
  {J : Matrix ι ι K}
variable (hσ : ∀ x, σ (σ x) = x) (hJ : Jᵀ = J.map σ)
include hσ hJ
namespace ReciprocityTheory.ChartRestriction.G.SA
theorem _root_.solution {e f : ι → K} (he : hf σ J e e = 0) (hff : hf σ J f f = 0)
    (hef : hf σ J e f = 1) {l m : K} (hml : m * σ l = 1) {M : Matrix ι ι K}
    (hM : M ∈ eichAlong σ J e f) :
    ∃ M' ∈ eichAlong σ J e f, tor σ J e f l m * M = M' * tor σ J e f l m := by
  obtain ⟨u, c, hue, huf, hc, rfl⟩ := hM
  refine ⟨_, ⟨σ l • u, l * σ l * c, ?_, ?_, ?_, rfl⟩, tor_conj_e hσ hJ he hff hef hml hue huf⟩
  · rw [hf_smul_left, hue, mul_zero]
  · rw [hf_smul_left, huf, mul_zero]
  · rw [hf_smul_left, hf_smul_right, map_mul, map_mul, hσ]
    linear_combination (l * σ l) * hc
end ReciprocityTheory.ChartRestriction.G.SA
