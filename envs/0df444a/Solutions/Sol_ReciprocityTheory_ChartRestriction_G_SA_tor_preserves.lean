-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.SA.tor_preserves
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T13:27:59.695814+00:00
-- url     : https://prove2.me/submissions/866371ba-43cc-4ff9-9291-fe76f815a8e3

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_StrongApproximation_EichPreserves
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_StrongApproximation_EichAlongSub
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_SA_tor_mulVec
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_SA_hf_fe
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_SA_hf_expand


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
variable (hef : hf σ J e f = 1)
include hef
namespace ReciprocityTheory.ChartRestriction.G.SA
theorem _root_.solution {l m : R} (hlm : m * σ l = 1) (x y : ι → R) :
    hf σ J (tor σ J e f l m *ᵥ x) (tor σ J e f l m *ᵥ y) = hf σ J x y := by
  rw [tor_mulVec σ J e f l m x, tor_mulVec σ J e f l m y, hf_expand (hσ := hσ) (hJ := hJ), he, hff, hef,
    hf_fe hσ hJ he hff hef]
  have h2 : l * σ m = 1 := by
    have h3 := congrArg σ hlm
    rw [map_mul, hσ, map_one] at h3
    linear_combination h3
  simp only [map_mul, map_sub, map_one]
  linear_combination (σ (hf σ J y f) * hf σ J x e) * hlm + (σ (hf σ J y e) * hf σ J x f) * h2
end ReciprocityTheory.ChartRestriction.G.SA
