-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.SA.eich_preserves
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T13:42:34.280193+00:00
-- url     : https://prove2.me/submissions/b4940db7-5430-4724-ab66-8baa8c7c678c

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_StrongApproximation_SAOpenStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_StrongApproximation_EichPreserves
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_SA_hf_symm
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_SA_eich_mulVec
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
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {R : Type*} [CommRing R] (σ : R →+* R)
  (J : Matrix ι ι R)
variable {σ J}
variable (hσ : ∀ x, σ (σ x) = x) (hJ : Jᵀ = J.map σ)
include hσ hJ
namespace ReciprocityTheory.ChartRestriction.G.SA
theorem _root_.solution {e u : ι → R} {c : R} (he : hf σ J e e = 0) (hue : hf σ J u e = 0)
    (hc : c + σ c + hf σ J u u = 0) (x y : ι → R) :
    hf σ J (eich σ J e u c *ᵥ x) (eich σ J e u c *ᵥ y) = hf σ J x y := by
  have heu : hf σ J e u = 0 := by rw [← hf_symm hσ hJ u e, hue, map_zero]
  have hv : ∀ z, eich σ J e u c *ᵥ z
      = z + hf σ J z e • u + (c * hf σ J z e - hf σ J z u) • e := by
    intro z
    rw [eich_mulVec, sub_smul]
    abel
  rw [hv, hv, hf_expand hσ hJ]
  simp only [he, hue, heu, mul_zero, add_zero, map_sub, map_mul]
  linear_combination (hf σ J x e * σ (hf σ J y e)) * hc
end ReciprocityTheory.ChartRestriction.G.SA
