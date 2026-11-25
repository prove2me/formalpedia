-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.SA.eich_inv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T13:42:07.655471+00:00
-- url     : https://prove2.me/submissions/2bffb495-15ec-4dcf-8a5a-57549f2ed08e

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_StrongApproximation_EichPreserves
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_StrongApproximation_EichAlongSub
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_SA_eich_mulVec
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_SA_hf_add_left
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_SA_hf_neg_right
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_SA_hf_smul_left
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_SA_hf_sub_left
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_SA_hf_symm


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
theorem _root_.solution {e u : ι → R} {c : R} (he : hf σ J e e = 0) (hue : hf σ J u e = 0)
    (hc : c + σ c + hf σ J u u = 0) : eich σ J e (-u) (σ c) * eich σ J e u c = 1 := by
  apply Matrix.ext_of_mulVec_single
  intro j
  rw [Matrix.one_mulVec, ← Matrix.mulVec_mulVec]
  have heu : hf σ J e u = 0 := by
    rw [← hf_symm (hσ := hσ) (hJ := hJ) (x := u) (y := e), hue, map_zero]
  rw [eich_mulVec (σ := σ) (J := J) e u c (Pi.single j 1)]
  set x : ι → R := Pi.single j 1
  set α := hf σ J x e
  set β := hf σ J x u
  set y := x + α • u - β • e + (c * α) • e with hy
  have h1 : hf σ J y e = α := by
    rw [hy, hf_add_left, hf_sub_left, hf_add_left, hf_smul_left, hf_smul_left, hf_smul_left, hue, he]
    ring
  have h2 : hf σ J y u = β + α * hf σ J u u := by
    rw [hy, hf_add_left, hf_sub_left, hf_add_left, hf_smul_left, hf_smul_left, hf_smul_left, heu]
    ring
  rw [eich_mulVec (σ := σ) (J := J) e (-u) (σ c) y, hf_neg_right, h1, h2]
  ext i
  simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, Pi.neg_apply, smul_eq_mul, hy]
  linear_combination (α * e i) * hc
end ReciprocityTheory.ChartRestriction.G.SA
