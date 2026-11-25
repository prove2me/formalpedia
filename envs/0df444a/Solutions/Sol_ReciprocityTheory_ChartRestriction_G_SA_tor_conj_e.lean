-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.SA.tor_conj_e
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T13:50:06.275021+00:00
-- url     : https://prove2.me/submissions/db97e891-8b89-4508-b364-38505e813b62

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_StrongApproximation_UnitaryTransvectionZeroSecondMemClosure
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_StrongApproximation_ConjMemEichSet
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_SA_eich_mulVec
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_SA_hf_add_left
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_SA_hf_fe
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_SA_hf_smul_left
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_SA_hf_smul_right
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_SA_hf_sub_left
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_SA_hf_symm
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_SA_tor_mulVec


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
theorem _root_.solution {e f : ι → K} (he : hf σ J e e = 0) (hff : hf σ J f f = 0) (hef : hf σ J e f = 1)
    {l m c : K} {u : ι → K} (hml : m * σ l = 1) (hue : hf σ J u e = 0) (huf : hf σ J u f = 0) :
    tor σ J e f l m * eich σ J e u c = eich σ J e (σ l • u) (l * σ l * c) * tor σ J e f l m := by
  have hfe := hf_fe hσ hJ he hff hef
  have heu : hf σ J e u = 0 := by rw [← hf_symm hσ hJ, hue, map_zero]
  have hfu : hf σ J f u = 0 := by rw [← hf_symm hσ hJ, huf, map_zero]
  rw [ext_iff_mulVec]
  intro x
  rw [← mulVec_mulVec, ← mulVec_mulVec, eich_mulVec, tor_mulVec, tor_mulVec, eich_mulVec]
  simp only [hf_add_left, hf_sub_left, hf_smul_left, hf_smul_right, hσ, he, hff, hef, hfe, hue, huf,
    heu, hfu, mul_zero, mul_one, add_zero, sub_zero, zero_add]
  ext i
  simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  linear_combination (-(hf σ J x e * u i) - l * c * hf σ J x e * e i) * hml
end ReciprocityTheory.ChartRestriction.G.SA
