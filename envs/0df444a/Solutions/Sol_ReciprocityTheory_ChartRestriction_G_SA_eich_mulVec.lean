-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.SA.eich_mulVec
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T13:34:28.540675+00:00
-- url     : https://prove2.me/submissions/a11d9401-f223-4208-9075-c6ddef1d57d3

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_StrongApproximation_SAOpenStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_StrongApproximation_EichPreserves
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_SA_hf_eq
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_SA_vmv_mulVec

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
variable (σ J)
namespace ReciprocityTheory.ChartRestriction.G.SA
theorem _root_.solution (e u : ι → R) (c : R) (x : ι → R) :
    eich σ J e u c *ᵥ x = x + hf σ J x e • u - hf σ J x u • e + (c * hf σ J x e) • e := by
  simp only [eich, Matrix.add_mulVec, Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec,
    vmv_mulVec, ← hf_eq, smul_smul]
end ReciprocityTheory.ChartRestriction.G.SA
