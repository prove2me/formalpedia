-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.projDeg_scaleOff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-27T05:25:46.701839+00:00
-- url     : https://prove2.me/submissions/af6276b8-5d78-4243-b8e6-b445e5c89607

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_ProjDefs
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_ExistsNatMulMemConeRingIntFin
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_ArakelovGeometry_fnField_le_of_eq_ratMul
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_ArakelovGeometry_scaleOff_eq_ratMul
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_ArakelovGeometry_eq_ratMul_scaleOff
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_ArakelovGeometry_scaleOff_comp_self

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
open ReciprocityTheory.ChartRestriction.G.Geo Polynomial
variable {Ω : Type*} [Field Ω] [CharZero Ω] {κ : Type*} [Finite κ] {D : ℕ}
namespace ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
theorem _root_.solution (x : κ → Ω) (e : Fin (D + 1) → κ) (he : Function.Injective e) {m : ℕ}
    (hm : 0 < m) : projDeg (scaleOff e m x) e = projDeg x e := by

  have h1 : fnField (scaleOff e m x) = fnField x := le_antisymm
    (fnField_le_of_eq_ratMul x _ _ (fun i => scaleOff_eq_ratMul x e m i))
    (fnField_le_of_eq_ratMul _ x _ (fun i => eq_ratMul_scaleOff x e hm i))
  simp only [projDeg, scaleOff_comp_self, h1]
end ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
