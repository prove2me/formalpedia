-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.Nab.cf_bracket
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T14:01:10.874189+00:00
-- url     : https://prove2.me/submissions/99db7b5d-f4e8-43c3-9422-5aeaa61773f0

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_DofComm
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_ConnectionSecondOfCommute
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_Nab_Dof_X
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_Nab_cf_inl
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_Nab_cf_inr
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_Nab_vf_C
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_Nab_vf_add
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_Nab_vf_cf_liftX


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.TB ReciprocityTheory.ChartRestriction.G.TB.WickVanishing ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.Nab
variable {R : Type} [CommRing R] {d : ℕ} {O : Type} [CommRing O] [StarRing O]
variable (k : Type) [CommRing k] [Algebra ℚ k] [Algebra R k]
namespace ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.Nab
theorem _root_.solution (hC : GE.DofCommSt) (B : FB R d O) (h : PS k 2 d) (u φ u' φ' : Fin d → k)
    (t : Fin d ⊕ Fin d) : vf (cf k B h u φ) (cf k B h u' φ' t) - vf (cf k B h u' φ') (cf k B h u φ t) = 0 := by
  cases t with
  | inl j =>
    rw [cf_inl, cf_inl, ← Dof_X, ← Dof_X, vf_cf_liftX, vf_cf_liftX, hC R d O k B u u', sub_self]
  | inr i =>
    rw [cf_inr, cf_inr, vf_add, vf_add, vf_C, vf_C, add_zero, add_zero, vf_cf_liftX, vf_cf_liftX,
      hC R d O k B u u', sub_self]
end ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.Nab
