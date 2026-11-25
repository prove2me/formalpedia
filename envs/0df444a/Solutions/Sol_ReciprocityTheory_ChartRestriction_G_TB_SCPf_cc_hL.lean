-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.TB.SCPf.cc_hL
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T00:55:30.991121+00:00
-- url     : https://prove2.me/submissions/512ff87d-2c10-4d82-9120-fa3a3068406c

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_LiftXEqRename
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_GaugeBilinearTermEqNegDoubleSum
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_SCMain
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_SCPf_nablaL_apply
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_coeff_ev_zero_left
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_gp_comp1
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_gp_pt
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_gt_const_ev_eq
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] ReciprocityTheory.ChartRestriction.G.TB.SCPf.nablaL_apply



set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.TB ReciprocityTheory.ChartRestriction.G.TB.SCPf
variable {R : Type} [CommRing R] {d : ℕ} {O : Type} [CommRing O] [StarRing O]
variable {k : Type} [CommRing k] [Algebra ℚ k] [Algebra R k]
namespace ReciprocityTheory.ChartRestriction.G.TB.SCPf
theorem _root_.solution (B : FB R d O) (h : PS k 2 d) (hc : B.IsCanonGauge k h) (w0 : O) :
    constantCoeff (B.hL k h w0) = 0 := by
  have h0 : constantCoeff h = 0 := by
    have e := WickVanishing.coeff_ev_zero_left h 0
    rw [hc.ax0, Finsupp.embDomain_zero] at e
    rw [← coeff_zero_eq_constantCoeff_apply, ← e, map_zero]
  unfold FB.hL
  rw [WickVanishing.gt_const_ev_eq _ ?_ h, h0]
  intro j
  fin_cases j
  · exact WickVanishing.gp_pt 0
  · exact WickVanishing.gp_comp1 _ _ (fun i => by simp [FB.actK, B.A.const]) (WickVanishing.gp_pt 0)
end ReciprocityTheory.ChartRestriction.G.TB.SCPf
