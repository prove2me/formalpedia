-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.Nab.rel_sy
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T14:00:31.104357+00:00
-- url     : https://prove2.me/submissions/0bb92236-fe66-4d95-a959-16956fce30a9

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_IntegralFamilyFirstZeroSecond
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_FirstDerivativeShiftIntegral
import Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_Nab_cc_ev__53681771e208
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_LogPf_CZ_cons
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_LogPf_CZ_nil
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_LogPf_CZ_pt
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_LogPf_cc_pt
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_LogPf_czY
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_LogPf_ev_X
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_LogPf_ev_ev
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_LogPf_ev_neg
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_LogPf_ev_sub
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_LogPf_formal_ev_second_point_of_x_zero
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_LogPf_pderiv_pt
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_LogPf_pt_apply
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_Nab_cc_sy
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_Nab_d2
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_Nab_ig_dlog
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_Nab_ig_ev
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_Nab_ig_fam_0z
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_Nab_zero_constant_zero_second


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
open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.TB.LogPf
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.TB ReciprocityTheory.ChartRestriction.G.TB.WickVanishing ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.Nab
variable {R : Type} [CommRing R] {d : ℕ} {O : Type} [CommRing O] [StarRing O]
variable {k : Type} [CommRing k] [Algebra ℚ k] [Algebra R k]
namespace ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.Nab
theorem _root_.solution {B : FB R d O} {h : PS k 2 d} (hc : B.IsCanonGauge k h) (b : Fin d) :
    ev (n := 2) ![pt k d 1] (sgOf k h b) + ev (n := 2) ![0, pt k d 1] (pderiv k ((0 : Fin 2), b) h) ∈
      Ig R k (Fin 2 × Fin d) := by
  have czSw : CZ (![pt k (n := 2) d 1, pt k d 0] : Fin 2 → Pt k 2 d) := CZ.cons (cc_pt 1) (CZ.cons (cc_pt 0) CZ.nil)
  have hH0 : constantCoeff (ev (n := 2) ![pt k d 1, pt k d 0] h - h) = 0 := by
    rw [map_sub, cc_ev' czSw, sub_self]
  have hH := ig_dlog B.sy (cc_sy B) _ hH0 hc.sy ((0 : Fin 2), b)
  have h2 := ig_ev zero_constant_zero_second ig_fam_0z hH
  have dd : pderiv k ((0 : Fin 2), b) (ev (n := 2) ![pt k d 1, pt k d 0] h) =
      ev (n := 2) ![pt k d 1, pt k d 0] (pderiv k ((1 : Fin 2), b) h) := by
    rw [d2 czSw]; simp [pderiv_pt]
  have es2 : ∀ g : PS k 2 d, ev (n := 2) ![0, pt k d 1] (ev (n := 2) ![pt k d 1, pt k d 0] g) =
      ev (n := 2) ![pt k d 1, 0] g := by
    intro g
    rw [ev_ev zero_constant_zero_second czSw]
    congr 1
    funext j c
    fin_cases j <;> simp [pt_apply, ev_X zero_constant_zero_second]
  rw [map_sub, ev_sub zero_constant_zero_second, dd, es2, ← formal_ev_second_point_of_x_zero] at h2
  have e : ev (n := 2) ![pt k d 1] (sgOf k h b) =
      -ev (n := 2) ![pt k d 1] (ev (n := 1) ![pt k d 0, 0] (pderiv k ((1 : Fin 2), b) h)) := by
    rw [← ev_neg czY]; rfl
  rw [e]
  have := neg_mem h2
  convert this using 1
  ring
end ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.Nab
