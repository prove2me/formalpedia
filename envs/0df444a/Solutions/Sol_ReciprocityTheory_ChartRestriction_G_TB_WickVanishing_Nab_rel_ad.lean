-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.Nab.rel_ad
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T14:12:25.372041+00:00
-- url     : https://prove2.me/submissions/8fd7a3ed-de3e-42a4-9e89-750009d900d7

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_IntegralFamilyFirstZeroSecond
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_FirstDerivativeShiftIntegral
import Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_Nab_const_actK__1950e9d409b9
import Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_G_TB_LogPf_ev_zero__a29edcfaf6d8
import Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_Nab_cc_ev__53681771e208
import Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_Nab_cc_pderiv__e7c46f068b17
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_LogPf_CZ_cons
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_LogPf_CZ_nil
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_LogPf_CZ_pt
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_LogPf_cc_pt
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_LogPf_cz1
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_LogPf_czY
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_LogPf_ev_X
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_LogPf_ev_ev
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_LogPf_ev_mul
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_LogPf_ev_neg
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_LogPf_ev_sub
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_LogPf_ev_sum
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_LogPf_pderiv_ev_zero
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_LogPf_pderiv_pt
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_LogPf_pt_apply
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_Nab_cc_ad
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_Nab_d2
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_Nab_d_y
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_Nab_ez_y
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_Nab_ig_dlog
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_Nab_ig_ev
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_Nab_integral_family_point_zero
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_Nab_zero_constant_first_point
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_gt_ev_pt_self


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
theorem _root_.solution {B : FB R d O} {h : PS k 2 d} (hc : B.IsCanonGauge k h) (a : O) (b : Fin d) :
    ∑ c, sgOf k h c * C (dAct k B (star a) c b) - ev (n := 1) ![B.actK k a] (sgOf k h b) ∈
      Ig R k (Fin 1 × Fin d) := by
  have cA0 : CZ (![comp1 (B.actK k a) (pt k (n := 2) d 0), pt k d 1] : Fin 2 → Pt k 2 d) :=
    CZ.cons (fun l => constantCoeff_ev zero_constant_first_point (const_actK' B a l)) (CZ.cons (cc_pt 1) CZ.nil)
  have cA1 : CZ (![pt k (n := 2) d 0, comp1 (B.actK k (star a)) (pt k (n := 2) d 1)] : Fin 2 → Pt k 2 d) :=
    CZ.cons (cc_pt 0) (CZ.cons (fun l => constantCoeff_ev czY (const_actK' B (star a) l)) CZ.nil)
  have cAk : CZ (![B.actK k a] : Fin 1 → Pt k 1 d) := CZ.cons (const_actK' B a) CZ.nil
  have hH0 : constantCoeff (ev (n := 2) ![comp1 (B.actK k a) (pt k d 0), pt k d 1] h -
      ev (n := 2) ![pt k d 0, comp1 (B.actK k (star a)) (pt k d 1)] h) = 0 := by
    rw [map_sub, cc_ev' cA0, cc_ev' cA1, sub_self]
  have hH := ig_dlog (B.ad a) (cc_ad B a) _ hH0 (hc.ad a) ((1 : Fin 2), b)
  have h2 := ig_ev cz1 integral_family_point_zero hH
  have z0 : ∀ c, pderiv k ((1 : Fin 2), b) (comp1 (B.actK k a) (pt k (n := 2) d 0) c) = 0 := fun c =>
    pderiv_ev_zero zero_constant_first_point _ _ (fun j l => by fin_cases j; simp [pderiv_pt])
  have d1 : pderiv k ((1 : Fin 2), b) (ev (n := 2) ![comp1 (B.actK k a) (pt k (n := 2) d 0), pt k d 1] h) =
      ev (n := 2) ![comp1 (B.actK k a) (pt k (n := 2) d 0), pt k d 1] (pderiv k ((1 : Fin 2), b) h) := by
    rw [d2 cA0]; simp [z0, pderiv_pt]
  have e1 : ∀ g : PS k 2 d, ev (n := 1) ![pt k d 0, 0]
      (ev (n := 2) ![comp1 (B.actK k a) (pt k (n := 2) d 0), pt k d 1] g) = ev (n := 1) ![B.actK k a, 0] g := by
    intro g
    rw [ev_ev cz1 cA0]
    congr 1
    funext j c
    fin_cases j
    · show ev (n := 1) ![pt k d 0, 0] (ev (n := 2) ![pt k d 0] (B.actK k a c)) = B.actK k a c
      rw [ev_ev cz1 zero_constant_first_point]
      have : (fun j c => ev (n := 1) ![pt k d 0, 0] ((![pt k (n := 2) d 0] : Fin 1 → Pt k 2 d) j c)) =
          (![pt k (n := 1) d 0] : Fin 1 → Pt k 1 d) := by
        funext j c; fin_cases j; simp [pt_apply, ev_X cz1]
      rw [this, gt_ev_pt_self]
    · simp [pt_apply, ev_X cz1]
  have e2 : ∀ g : PS k 2 d, ev (n := 1) ![B.actK k a] (ev (n := 1) ![pt k d 0, 0] g) =
      ev (n := 1) ![B.actK k a, 0] g := by
    intro g
    rw [ev_ev cAk cz1]
    congr 1
    funext j c
    fin_cases j <;> simp [pt_apply, ev_X cAk, ev_zero' cAk]
  have z1 : ∀ c, pderiv k ((1 : Fin 2), b) (pt k (n := 2) d 0 c) = 0 := fun c => by simp [pderiv_pt]
  have zA : ∀ c, pderiv k ((1 : Fin 2), b) (comp1 (B.actK k (star a)) (pt k (n := 2) d 1) c) =
      ev (n := 2) ![pt k d 1] (pderiv k ((0 : Fin 1), b) (B.actK k (star a) c)) := fun c => d_y _ b
  have e3 : ∀ g : PS k 2 d, ev (n := 1) ![pt k d 0, 0]
      (ev (n := 2) ![pt k d 0, comp1 (B.actK k (star a)) (pt k (n := 2) d 1)] g) = ev (n := 1) ![pt k d 0, 0] g := by
    intro g
    rw [ev_ev cz1 cA1]
    congr 1
    funext j c
    fin_cases j
    · simp [pt_apply, ev_X cz1]
    · show ev (n := 1) ![pt k d 0, 0] (ev (n := 2) ![pt k d 1] (B.actK k (star a) c)) = 0
      rw [ez_y, const_actK', map_zero]
  have e4 : ∀ c, ev (n := 1) ![pt k d 0, 0] (ev (n := 2) ![pt k d 1] (pderiv k ((0 : Fin 1), b)
      (B.actK k (star a) c))) = C (dAct k B (star a) c b) := fun c => by
    rw [ez_y, cc_pderiv']; rfl
  rw [map_sub, ev_sub cz1, d1, e1, d2 cA1] at h2
  simp only [z1, mul_zero, Finset.sum_const_zero, zero_add, zA, ev_sum cz1, ev_mul cz1, e3, e4] at h2
  have e5 : ev (n := 1) ![B.actK k a] (sgOf k h b) = -ev (n := 1) ![B.actK k a, 0] (pderiv k ((1 : Fin 2), b) h) := by
    rw [← e2, ← ev_neg cAk]; rfl
  rw [e5]
  simp only [sgOf]
  convert h2 using 1
  simp only [neg_mul, Finset.sum_neg_distrib]
  ring
end ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.Nab
