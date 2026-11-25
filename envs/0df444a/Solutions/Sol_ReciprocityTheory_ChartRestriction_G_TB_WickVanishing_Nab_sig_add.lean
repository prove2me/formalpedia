-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.Nab.sig_add
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T14:12:29.413715+00:00
-- url     : https://prove2.me/submissions/854a9f63-825d-4ef4-bb31-d928aded9c44

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_IntegralFamilyPointZero
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_ConstantCoeffAddFirstSecond
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_Nab_zp
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_Nab_cc_h
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_Nab_constantCoeff_first_factor
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_Nab_constantCoeff_add_first_second
import Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_Nab_cc_ev__53681771e208
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_LogPf_CZ_cons
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_LogPf_CZ_nil
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_LogPf_CZ_pt
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_LogPf_cc_pt
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_LogPf_cz01
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_LogPf_czZ
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_LogPf_ev_X
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_LogPf_ev_add
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_LogPf_ev_ev
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_LogPf_ev_pt
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_LogPf_ev_sub
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_LogPf_pderiv_ev_zero
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_LogPf_pderiv_pt
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_LogPf_pt_apply
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_Nab_ig_dlog
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_Nab_ig_ev
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_Nab_integral_family_pair_zero


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
theorem _root_.solution {B : FB R d O} {h : PS k 2 d} (hc : B.IsCanonGauge k h) (i : Fin d) :
    ev (n := 2) ![(lawK k B).F] (sgOf k h i) - ev (n := 2) ![pt k d 0] (sgOf k h i) -
      ev (n := 2) ![pt k d 1] (sgOf k h i) ∈ Ig R k (Fin 2 × Fin d) := by
  have c02 : CZ (![pt k (n := 3) d 0, pt k d 2] : Fin 2 → Pt k 3 d) := CZ.cons (cc_pt 0) (CZ.cons (cc_pt 2) CZ.nil)
  have c12 : CZ (![pt k (n := 3) d 1, pt k d 2] : Fin 2 → Pt k 3 d) := CZ.cons (cc_pt 1) (CZ.cons (cc_pt 2) CZ.nil)
  have cA : CZ (![addOf (B.FK k) (pt k (n := 3) d 0) (pt k d 1), pt k d 2] : Fin 2 → Pt k 3 d) :=
    CZ.cons (constantCoeff_add_first_second B) (CZ.cons (cc_pt 2) CZ.nil)
  have hH0 : constantCoeff (ev (n := 3) ![pt k d 0, pt k d 2] h + ev (n := 3) ![pt k d 1, pt k d 2] h -
      ev (n := 3) ![addOf (B.FK k) (pt k d 0) (pt k d 1), pt k d 2] h) = 0 := by
    rw [map_sub, map_add, cc_ev' c02, cc_ev' c12, cc_ev' cA, cc_h hc]
    simp
  have hH := ig_dlog B.ph1 (constantCoeff_first_factor B) _ hH0 hc.ph1 ((2 : Fin 3), i)
  have h2 := ig_ev czZ integral_family_pair_zero hH
  have z0 : ∀ c, pderiv k ((2 : Fin 3), i) (pt k (n := 3) d 0 c) = 0 := fun c => by simp [pderiv_pt]
  have z1 : ∀ c, pderiv k ((2 : Fin 3), i) (pt k (n := 3) d 1 c) = 0 := fun c => by simp [pderiv_pt]
  have zA : ∀ c, pderiv k ((2 : Fin 3), i) (addOf (B.FK k) (pt k (n := 3) d 0) (pt k d 1) c) = 0 := fun c =>
    pderiv_ev_zero cz01 _ _ (fun j l => by fin_cases j <;> simp [pderiv_pt])
  rw [map_sub, map_add, ev_sub czZ, ev_add czZ, zp h i _ (cc_pt 0) z0, zp h i _ (cc_pt 1) z1,
    zp h i _ (constantCoeff_add_first_second B) zA] at h2
  have f0 : (fun c => ev (n := 2) ![pt k d 0, pt k d 1, 0] (pt k (n := 3) d 0 c)) = pt k (n := 2) d 0 := by
    funext c; simp [pt_apply, ev_X czZ]
  have f1 : (fun c => ev (n := 2) ![pt k d 0, pt k d 1, 0] (pt k (n := 3) d 1 c)) = pt k (n := 2) d 1 := by
    funext c; simp [pt_apply, ev_X czZ]
  have fA : (fun c => ev (n := 2) ![pt k d 0, pt k d 1, 0] (addOf (B.FK k) (pt k (n := 3) d 0) (pt k d 1) c)) =
      (lawK k B).F := by
    funext c
    show ev (n := 2) ![pt k d 0, pt k d 1, 0] (ev (n := 3) ![pt k d 0, pt k d 1] (B.FK k c)) = B.FK k c
    rw [ev_ev czZ cz01]
    have : (fun j c => ev (n := 2) ![pt k d 0, pt k d 1, 0] ((![pt k (n := 3) d 0, pt k d 1] : Fin 2 → Pt k 3 d) j c)) =
        fun j => pt k (n := 2) d j := by
      funext j c; fin_cases j <;> simp [pt_apply, ev_X czZ]
    rw [this, ev_pt]
  have es : -ev (n := 1) ![pt k d 0, 0] (pderiv k ((1 : Fin 2), i) h) = sgOf k h i := rfl
  rw [f0, f1, fA, es] at h2
  have e : ev (n := 2) ![(lawK k B).F] (sgOf k h i) - ev (n := 2) ![pt k d 0] (sgOf k h i) -
      ev (n := 2) ![pt k d 1] (sgOf k h i) =
      -ev (n := 2) ![pt k d 0] (sgOf k h i) + -ev (n := 2) ![pt k d 1] (sgOf k h i) -
        -ev (n := 2) ![(lawK k B).F] (sgOf k h i) := by ring
  rw [e]
  exact h2
end ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.Nab
