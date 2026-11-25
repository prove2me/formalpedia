-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.Nab.first_derivative_shift_integral
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T14:00:40.026705+00:00
-- url     : https://prove2.me/submissions/6f916320-6da7-4d9d-809a-523dd2ab7550

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_IntegralFamilyFirstZeroSecond
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_FirstDerivativeShiftIntegral
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_Nab_eval_first_axis_of_identity
import Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_G_TB_LogPf_ev_zero__a29edcfaf6d8
import Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_Nab_cc_ev__53681771e208
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_LogPf_CZ_cons
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_LogPf_CZ_nil
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_LogPf_CZ_pt
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_LogPf_cc_pt
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_LogPf_cz01
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_LogPf_cz12
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_LogPf_ev_X
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_LogPf_ev_add
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_LogPf_ev_ev
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_LogPf_ev_mul
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_LogPf_ev_pt
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_LogPf_ev_sub
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_LogPf_ev_sum
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_LogPf_formalGroupLaw_ev_x_zero
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_LogPf_pderiv_ev_zero
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_LogPf_pderiv_pt
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_LogPf_pt_apply
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_Nab_cc_h
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_Nab_constantCoeff_add_first_second
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_Nab_constantCoeff_first_factor
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_Nab_cz0z
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_Nab_d2
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_Nab_eval_first_axis_restrict
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_Nab_ig_dlog
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_Nab_ig_ev
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_Nab_integral_family_first_zero_second
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_Nab_lawK_F


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
    ∑ c, pderiv k ((0 : Fin 2), c) h * ev (n := 2) ![pt k d 0] (Jac (lawK k B) c b) -
      ev (n := 2) ![0, pt k d 1] (pderiv k ((0 : Fin 2), b) h) ∈ Ig R k (Fin 2 × Fin d) := by
  have c02 : CZ (![pt k (n := 3) d 0, pt k d 2] : Fin 2 → Pt k 3 d) := CZ.cons (cc_pt 0) (CZ.cons (cc_pt 2) CZ.nil)
  have cA : CZ (![addOf (B.FK k) (pt k (n := 3) d 0) (pt k d 1), pt k d 2] : Fin 2 → Pt k 3 d) :=
    CZ.cons (constantCoeff_add_first_second B) (CZ.cons (cc_pt 2) CZ.nil)
  have hH0 : constantCoeff (ev (n := 3) ![pt k d 0, pt k d 2] h + ev (n := 3) ![pt k d 1, pt k d 2] h -
      ev (n := 3) ![addOf (B.FK k) (pt k d 0) (pt k d 1), pt k d 2] h) = 0 := by
    rw [map_sub, map_add, cc_ev' c02, cc_ev' cz12, cc_ev' cA, cc_h hc]
    simp
  have hH := ig_dlog B.ph1 (constantCoeff_first_factor B) _ hH0 hc.ph1 ((1 : Fin 3), b)
  have h2 := ig_ev cz0z integral_family_first_zero_second hH
  have t1 : pderiv k ((1 : Fin 3), b) (ev (n := 3) ![pt k d 0, pt k d 2] h) = 0 :=
    pderiv_ev_zero c02 _ _ (fun j l => by fin_cases j <;> simp [pderiv_pt])
  have dd : pderiv k ((1 : Fin 3), b) (ev (n := 3) ![pt k d 1, pt k d 2] h) =
      ev (n := 3) ![pt k d 1, pt k d 2] (pderiv k ((0 : Fin 2), b) h) := by
    rw [d2 cz12]; simp [pderiv_pt]
  have t2 : ev (n := 2) ![pt k d 0, 0, pt k d 1] (pderiv k ((1 : Fin 3), b) (ev (n := 3) ![pt k d 1, pt k d 2] h)) =
      ev (n := 2) ![0, pt k d 1] (pderiv k ((0 : Fin 2), b) h) := by
    rw [dd, ev_ev cz0z cz12]
    congr 1
    funext j c
    fin_cases j <;> simp [pt_apply, ev_X cz0z]
  have z2 : ∀ c, pderiv k ((1 : Fin 3), b) (pt k (n := 3) d 2 c) = 0 := fun c => by simp [pderiv_pt]
  have dA : ∀ c, pderiv k ((1 : Fin 3), b) (addOf (B.FK k) (pt k (n := 3) d 0) (pt k d 1) c) =
      ev (n := 3) ![pt k d 0, pt k d 1] (pderiv k ((1 : Fin 2), b) (B.FK k c)) := by
    intro c
    show pderiv k ((1 : Fin 3), b) (ev (n := 3) ![pt k d 0, pt k d 1] (B.FK k c)) = _
    rw [d2 cz01]
    simp [pderiv_pt]
  have eB : ∀ g : PS k 2 d, ev (n := 2) ![pt k d 0, 0, pt k d 1] (ev (n := 3) ![pt k d 0, pt k d 1] g) =
      ev (n := 2) ![pt k d 0, 0] g := by
    intro g
    rw [ev_ev cz0z cz01]
    congr 1
    funext j c
    fin_cases j <;> simp [pt_apply, ev_X cz0z]
  have eA : ∀ g : PS k 2 d, ev (n := 2) ![pt k d 0, 0, pt k d 1]
      (ev (n := 3) ![addOf (B.FK k) (pt k (n := 3) d 0) (pt k d 1), pt k d 2] g) = g := by
    intro g
    rw [ev_ev cz0z cA]
    conv_rhs => rw [← ev_pt g]
    congr 1
    funext j c
    fin_cases j
    · show ev (n := 2) ![pt k d 0, 0, pt k d 1] (ev (n := 3) ![pt k d 0, pt k d 1] (B.FK k c)) = X ((0 : Fin 2), c)
      rw [eB]
      refine eval_first_axis_of_identity _ c ?_
      have := formalGroupLaw_ev_x_zero (lawK k B) c
      rwa [lawK_F] at this
    · simp [pt_apply, ev_X cz0z]
  have t3 : ev (n := 2) ![pt k d 0, 0, pt k d 1] (pderiv k ((1 : Fin 3), b)
      (ev (n := 3) ![addOf (B.FK k) (pt k (n := 3) d 0) (pt k d 1), pt k d 2] h)) =
      ∑ c, pderiv k ((0 : Fin 2), c) h * ev (n := 2) ![pt k d 0] (Jac (lawK k B) c b) := by
    rw [d2 cA]
    simp only [z2, mul_zero, Finset.sum_const_zero, add_zero, dA]
    rw [ev_sum cz0z]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [ev_mul cz0z, eA, eB, ← eval_first_axis_restrict]
    rfl
  rw [map_sub, map_add, ev_sub cz0z, ev_add cz0z, t1, ev_zero' cz0z, t2, t3] at h2
  have e : ∑ c, pderiv k ((0 : Fin 2), c) h * ev (n := 2) ![pt k d 0] (Jac (lawK k B) c b) -
      ev (n := 2) ![0, pt k d 1] (pderiv k ((0 : Fin 2), b) h) =
      -(0 + ev (n := 2) ![0, pt k d 1] (pderiv k ((0 : Fin 2), b) h) -
        ∑ c, pderiv k ((0 : Fin 2), c) h * ev (n := 2) ![pt k d 0] (Jac (lawK k B) c b)) := by ring
  rw [e]
  exact neg_mem h2
end ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.Nab
