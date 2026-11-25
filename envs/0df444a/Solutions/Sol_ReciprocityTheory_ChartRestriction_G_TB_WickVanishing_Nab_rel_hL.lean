-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.Nab.rel_hL
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T15:24:30.807183+00:00
-- url     : https://prove2.me/submissions/9c89c90d-87dd-48e9-b716-ff4c3625e469

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_CoeffActAdd
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_SigCancel
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_Nab_ig_dAct
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_Nab_hL_eq
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_Nab_dof_hL
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_Nab_sig_cancel
import Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_Nab_const_actK__1950e9d409b9
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_LogPf_CZ_cons
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_LogPf_CZ_nil
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_LogPf_CZ_pt
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_LogPf_cc_pt
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_LogPf_czY
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_LogPf_ev_X
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_LogPf_ev_add
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_LogPf_ev_ev
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_LogPf_ev_sub
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_LogPf_pt_apply
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_Nab_first_derivative_shift_integral
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_Nab_ig_C
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_Nab_ig_ev
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_Nab_ig_map
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_Nab_ig_pt
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_Nab_rel_ad
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_Nab_rel_sy
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_Nab_second_derivative_shift_integral
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
theorem _root_.solution {B : FB R d O} {h : PS k 2 d} (hc : B.IsCanonGauge k h) (w0 : O) (hw : w0 + star w0 = 1)
    (u : Fin d → k) (hu : ∀ j, ∃ r, algebraMap R k r = u j) :
    Dof (B.FK k) u (B.hL k h w0) + ∑ c, sgOf k h c * C (u c) ∈ Ig R k (Fin 1 × Fin d) := by
  have iu : ∀ b, (C (u b) : PS k 1 d) ∈ Ig R k (Fin 1 × Fin d) := fun b => by
    obtain ⟨r, hr⟩ := hu b
    rw [← hr]
    exact ig_C r
  have cPA : CZ (![pt k (n := 1) d 0, B.actK k w0] : Fin 2 → Pt k 1 d) :=
    CZ.cons (cc_pt 0) (CZ.cons (const_actK' B w0) CZ.nil)
  have iPA : ∀ j i, (![pt k (n := 1) d 0, B.actK k w0] : Fin 2 → Pt k 1 d) j i ∈ Ig R k (Fin 1 × Fin d) := by
    intro j i; fin_cases j
    · exact ig_pt _ _
    · exact ig_map _
  have evz : ∀ g : PS k 1 d, ev (n := 1) ![pt k d 0, B.actK k w0] (ev (n := 2) ![pt k d 1] g) =
      ev (n := 1) ![B.actK k w0] g := by
    intro g
    rw [ev_ev cPA czY]
    congr 1
    funext j c; fin_cases j; simp [pt_apply, ev_X cPA]
  have evx : ∀ g : PS k 1 d, ev (n := 1) ![pt k d 0, B.actK k w0] (ev (n := 2) ![pt k d 0] g) = g := by
    intro g
    rw [ev_ev cPA zero_constant_first_point]
    have : (fun j c => ev (n := 1) ![pt k d 0, B.actK k w0] ((![pt k (n := 2) d 0] : Fin 1 → Pt k 2 d) j c)) =
        (![pt k (n := 1) d 0] : Fin 1 → Pt k 1 d) := by
      funext j c; fin_cases j; simp [pt_apply, ev_X cPA]
    rw [this, gt_ev_pt_self]
  have E1 : ∀ b, ev (n := 1) ![pt k d 0, B.actK k w0]
      (∑ c, pderiv k ((0 : Fin 2), c) h * ev (n := 2) ![pt k d 0] (Jac (lawK k B) c b)) =
      (ev (n := 1) ![pt k d 0, B.actK k w0] (∑ c, pderiv k ((0 : Fin 2), c) h * ev (n := 2) ![pt k d 0]
          (Jac (lawK k B) c b) - ev (n := 2) ![0, pt k d 1] (pderiv k ((0 : Fin 2), b) h)) +
        ev (n := 1) ![pt k d 0, B.actK k w0] (ev (n := 2) ![pt k d 1] (sgOf k h b) +
          ev (n := 2) ![0, pt k d 1] (pderiv k ((0 : Fin 2), b) h)) +
        (∑ c, sgOf k h c * C (dAct k B (star w0) c b) - ev (n := 1) ![B.actK k w0] (sgOf k h b))) -
      ∑ c, sgOf k h c * C (dAct k B (star w0) c b) := by
    intro b
    rw [ev_sub cPA, ev_add cPA, evz]
    ring
  have E2 : ∀ j, ev (n := 1) ![pt k d 0, B.actK k w0]
      (∑ c, pderiv k ((1 : Fin 2), c) h * ev (n := 2) ![pt k d 1] (Jac (lawK k B) c j)) =
      ev (n := 1) ![pt k d 0, B.actK k w0] (∑ c, pderiv k ((1 : Fin 2), c) h * ev (n := 2) ![pt k d 1]
        (Jac (lawK k B) c j) + ev (n := 2) ![pt k d 0] (sgOf k h j)) - sgOf k h j := by
    intro j
    rw [ev_add cPA, evx]
    ring
  rw [hL_eq, dof_hL, ← sig_cancel B h w0 hw u]
  simp only [E1, E2, mul_sub, Finset.sum_sub_distrib]
  have key : ∀ (X1 X2 Y1 Y2 : PS k 1 d), X1 - Y1 + (X2 - Y2) + (Y1 + Y2) = X1 + X2 := fun _ _ _ _ => by ring
  rw [key]
  refine add_mem (sum_mem fun b _ => mul_mem (iu b) ?_) (sum_mem fun j _ => mul_mem ?_ ?_)
  · exact add_mem (add_mem (ig_ev cPA iPA (first_derivative_shift_integral hc b)) (ig_ev cPA iPA (rel_sy hc b))) (rel_ad hc w0 b)
  · exact sum_mem fun b _ => mul_mem (iu b) (ig_dAct B w0 j b)
  · exact ig_ev cPA iPA (second_derivative_shift_integral hc j)
end ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.Nab
