-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.Nab.dof_hL
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T14:30:26.432797+00:00
-- url     : https://prove2.me/submissions/5ec0662d-a75e-42fa-a2df-3bb34d64ccc6

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_CoeffActAdd
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_SigCancel
import Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_Nab_const_actK__1950e9d409b9
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_LogPf_CZ_cons
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_LogPf_CZ_nil
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_LogPf_CZ_pt
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_LogPf_cc_pt
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_LogPf_czY
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_LogPf_ev_X
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_LogPf_ev_ev
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_LogPf_ev_mul
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_LogPf_ev_sum
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_LogPf_pderiv_pt
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_LogPf_pt_apply
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_Nab_d2
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_Nab_hom_rel
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
theorem _root_.solution (B : FB R d O) (h : PS k 2 d) (w0 : O) (u : Fin d → k) :
    Dof (B.FK k) u (ev (n := 1) ![pt k d 0, B.actK k w0] h) =
      ∑ b, C (u b) * ev (n := 1) ![pt k d 0, B.actK k w0]
          (∑ c, pderiv k ((0 : Fin 2), c) h * ev (n := 2) ![pt k d 0] (Jac (lawK k B) c b)) +
        ∑ j, (∑ b, C (u b) * C (dAct k B w0 j b)) * ev (n := 1) ![pt k d 0, B.actK k w0]
          (∑ c, pderiv k ((1 : Fin 2), c) h * ev (n := 2) ![pt k d 1] (Jac (lawK k B) c j)) := by
  have cPA : CZ (![pt k (n := 1) d 0, B.actK k w0] : Fin 2 → Pt k 1 d) :=
    CZ.cons (cc_pt 0) (CZ.cons (const_actK' B w0) CZ.nil)
  have cAk : CZ (![B.actK k w0] : Fin 1 → Pt k 1 d) := CZ.cons (const_actK' B w0) CZ.nil
  have evx : ∀ g : PS k 1 d, ev (n := 1) ![pt k d 0, B.actK k w0] (ev (n := 2) ![pt k d 0] g) = g := by
    intro g
    rw [ev_ev cPA zero_constant_first_point]
    have : (fun j c => ev (n := 1) ![pt k d 0, B.actK k w0] ((![pt k (n := 2) d 0] : Fin 1 → Pt k 2 d) j c)) =
        (![pt k (n := 1) d 0] : Fin 1 → Pt k 1 d) := by
      funext j c; fin_cases j; simp [pt_apply, ev_X cPA]
    rw [this, gt_ev_pt_self]
  have evz : ∀ g : PS k 1 d, ev (n := 1) ![pt k d 0, B.actK k w0] (ev (n := 2) ![pt k d 1] g) = ev (n := 1) ![B.actK k w0] g := by
    intro g
    rw [ev_ev cPA czY]
    congr 1
    funext j c; fin_cases j; simp [pt_apply, ev_X cPA]
  have dh : ∀ j, pderiv k ((0 : Fin 1), j) (ev (n := 1) ![pt k d 0, B.actK k w0] h) = ev (n := 1) ![pt k d 0, B.actK k w0] (pderiv k ((0 : Fin 2), j) h) +
      ∑ c, ev (n := 1) ![pt k d 0, B.actK k w0] (pderiv k ((1 : Fin 2), c) h) * pderiv k ((0 : Fin 1), j) (B.actK k w0 c) := by
    intro j
    rw [d2 cPA]
    congr 1
    simp [pderiv_pt]
  have hDof : ∀ g : PS k 1 d, Dof (B.FK k) u g = ∑ j, (∑ b, C (u b) * Jac (lawK k B) j b) * pderiv k ((0 : Fin 1), j) g :=
    fun g => rfl
  have eD1 : ∀ b, ev (n := 1) ![pt k d 0, B.actK k w0] (∑ c, pderiv k ((0 : Fin 2), c) h * ev (n := 2) ![pt k d 0] (Jac (lawK k B) c b)) =
      ∑ c, ev (n := 1) ![pt k d 0, B.actK k w0] (pderiv k ((0 : Fin 2), c) h) * Jac (lawK k B) c b := by
    intro b; rw [ev_sum cPA]; simp only [ev_mul cPA, evx]
  have eD2 : ∀ j, ev (n := 1) ![pt k d 0, B.actK k w0] (∑ c, pderiv k ((1 : Fin 2), c) h * ev (n := 2) ![pt k d 1] (Jac (lawK k B) c j)) =
      ∑ c, ev (n := 1) ![pt k d 0, B.actK k w0] (pderiv k ((1 : Fin 2), c) h) * ev (n := 1) ![B.actK k w0] (Jac (lawK k B) c j) := by
    intro j; rw [ev_sum cPA]; simp only [ev_mul cPA, evz]
  have hm : ∀ c, ∑ j, (∑ b, C (u b) * Jac (lawK k B) j b) * pderiv k ((0 : Fin 1), j) (B.actK k w0 c) =
      ∑ j, (∑ b, C (u b) * C (dAct k B w0 j b)) * ev (n := 1) ![B.actK k w0] (Jac (lawK k B) c j) := by
    intro c
    calc ∑ j, (∑ b, C (u b) * Jac (lawK k B) j b) * pderiv k ((0 : Fin 1), j) (B.actK k w0 c)
        = ∑ b, C (u b) * ∑ j, pderiv k ((0 : Fin 1), j) (B.actK k w0 c) * Jac (lawK k B) j b := by
          simp only [Finset.sum_mul, Finset.mul_sum]
          rw [Finset.sum_comm]
          exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
      _ = ∑ b, C (u b) * ∑ j, ev (n := 1) ![B.actK k w0] (Jac (lawK k B) c j) * C (dAct k B w0 j b) :=
          Finset.sum_congr rfl fun b _ => by rw [hom_rel B w0 c b]
      _ = ∑ j, (∑ b, C (u b) * C (dAct k B w0 j b)) * ev (n := 1) ![B.actK k w0] (Jac (lawK k B) c j) := by
          simp only [Finset.sum_mul, Finset.mul_sum]
          rw [Finset.sum_comm]
          exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
  rw [hDof]
  simp only [dh, mul_add, Finset.sum_add_distrib, eD1, eD2]
  congr 1
  · simp only [Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
  · have e2 : ∑ j, (∑ b, C (u b) * Jac (lawK k B) j b) * ∑ c, ev (n := 1) ![pt k d 0, B.actK k w0] (pderiv k ((1 : Fin 2), c) h) *
        pderiv k ((0 : Fin 1), j) (B.actK k w0 c) =
        ∑ c, ev (n := 1) ![pt k d 0, B.actK k w0] (pderiv k ((1 : Fin 2), c) h) *
          ∑ j, (∑ b, C (u b) * Jac (lawK k B) j b) * pderiv k ((0 : Fin 1), j) (B.actK k w0 c) := by
      simp only [Finset.mul_sum]
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
    rw [e2]
    simp only [hm, Finset.mul_sum]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
end ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.Nab
