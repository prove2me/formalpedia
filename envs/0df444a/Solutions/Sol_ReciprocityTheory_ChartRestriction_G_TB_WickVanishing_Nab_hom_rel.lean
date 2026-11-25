-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.Nab.hom_rel
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T14:12:21.085081+00:00
-- url     : https://prove2.me/submissions/e2dc1ca7-753e-4e98-869c-5b280d15c78f

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_FirstDerivativeShiftIntegral
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_CoeffActAdd
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_Nab_homK
import Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_G_TB_LogPf_ev_zero__a29edcfaf6d8
import Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_Nab_cc_pderiv__e7c46f068b17
import Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_Nab_const_actK__1950e9d409b9
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_LogPf_CZ_cons
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_LogPf_CZ_nil
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_LogPf_CZ_pt
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_LogPf_cz1
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_LogPf_czY
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_LogPf_ev_X
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_LogPf_ev_ev
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_LogPf_ev_mul
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_LogPf_ev_sum
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_LogPf_pderiv_ev_zero
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_LogPf_pderiv_pt
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_LogPf_pt_apply
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_Nab_d2
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_Nab_d_F
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_Nab_d_y
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_Nab_ezF
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_Nab_ez_dF
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_Nab_ez_y
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
theorem _root_.solution (B : FB R d O) (a : O) (c b : Fin d) :
    ∑ j, pderiv k ((0 : Fin 1), j) (B.actK k a c) * Jac (lawK k B) j b =
      ∑ j, ev (n := 1) ![B.actK k a] (Jac (lawK k B) c j) * C (dAct k B a j b) := by
  have cP : CZ (![comp1 (B.actK k a) (pt k (n := 2) d 0), comp1 (B.actK k a) (pt k (n := 2) d 1)] : Fin 2 → Pt k 2 d) :=
    CZ.cons (fun l => constantCoeff_ev zero_constant_first_point (const_actK' B a l)) (CZ.cons (fun l => constantCoeff_ev czY (const_actK' B a l)) CZ.nil)
  have cAk : CZ (![B.actK k a] : Fin 1 → Pt k 1 d) := CZ.cons (const_actK' B a) CZ.nil
  have h := congrArg (fun g => ev (n := 1) ![pt k d 0, 0] (pderiv k ((1 : Fin 2), b) g)) (homK B a c)
  beta_reduce at h
  have z0 : ∀ j, pderiv k ((1 : Fin 2), b) (comp1 (B.actK k a) (pt k (n := 2) d 0) j) = 0 := fun j =>
    pderiv_ev_zero zero_constant_first_point _ _ (fun j l => by fin_cases j; simp [pderiv_pt])
  have zA : ∀ j, pderiv k ((1 : Fin 2), b) (comp1 (B.actK k a) (pt k (n := 2) d 1) j) =
      ev (n := 2) ![pt k d 1] (pderiv k ((0 : Fin 1), b) (B.actK k a j)) := fun j => d_y _ b
  have e1 : ∀ g : PS k 2 d, ev (n := 1) ![pt k d 0, 0]
      (ev (n := 2) ![comp1 (B.actK k a) (pt k (n := 2) d 0), comp1 (B.actK k a) (pt k (n := 2) d 1)] g) =
      ev (n := 1) ![B.actK k a] (ev (n := 1) ![pt k d 0, 0] g) := by
    intro g
    rw [ev_ev cz1 cP, ev_ev cAk cz1]
    congr 1
    funext j c
    fin_cases j
    · show ev (n := 1) ![pt k d 0, 0] (ev (n := 2) ![pt k d 0] (B.actK k a c)) = _
      rw [ev_ev cz1 zero_constant_first_point]
      have : (fun j c => ev (n := 1) ![pt k d 0, 0] ((![pt k (n := 2) d 0] : Fin 1 → Pt k 2 d) j c)) =
          (![pt k (n := 1) d 0] : Fin 1 → Pt k 1 d) := by
        funext j c; fin_cases j; simp [pt_apply, ev_X cz1]
      rw [this, gt_ev_pt_self]
      simp [pt_apply, ev_X cAk]
    · show ev (n := 1) ![pt k d 0, 0] (ev (n := 2) ![pt k d 1] (B.actK k a c)) = _
      rw [ez_y, const_actK', map_zero]
      simp [ev_zero' cAk]
  rw [d_F, d2 cP] at h
  simp only [z0, mul_zero, Finset.sum_const_zero, zero_add, zA, ev_sum cz1, ev_mul cz1, ezF, ez_dF, e1, ez_y,
    cc_pderiv'] at h
  rw [h]
  rfl
end ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.Nab
