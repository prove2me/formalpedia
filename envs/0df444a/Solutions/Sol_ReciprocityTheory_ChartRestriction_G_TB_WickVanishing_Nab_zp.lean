-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.Nab.zp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T13:56:38.21181+00:00
-- url     : https://prove2.me/submissions/8cf26d71-0791-4c0e-ba29-88109303b2e4

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_IntegralFamilyPointZero
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_ConstantCoeffAddFirstSecond
import Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_G_TB_LogPf_ev_zero__a29edcfaf6d8
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_LogPf_CZ_cons
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_LogPf_CZ_nil
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_LogPf_CZ_pt
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_LogPf_cc_pt
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_LogPf_cz1
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_LogPf_czZ
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_LogPf_ev_X
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_LogPf_ev_ev
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_LogPf_ev_neg
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_LogPf_pderiv_ev
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_LogPf_pderiv_pt
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_LogPf_pt_apply


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
variable {k : Type} [CommRing k] {d : ℕ}
namespace ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.Nab
theorem _root_.solution (h : PS k 2 d) (i : Fin d) (p : Pt k 3 d) (hp : ∀ c, constantCoeff (p c) = 0)
    (hpz : ∀ c, pderiv k ((2 : Fin 3), i) (p c) = 0) :
    ev (n := 2) ![pt k d 0, pt k d 1, 0] (pderiv k ((2 : Fin 3), i) (ev (n := 3) ![p, pt k d 2] h)) =
      -ev (n := 2) ![fun c => ev (n := 2) ![pt k d 0, pt k d 1, 0] (p c)]
        (-ev (n := 1) ![pt k d 0, 0] (pderiv k ((1 : Fin 2), i) h)) := by
  have hq : CZ (![p, pt k d 2] : Fin 2 → Pt k 3 d) := CZ.cons hp (CZ.cons (cc_pt 2) CZ.nil)
  have hp' : CZ (![fun c => ev (n := 2) ![pt k d 0, pt k d 1, 0] (p c)] : Fin 1 → Pt k 2 d) :=
    CZ.cons (fun c => constantCoeff_ev czZ (hp c)) CZ.nil
  rw [pderiv_ev hq, Fintype.sum_prod_type, Fin.sum_univ_two]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, hpz, mul_zero, Finset.sum_const_zero,
    zero_add, pderiv_pt, Prod.mk.injEq, true_and, mul_ite, mul_one, Finset.sum_ite_eq',
    Finset.mem_univ, if_true]
  rw [ev_neg hp', neg_neg, ev_ev czZ hq, ev_ev hp' cz1]
  congr 1
  funext j c
  fin_cases j
  · simp [pt_apply, ev_X hp']
  · simp [pt_apply, ev_X czZ, ev_zero' hp']
end ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.Nab
