-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.Nab.second_derivative_shift_integral
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T14:00:36.030583+00:00
-- url     : https://prove2.me/submissions/061308fc-5be1-4753-ae3d-a374b6c94801

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_ConstantCoeffAddFirstSecond
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_IntegralFamilyFirstZeroSecond
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_Nab_d2
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_Nab_eval_first_axis_restrict
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_Nab_constantCoeff_second_factor
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_Nab_constantCoeff_add_second_third
import Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_G_TB_LogPf_ev_zero__a29edcfaf6d8
import Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_Nab_cc_ev__53681771e208
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_LogPf_CZ_cons
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_LogPf_CZ_nil
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_LogPf_CZ_pt
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_LogPf_cc_pt
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_LogPf_cz01
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_LogPf_cz1
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_LogPf_cz12
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_LogPf_czY
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_LogPf_czZ
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_LogPf_ev_X
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_LogPf_ev_ev
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_LogPf_ev_mul
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_LogPf_ev_neg
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_LogPf_ev_pt
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_LogPf_ev_sub
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_LogPf_ev_sum
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_LogPf_formalGroupLaw_ev_x_zero
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_LogPf_formal_ev_second_point_of_x_zero
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_LogPf_pderiv_ev_zero
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_LogPf_pderiv_pt
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_LogPf_pt_apply
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_Nab_ig_dlog
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_Nab_ig_ev
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_Nab_integral_family_pair_zero
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_Nab_zero_constant_first_point


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
    ∑ c, pderiv k ((1 : Fin 2), c) h * ev (n := 2) ![pt k d 1] (Jac (lawK k B) c b) +
      ev (n := 2) ![pt k d 0] (sgOf k h b) ∈ Ig R k (Fin 2 × Fin d) := by
  set A : Pt k 3 d := addOf (B.FK k) (pt k (n := 3) d 1) (pt k d 2) with hA
  have c02 : CZ (![pt k (n := 3) d 0, pt k d 2] : Fin 2 → Pt k 3 d) :=
    CZ.cons (cc_pt 0) (CZ.cons (cc_pt 2) CZ.nil)
  have c0A : CZ (![pt k (n := 3) d 0, A] : Fin 2 → Pt k 3 d) :=
    CZ.cons (cc_pt 0) (CZ.cons (constantCoeff_add_second_third B) CZ.nil)
  have hh : constantCoeff h = 0 := by
    have := congrArg constantCoeff hc.ax1
    rwa [cc_ev' cz1, map_zero] at this

  set H := ev (n := 3) ![pt k d 0, pt k d 1] h + ev (n := 3) ![pt k d 0, pt k d 2] h -
    ev (n := 3) ![pt k d 0, A] h with hH
  have hcH : constantCoeff H = 0 := by
    rw [hH, map_sub, map_add, cc_ev' cz01, cc_ev' c02, cc_ev' c0A, hh]
    simp
  have hI : pderiv k ((2 : Fin 3), b) H ∈ Ig R k (Fin 3 × Fin d) :=
    ig_dlog B.ph2 (constantCoeff_second_factor B) H hcH hc.ph2 _
  have hG := ig_ev (R := R) czZ integral_family_pair_zero hI

  have dA : ∀ c, pderiv k ((2 : Fin 3), b) (A c) =
      ev (n := 3) ![pt k d 1, pt k d 2] (pderiv k ((1 : Fin 2), b) (B.FK k c)) := by
    intro c
    show pderiv k _ (ev (n := 3) ![pt k d 1, pt k d 2] (B.FK k c)) = _
    rw [d2 cz12]
    simp [pderiv_pt]
  have step1 : pderiv k ((2 : Fin 3), b) H =
      ev (n := 3) ![pt k d 0, pt k d 2] (pderiv k ((1 : Fin 2), b) h) -
        ∑ c, ev (n := 3) ![pt k d 0, A] (pderiv k ((1 : Fin 2), c) h) *
          ev (n := 3) ![pt k d 1, pt k d 2] (pderiv k ((1 : Fin 2), b) (B.FK k c)) := by
    rw [hH, map_sub, map_add, pderiv_ev_zero cz01 h _ ?_, d2 c02, d2 c0A]
    · simp only [dA]
      simp [pderiv_pt]
    · intro j i
      fin_cases j <;> simp [pderiv_pt]

  have e02 : (fun j i => ev (n := 2) ![pt k d 0, pt k d 1, 0]
      ((![pt k (n := 3) d 0, pt k d 2] : Fin 2 → Pt k 3 d) j i)) = ![pt k (n := 2) d 0, 0] := by
    funext j i
    fin_cases j <;> simp [pt_apply, ev_X czZ, ev_zero' czZ]
  have e12 : (fun j i => ev (n := 2) ![pt k d 0, pt k d 1, 0]
      ((![pt k (n := 3) d 1, pt k d 2] : Fin 2 → Pt k 3 d) j i)) = ![pt k (n := 2) d 1, 0] := by
    funext j i
    fin_cases j <;> simp [pt_apply, ev_X czZ, ev_zero' czZ]
  have e0A : (fun j i => ev (n := 2) ![pt k d 0, pt k d 1, 0]
      ((![pt k (n := 3) d 0, A] : Fin 2 → Pt k 3 d) j i)) = ![pt k (n := 2) d 0, pt k d 1] := by
    funext j i
    fin_cases j
    · simp [pt_apply, ev_X czZ]
    · show ev (n := 2) ![pt k d 0, pt k d 1, 0] (ev (n := 3) ![pt k d 1, pt k d 2] (B.FK k i)) = pt k d 1 i
      rw [ev_ev czZ cz12, e12, ← formal_ev_second_point_of_x_zero,
        show ev (n := 1) ![pt k d 0, 0] (B.FK k i) = (X ((0 : Fin 1), i) : PS k 1 d) from
          formalGroupLaw_ev_x_zero (G := lawK k B) i, ev_X czY]
      rfl
  have e01 : (![pt k (n := 2) d 0, pt k d 1] : Fin 2 → Pt k 2 d) = fun j => pt k d j := by
    funext j
    fin_cases j <;> rfl
  have key : ev (n := 2) ![pt k d 0, pt k d 1, 0] (pderiv k ((2 : Fin 3), b) H) =
      ev (n := 2) ![pt k d 0, 0] (pderiv k ((1 : Fin 2), b) h) -
        ∑ c, pderiv k ((1 : Fin 2), c) h * ev (n := 2) ![pt k d 1] (Jac (lawK k B) c b) := by
    rw [step1, ev_sub czZ, ev_ev czZ c02, e02, ev_sum czZ]
    congr 1
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [ev_mul czZ, ev_ev czZ c0A, e0A, e01, ev_pt, ev_ev czZ cz12, e12, ← formal_ev_second_point_of_x_zero]
    rfl
  have tgt : ∑ c, pderiv k ((1 : Fin 2), c) h * ev (n := 2) ![pt k d 1] (Jac (lawK k B) c b) +
      ev (n := 2) ![pt k d 0] (sgOf k h b) =
        -ev (n := 2) ![pt k d 0, pt k d 1, 0] (pderiv k ((2 : Fin 3), b) H) := by
    rw [key, sgOf, ev_neg zero_constant_first_point, eval_first_axis_restrict]
    ring
  rw [tgt]
  exact neg_mem hG
end ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.Nab
