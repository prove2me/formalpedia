-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.Val.E_nabla
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T14:12:38.17462+00:00
-- url     : https://prove2.me/submissions/435e82da-8975-4d3b-8a49-c6ef4d5aa60f

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_ConnectionSecondOfCommute
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_GaugeBilinearTermEqNegDoubleSum
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_HarmonicValueIntegral
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_Val_bE_const
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_Val_E_liftX
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_LogPf_CZ_pt
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_LogPf_pderiv_subst
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_Nab_Dof_X
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_Nab_cf_inl
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_Nab_cf_inr
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_Nab_nabla_eq


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
open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.TB ReciprocityTheory.ChartRestriction.G.TB.WickVanishing ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.Val
open ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.Nab
variable {R : Type} [CommRing R] {d : ℕ} {O : Type} [CommRing O] [StarRing O]
variable (k : Type) [CommRing k] [Algebra ℚ k] [Algebra R k]
variable {k}
namespace ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.Val
theorem _root_.solution (B : FB R d O) (h : PS k 2 d) (hax : ev (n := 1) ![0, pt k d 0] h = 0) (m : ℕ) (u : Fin d → k)
    (G : AA k d) : subst (bE k h) (nabla k B h m u 0 G) = Dof (B.FK k) u (subst (bE k h) G) := by
  have hc := bE_const k h hax
  have hb : HasSubst (bE k h) := hasSubst_of_constantCoeff_zero hc
  have hfm : subst (bE k h) (fm k h u) = 0 := by
    unfold fm
    rw [← coe_substAlgHom hb, map_sum]
    refine Finset.sum_eq_zero fun i _ => ?_
    rw [map_mul, map_sub, coe_substAlgHom hb, subst_X hb, E_liftX k h hax]
    simp [bE]
  have hE : ∀ t, subst (bE k h) (cf k B h u 0 t) = Dof (B.FK k) u (bE k h t) := by
    rintro (j | i)
    · rw [cf_inl, E_liftX k h hax]
      exact (Dof_X k (B.FK k) u j).symm
    · rw [cf_inr, Pi.zero_apply, map_zero, add_zero, E_liftX k h hax]
      rfl
  rw [nabla_eq, vf, ← coe_substAlgHom hb, map_sub, map_sum]
  simp only [map_mul, coe_substAlgHom hb, hfm, hE, mul_zero, zero_mul, sub_zero]
  unfold Dof
  simp only [LogPf.pderiv_subst hc, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun j _ => ?_
  ring
end ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.Val
