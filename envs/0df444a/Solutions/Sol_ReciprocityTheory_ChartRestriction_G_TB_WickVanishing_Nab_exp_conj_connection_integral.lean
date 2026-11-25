-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.Nab.exp_conj_connection_integral
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T15:51:30.613947+00:00
-- url     : https://prove2.me/submissions/3bcf8983-5cf0-41e8-a8c4-a8af1eba76c0

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_SigCancel
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_ExpConjConnectionIntegral
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_Nab_liftX_one
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_Nab_liftX_add
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_Nab_liftX_sub
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_Nab_liftX_C
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_Nab_ig_FK
import Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_Nab_cc_ev__53681771e208
import Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_Nab_const_actK__1950e9d409b9
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_LogPf_CZ_cons
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_LogPf_CZ_nil
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_LogPf_CZ_pt
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_LogPf_cc_pt
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_LogPf_cz1
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_Nab_cc_h
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_Nab_cf_inl
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_Nab_cf_inr
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_Nab_dof_Cmul
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_Nab_dof_expS
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_Nab_dof_sig
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_Nab_hL_eq
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_Nab_ig_C
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_Nab_ig_X
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_Nab_ig_ev
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_Nab_ig_liftX
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_Nab_ig_pderiv
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_Nab_integral_family_point_zero
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_Nab_liftX_mul
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_Nab_liftX_sum
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_Nab_nabla_eq
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_Nab_rel_hL
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_Nab_vf_cf_liftX
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_Nab_vf_mul
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_gt_expS_add
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_nt_const_smul
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_nt_expS_zero


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
    (m : ℕ) (u' φ' : Fin d → R) (G : AA k d) (hG : G ∈ Ig R k (Fin d ⊕ Fin d)) :
    liftX k (FB.expS k (-((m : k) • B.hL k h w0))) *
      nabla k B h m (fun i => algebraMap R k (u' i))
        (fun i => algebraMap R k (φ' i) - (sg1 k h).mulVec (fun j => algebraMap R k (u' j)) i)
        (liftX k (FB.expS k ((m : k) • B.hL k h w0)) * G) ∈ Ig R k (Fin d ⊕ Fin d) := by
  have cPA : CZ (![pt k (n := 1) d 0, B.actK k w0] : Fin 2 → Pt k 1 d) :=
    CZ.cons (cc_pt 0) (CZ.cons (const_actK' B w0) CZ.nil)
  have ccf : constantCoeff ((m : k) • B.hL k h w0) = 0 := by
    rw [nt_const_smul, hL_eq, cc_ev' cPA, cc_h hc, mul_zero]
  have ccf' : constantCoeff (-((m : k) • B.hL k h w0)) = 0 := by rw [map_neg, ccf, neg_zero]
  have hinv : liftX k (FB.expS k (-((m : k) • B.hL k h w0))) * liftX k (FB.expS k ((m : k) • B.hL k h w0)) = 1 := by
    rw [← liftX_mul, ← gt_expS_add _ _ ccf' ccf, neg_add_cancel, nt_expS_zero, liftX_one]
  rw [nabla_eq, vf_mul, vf_cf_liftX, dof_expS _ _ ccf, liftX_mul]
  have e : ∀ (a b x y z : AA k d), a * (b * x * G + b * y - z * (b * G)) = (a * b) * (x * G + y - z * G) :=
    fun a b x y z => by ring
  rw [e, hinv, one_mul, smul_eq_C_mul, dof_Cmul, liftX_mul, liftX_C]
  have hfm : fm k h (fun i => algebraMap R k (u' i)) =
      ∑ i, X (Sum.inr i) * C (algebraMap R k (u' i)) - liftX k (∑ i, sgOf k h i * C (algebraMap R k (u' i))) := by
    simp only [fm, sub_mul, Finset.sum_sub_distrib, liftX_sum, liftX_mul, liftX_C]
  rw [hfm]
  have e2 : ∀ (cm D S XC y : AA k d), cm * D * G + y - cm * (XC - S) * G = y + cm * (D + S - XC) * G :=
    fun cm D S XC y => by ring
  rw [e2, ← liftX_add]
  have hm : (C ((m : ℕ) : k) : AA k d) ∈ Ig R k (Fin d ⊕ Fin d) := by
    rw [← map_natCast (algebraMap R k) m]
    exact ig_C _
  refine add_mem ?_ (mul_mem (mul_mem hm (sub_mem (ig_liftX (rel_hL hc w0 hw _ fun j => ⟨u' j, rfl⟩)) ?_)) hG)
  · simp only [vf]
    refine sum_mem fun t _ => mul_mem ?_ (ig_pderiv hG t)
    rcases t with j | i
    · rw [cf_inl]
      exact ig_liftX (sum_mem fun i _ => mul_mem (ig_C _) (ig_ev cz1 integral_family_point_zero (ig_pderiv (ig_FK B j) _)))
    · have e3 : cf k B h (fun i => algebraMap R k (u' i))
          (fun i => algebraMap R k (φ' i) - (sg1 k h).mulVec (fun j => algebraMap R k (u' j)) i) (Sum.inr i) =
          liftX k (Dof (B.FK k) (fun j => algebraMap R k (u' j)) (sgOf k h i) -
            C (∑ j, sg1 k h i j * algebraMap R k (u' j))) + C (algebraMap R k (φ' i)) := by
        rw [cf_inr, liftX_sub, liftX_C]
        simp only [Matrix.mulVec, dotProduct, map_sub]
        ring
      rw [e3]
      exact add_mem (ig_liftX (dof_sig hc u' i)) (ig_C _)
  · exact sum_mem fun i _ => mul_mem (ig_X _) (ig_C _)
end ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.Nab
