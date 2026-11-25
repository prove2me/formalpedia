-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.connection_translation_of_poly
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T14:12:41.620907+00:00
-- url     : https://prove2.me/submissions/1c4a5393-b8d4-4d5e-85f3-12f86a7f61fa

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_GaugeTrans
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_NabTrans
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_nt_ev_smul
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_nt_expS_zero
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_nt_const_smul
import Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_gp_zero__bb72846b09b6
import Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_gt_ev_ev__a7884319006c
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_evP_comp1
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_evP_pt
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_eval_pair_points
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_gp_comp1
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_gp_pt
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_gt_comp1_comp1
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_gt_comp1_pt_right
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_gt_comp_inv
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_gt_const_ev
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_gt_const_ev_eq
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_gt_ev_add
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_gt_ev_expS
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_gt_ev_mul
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_gt_expS_add
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_gt_map_id
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_pair_points_zero_constant
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_single_point_zero_constant


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
open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ Finsupp
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.TB ReciprocityTheory.ChartRestriction.G.TB.WickVanishing
namespace ReciprocityTheory.ChartRestriction.G.TB.WickVanishing
theorem _root_.solution (hTP : TransPolySt) : NabTransSt := by
  intro k _ _ d O _ _ B B' φ φi lam hinv hl0 hl1 hF0 hF hA h hh w0 m f ι _ u P
  have hφ : GP φ := hinv.1
  have hp : ∀ {n : ℕ} (j : Fin n), GP (pt k (n := n) d j) := fun j => gp_pt j
  have hcφ : ∀ {n : ℕ} (a : Pt k n d), GP a → GP (comp1 φ a) := fun a ha => gp_comp1 φ a hφ ha
  have hBF : ∀ i, constantCoeff (B.G.F i) = 0 := B.G.const
  have fk : B.FK k = B.G.F := funext fun i => gt_map_id _
  have fk' : B'.FK k = transF B.G.F φ φi := funext fun i => (gt_map_id _).trans (hF i)
  have ak : ∀ a, B.actK k a = B.A.act a := fun a => funext fun i => gt_map_id _
  have ak' : ∀ a, B'.actK k a = B'.A.act a := fun a => funext fun i => gt_map_id _
  have hz0 : ∀ {n : ℕ}, GP (0 : Pt k n d) := gp_zero₂
  have hh0 : constantCoeff h = 0 := by
    have := congrArg constantCoeff hh
    rwa [gt_const_ev_eq _ (pair_points_zero_constant hz0 (hp 0)), map_zero] at this
  have hlam0 : constantCoeff lam = 0 := by
    have := congrArg constantCoeff hl0
    rwa [gt_const_ev_eq _ (pair_points_zero_constant hz0 (hp 0)), map_zero] at this
  have hΦ2 : ∀ j, GP (![comp1 φ (pt k (n := 2) d 0), comp1 φ (pt k (n := 2) d 1)] j) :=
    pair_points_zero_constant (hcφ _ (hp 0)) (hcφ _ (hp 1))
  have hBa : GP (B.A.act w0) := B.A.const w0
  have hB'a : GP (B'.A.act w0) := B'.A.const w0
  have hx' := gp_comp1 _ _ hB'a (hp (n := 1) 0)
  have hx := gp_comp1 _ _ hBa (hp (n := 1) 0)

  have Ha : comp1 φ (comp1 (B'.A.act w0) (pt k (n := 1) d 0)) = comp1 (B.A.act w0) φ := by
    rw [hA w0, gt_comp1_comp1 φi _ (gp_comp1 _ φ hBa hφ) _ (hp 0),
      gt_comp1_comp1 (B.A.act w0) φ hφ _ (hp 0), gt_comp_inv hinv _ (gp_comp1 _ _ hBa (hcφ _ (hp 0))),
      gt_comp1_pt_right]

  have hL : B'.hL k (ev ![comp1 φ (pt k (n := 2) d 0), comp1 φ (pt k (n := 2) d 1)] h + lam) w0 =
      ev ![φ] (B.hL k h w0) + ev ![pt k (n := 1) d 0, comp1 (B'.A.act w0) (pt k (n := 1) d 0)] lam := by
    unfold FB.hL
    rw [ak', ak, gt_ev_add _ (pair_points_zero_constant (hp 0) hx'), gt_ev_ev' _ _ (pair_points_zero_constant (hp 0) hx') hΦ2, eval_pair_points,
      evP_comp1 _ (pair_points_zero_constant (hp 0) hx') φ _ (hp 0), evP_comp1 _ (pair_points_zero_constant (hp 0) hx') φ _ (hp 1),
      evP_pt _ (pair_points_zero_constant (hp 0) hx'), evP_pt _ (pair_points_zero_constant (hp 0) hx'),
      gt_ev_ev' _ _ (single_point_zero_constant hφ) (pair_points_zero_constant (hp 0) hx), eval_pair_points, evP_comp1 _ (single_point_zero_constant hφ) _ _ (hp 0),
      evP_pt _ (single_point_zero_constant hφ)]
    congr 2
    change ![comp1 φ (pt k (n := 1) d 0), comp1 φ (comp1 (B'.A.act w0) (pt k (n := 1) d 0))] =
      ![φ, comp1 (B.A.act w0) φ]
    rw [gt_comp1_pt_right, Ha]
  have cL : constantCoeff (ev ![pt k (n := 1) d 0, comp1 (B'.A.act w0) (pt k (n := 1) d 0)] lam) = 0 :=
    gt_const_ev _ (pair_points_zero_constant (hp 0) hx') lam hlam0
  have chL : constantCoeff (B.hL k h w0) = 0 := by
    unfold FB.hL
    rw [ak]
    exact gt_const_ev _ (pair_points_zero_constant (hp 0) hx) h hh0

  have hG : ev ![φ] f * FB.expS k (-((m : k) •
        ev ![pt k (n := 1) d 0, comp1 (B'.actK k w0) (pt k (n := 1) d 0)] lam)) *
      FB.expS k ((m : k) • B'.hL k (ev ![comp1 φ (pt k (n := 2) d 0), comp1 φ (pt k (n := 2) d 1)] h + lam) w0) =
      ev ![φ] (f * FB.expS k ((m : k) • B.hL k h w0)) := by
    rw [hL, ak', smul_add, gt_expS_add _ _ (by rw [nt_const_smul, gt_const_ev _ (single_point_zero_constant hφ) _ chL, mul_zero])
      (by rw [nt_const_smul, cL, mul_zero]), gt_ev_mul _ (single_point_zero_constant hφ),
      gt_ev_expS _ (single_point_zero_constant hφ) _ (by rw [nt_const_smul, chL, mul_zero]), nt_ev_smul _ (single_point_zero_constant hφ)]
    have e : FB.expS k (-((m : k) • ev ![pt k (n := 1) d 0, comp1 (B'.A.act w0) (pt k (n := 1) d 0)] lam)) *
        FB.expS k ((m : k) • ev ![pt k (n := 1) d 0, comp1 (B'.A.act w0) (pt k (n := 1) d 0)] lam) = 1 := by
      rw [← gt_expS_add _ _ (by rw [map_neg, nt_const_smul, cL, mul_zero, neg_zero]) (by rw [nt_const_smul, cL, mul_zero]),
        neg_add_cancel, nt_expS_zero]
    calc _ = ev ![φ] f * FB.expS k ((m : k) • ev ![φ] (B.hL k h w0)) *
          (FB.expS k (-((m : k) • ev ![pt k (n := 1) d 0, comp1 (B'.A.act w0) (pt k (n := 1) d 0)] lam)) *
            FB.expS k ((m : k) • ev ![pt k (n := 1) d 0, comp1 (B'.A.act w0) (pt k (n := 1) d 0)] lam)) := by ring
      _ = _ := by rw [e, mul_one]
  unfold FB.nabVal
  rw [hG, fk', hTP k d B.G.F hBF (by intro i; rw [← fk]; exact hF0 i) φ φi hinv ι u P, fk,
    gt_const_ev_eq _ (single_point_zero_constant hφ)]
end ReciprocityTheory.ChartRestriction.G.TB.WickVanishing
