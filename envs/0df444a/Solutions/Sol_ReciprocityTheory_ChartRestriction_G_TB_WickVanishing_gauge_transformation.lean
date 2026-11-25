-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.gauge_transformation
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T14:08:08.068233+00:00
-- url     : https://prove2.me/submissions/7cb37a3a-02ba-4c7c-b41f-2e435018fe08

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_ChartChg
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_GaugeTrans
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_gt_ev_add
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_gt_ev_sub
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_gt_ev_zero
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_gt_const_ev
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_gp_pt
import Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_gp_zero__bb72846b09b6
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_gp_comp1
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_gp_addOf
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_gt_ev_expS
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_gt_expS_add
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_single_point_zero_constant
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_pair_points_zero_constant
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_triple_points_zero_constant
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_evP_pt
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_evP_comp1
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_evP_addOf
import Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_gt_ev_ev__a7884319006c
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_gt_comp1_comp1
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_gt_comp_inv
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_gt_const_ev_eq
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_gt_map_id
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_gt_comp1_zero
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_evP_zero
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_gt_comp1_pt_right
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
set_option autoImplicit false
noncomputable section
open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ Finsupp
namespace ReciprocityTheory.ChartRestriction.G.TB.WickVanishing
section Exp2
variable (A : Type) [CommRing A] [Algebra ℚ A]
end Exp2
section Ev
variable {k : Type} [CommRing k] {d : ℕ}
end Ev
section Calc
variable {k : Type} [CommRing k] {d : ℕ}
end Calc
section Calc2
variable {k : Type} [CommRing k] {d : ℕ}
end Calc2
section Main
private theorem gt_ev2_lemma {k : Type} [CommRing k] {d m n : ℕ} (V : Fin m → Pt k n d)
    (hV : ∀ j, GP (V j)) (x y : Pt k m d) (hx : GP x) (hy : GP y) (f : PS k 2 d) :
    ev V (ev ![x, y] f) = ev ![evP V x, evP V y] f := by
  rw [gt_ev_ev' V ![x, y] hV (pair_points_zero_constant hx hy) f]
  congr 1
  funext j
  fin_cases j <;> rfl
private theorem gt_cc3_lemma {k : Type} [CommRing k] {d n : ℕ} (f : PS k 2 d) (hf : constantCoeff f = 0)
    (V1 V2 V3 : Fin 2 → Pt k n d) (h1 : ∀ j, GP (V1 j)) (h2 : ∀ j, GP (V2 j)) (h3 : ∀ j, GP (V3 j)) :
    constantCoeff (ev V1 f + ev V2 f - ev V3 f) = 0 := by
  rw [map_sub, map_add, gt_const_ev V1 h1 f hf, gt_const_ev V2 h2 f hf, gt_const_ev V3 h3 f hf]
  all_goals simp
private theorem gt_cc2_lemma {k : Type} [CommRing k] {d n : ℕ} (f : PS k 2 d) (hf : constantCoeff f = 0)
    (V1 V2 : Fin 2 → Pt k n d) (h1 : ∀ j, GP (V1 j)) (h2 : ∀ j, GP (V2 j)) :
    constantCoeff (ev V1 f - ev V2 f) = 0 := by
  rw [map_sub, gt_const_ev V1 h1 f hf, gt_const_ev V2 h2 f hf]
  all_goals simp
end Main
end ReciprocityTheory.ChartRestriction.G.TB.WickVanishing
end
end

set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ Finsupp
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.TB ReciprocityTheory.ChartRestriction.G.TB.WickVanishing
namespace ReciprocityTheory.ChartRestriction.G.TB.WickVanishing
theorem _root_.solution : GaugeTransSt := by
  intro k _ _ d O _ _ B B' φ φi lam hinv hl0 hl1 hF hA hp1 hp2 hsy had h hh
  obtain ⟨hφ, hφi, hc1, hc2⟩ := id hinv
  have z1 : GP (0 : Pt k 1 d) := gp_zero₂
  have q1 : GP (pt k (n := 1) d 0) := gp_pt 0
  have q2 : ∀ j : Fin 2, GP (pt k (n := 2) d j) := fun j => gp_pt j
  have q3 : ∀ j : Fin 3, GP (pt k (n := 3) d j) := fun j => gp_pt j
  have hFc : ∀ i, constantCoeff (B.G.F i) = 0 := B.G.const
  have hFc' : ∀ i, constantCoeff (B'.G.F i) = 0 := B'.G.const
  have hAc : ∀ a, GP (B.A.act a) := fun a => B.A.const a
  have hAc' : ∀ a, GP (B'.A.act a) := fun a => B'.A.const a
  have hΦ2 : ∀ j, GP ((![comp1 φ (pt k (n := 2) d 0), comp1 φ (pt k (n := 2) d 1)] : Fin 2 → Pt k 2 d) j) :=
    pair_points_zero_constant (gp_comp1 φ _ hφ (q2 0)) (gp_comp1 φ _ hφ (q2 1))
  have hΦ3 : ∀ j, GP ((![comp1 φ (pt k (n := 3) d 0), comp1 φ (pt k (n := 3) d 1), comp1 φ (pt k (n := 3) d 2)] : Fin 3 → Pt k 3 d) j) :=
    triple_points_zero_constant (gp_comp1 φ _ hφ (q3 0)) (gp_comp1 φ _ hφ (q3 1)) (gp_comp1 φ _ hφ (q3 2))
  have ev20 : evP ![comp1 φ (pt k (n := 2) d 0), comp1 φ (pt k (n := 2) d 1)] (pt k (n := 2) d 0) = comp1 φ (pt k (n := 2) d 0) := evP_pt _ hΦ2 0
  have ev21 : evP ![comp1 φ (pt k (n := 2) d 0), comp1 φ (pt k (n := 2) d 1)] (pt k (n := 2) d 1) = comp1 φ (pt k (n := 2) d 1) := evP_pt _ hΦ2 1
  have ev30 : evP ![comp1 φ (pt k (n := 3) d 0), comp1 φ (pt k (n := 3) d 1), comp1 φ (pt k (n := 3) d 2)] (pt k (n := 3) d 0) = comp1 φ (pt k (n := 3) d 0) := evP_pt _ hΦ3 0
  have ev31 : evP ![comp1 φ (pt k (n := 3) d 0), comp1 φ (pt k (n := 3) d 1), comp1 φ (pt k (n := 3) d 2)] (pt k (n := 3) d 1) = comp1 φ (pt k (n := 3) d 1) := evP_pt _ hΦ3 1
  have ev32 : evP ![comp1 φ (pt k (n := 3) d 0), comp1 φ (pt k (n := 3) d 1), comp1 φ (pt k (n := 3) d 2)] (pt k (n := 3) d 2) = comp1 φ (pt k (n := 3) d 2) := evP_pt _ hΦ3 2
  have hFK : B.FK k = B.G.F := by
    funext i
    exact gt_map_id _
  have hFK' : B'.FK k = B'.G.F := by
    funext i
    exact gt_map_id _
  have hAK : ∀ a, B.actK k a = B.A.act a := fun a => by
    funext i
    exact gt_map_id _
  have hAK' : ∀ a, B'.actK k a = B'.A.act a := fun a => by
    funext i
    exact gt_map_id _
  have hh0 : constantCoeff h = 0 := by
    rw [← gt_const_ev_eq _ (pair_points_zero_constant z1 q1) h, hh.ax0, map_zero]
  have hl0' : constantCoeff lam = 0 := by
    rw [← gt_const_ev_eq _ (pair_points_zero_constant z1 q1) lam, hl0, map_zero]
  have K2 : ∀ {m : ℕ} (x y : Pt k m d), GP x → GP y → ∀ f : PS k 2 d,
      ev ![x, y] (ev (n := 2) ![comp1 φ (pt k (n := 2) d 0), comp1 φ (pt k (n := 2) d 1)] f) = ev ![comp1 φ x, comp1 φ y] f := by
    intro m x y hx hy f
    have a0 : evP ![x, y] (pt k (n := 2) d 0) = x := evP_pt _ (pair_points_zero_constant hx hy) 0
    have a1 : evP ![x, y] (pt k (n := 2) d 1) = y := evP_pt _ (pair_points_zero_constant hx hy) 1
    rw [gt_ev2_lemma ![x, y] (pair_points_zero_constant hx hy) _ _ (gp_comp1 φ _ hφ (q2 0)) (gp_comp1 φ _ hφ (q2 1)) f,
      evP_comp1 ![x, y] (pair_points_zero_constant hx hy) φ _ (q2 0), evP_comp1 ![x, y] (pair_points_zero_constant hx hy) φ _ (q2 1), a0, a1]
  have KH : ∀ {m : ℕ} (x y : Pt k m d), GP x → GP y →
      ev ![x, y] (ev (n := 2) ![comp1 φ (pt k (n := 2) d 0), comp1 φ (pt k (n := 2) d 1)] h + lam) = ev ![comp1 φ x, comp1 φ y] h + ev ![x, y] lam := by
    intro m x y hx hy
    rw [gt_ev_add _ (pair_points_zero_constant hx hy), K2 x y hx hy h]
  have TI : ∀ {m : ℕ} (x y : Pt k m d), GP x → GP y →
      addOf B'.G.F x y = comp1 φi (addOf B.G.F (comp1 φ x) (comp1 φ y)) := by
    intro m x y hx hy
    have hxy := pair_points_zero_constant hx hy
    have a0 : evP ![x, y] (pt k (n := 2) d 0) = x := evP_pt _ hxy 0
    have a1 : evP ![x, y] (pt k (n := 2) d 1) = y := evP_pt _ hxy 1
    have hA2 : GP (addOf B.G.F (comp1 φ (pt k (n := 2) d 0)) (comp1 φ (pt k (n := 2) d 1))) :=
      gp_addOf _ hFc _ _ (gp_comp1 φ _ hφ (q2 0)) (gp_comp1 φ _ hφ (q2 1))
    have hE : evP ![x, y] (addOf B.G.F (comp1 φ (pt k (n := 2) d 0)) (comp1 φ (pt k (n := 2) d 1))) =
        addOf B.G.F (comp1 φ x) (comp1 φ y) := by
      rw [evP_addOf _ hxy _ _ _ (gp_comp1 φ _ hφ (q2 0)) (gp_comp1 φ _ hφ (q2 1)),
        evP_comp1 _ hxy φ _ (q2 0), evP_comp1 _ hxy φ _ (q2 1), a0, a1]
    funext i
    show ev ![x, y] (B'.G.F i) = ev ![addOf B.G.F (comp1 φ x) (comp1 φ y)] (φi i)
    rw [hF i]
    show ev ![x, y] (ev ![addOf B.G.F (comp1 φ (pt k (n := 2) d 0)) (comp1 φ (pt k (n := 2) d 1))] (φi i)) = _
    rw [gt_ev_ev' _ _ hxy (single_point_zero_constant hA2) (φi i), ← hE]
    congr 1
    funext j
    fin_cases j
    rfl
  have TI' : ∀ {m : ℕ} (x y : Pt k m d), GP x → GP y →
      comp1 φ (addOf B'.G.F x y) = addOf B.G.F (comp1 φ x) (comp1 φ y) := by
    intro m x y hx hy
    rw [TI x y hx hy]
    exact gt_comp_inv hinv _ (gp_addOf _ hFc _ _ (gp_comp1 φ x hφ hx) (gp_comp1 φ y hφ hy))
  have TA : ∀ (a : O) {m : ℕ} (x : Pt k m d), GP x →
      comp1 φ (comp1 (B'.A.act a) x) = comp1 (B.A.act a) (comp1 φ x) := by
    intro a m x hx
    rw [hA a, gt_comp1_comp1 φi _ (gp_comp1 _ φ (hAc a) hφ) x hx,
      gt_comp1_comp1 (B.A.act a) φ hφ x hx]
    exact gt_comp_inv hinv _ (gp_comp1 _ _ (hAc a) (gp_comp1 φ x hφ hx))
  have f0 : ev (n := 1) ![0, pt k (n := 1) d 0] (ev (n := 2) ![comp1 φ (pt k (n := 2) d 0), comp1 φ (pt k (n := 2) d 1)] h + lam) = 0 := by
    rw [gt_ev_add _ (pair_points_zero_constant z1 q1), hl0, add_zero, K2 _ _ z1 q1, gt_comp1_zero φ hφ, gt_comp1_pt_right]
    have e := congrArg (ev ![φ]) hh.ax0
    rw [gt_ev2_lemma ![φ] (single_point_zero_constant hφ) _ _ z1 q1, evP_zero ![φ] (single_point_zero_constant hφ),
      evP_pt ![φ] (single_point_zero_constant hφ), gt_ev_zero ![φ] (single_point_zero_constant hφ)] at e
    exact e
  have f1 : ev (n := 1) ![pt k (n := 1) d 0, 0] (ev (n := 2) ![comp1 φ (pt k (n := 2) d 0), comp1 φ (pt k (n := 2) d 1)] h + lam) = 0 := by
    rw [gt_ev_add _ (pair_points_zero_constant q1 z1), hl1, add_zero, K2 _ _ q1 z1, gt_comp1_zero φ hφ, gt_comp1_pt_right]
    have e := congrArg (ev ![φ]) hh.ax1
    rw [gt_ev2_lemma ![φ] (single_point_zero_constant hφ) _ _ q1 z1, evP_zero ![φ] (single_point_zero_constant hφ),
      evP_pt ![φ] (single_point_zero_constant hφ), gt_ev_zero ![φ] (single_point_zero_constant hφ)] at e
    exact e
  have gF3 : GP (addOf B.G.F (pt k (n := 3) d 0) (pt k (n := 3) d 1)) := gp_addOf _ hFc _ _ (q3 0) (q3 1)
  have gF3' : GP (addOf B'.G.F (pt k (n := 3) d 0) (pt k (n := 3) d 1)) := gp_addOf _ hFc' _ _ (q3 0) (q3 1)
  have gG3 : GP (addOf B.G.F (pt k (n := 3) d 1) (pt k (n := 3) d 2)) := gp_addOf _ hFc _ _ (q3 1) (q3 2)
  have gG3' : GP (addOf B'.G.F (pt k (n := 3) d 1) (pt k (n := 3) d 2)) := gp_addOf _ hFc' _ _ (q3 1) (q3 2)
  have e1 : B.ph1 = FB.expS k (ev (n := 3) ![pt k (n := 3) d 0, pt k (n := 3) d 2] h + ev (n := 3) ![pt k (n := 3) d 1, pt k (n := 3) d 2] h - ev (n := 3) ![addOf B.G.F (pt k (n := 3) d 0) (pt k (n := 3) d 1), pt k (n := 3) d 2] h) := by
    have e := hh.ph1
    rw [hFK] at e
    exact (gt_map_id _).symm.trans e
  have e2 : B.ph2 = FB.expS k (ev (n := 3) ![pt k (n := 3) d 0, pt k (n := 3) d 1] h + ev (n := 3) ![pt k (n := 3) d 0, pt k (n := 3) d 2] h - ev (n := 3) ![pt k (n := 3) d 0, addOf B.G.F (pt k (n := 3) d 1) (pt k (n := 3) d 2)] h) := by
    have e := hh.ph2
    rw [hFK] at e
    exact (gt_map_id _).symm.trans e
  have esy : B.sy = FB.expS k (ev (n := 2) ![pt k (n := 2) d 1, pt k (n := 2) d 0] h - h) := (gt_map_id _).symm.trans hh.sy
  have ead : ∀ a, B.ad a = FB.expS k (ev (n := 2) ![comp1 (B.A.act a) (pt k (n := 2) d 0), pt k (n := 2) d 1] h - ev (n := 2) ![pt k (n := 2) d 0, comp1 (B.A.act (star a)) (pt k (n := 2) d 1)] h) := by
    intro a
    have e := hh.ad a
    rw [hAK a, hAK (star a)] at e
    exact (gt_map_id _).symm.trans e
  have ccM := gt_cc3_lemma h hh0 _ _ _ (pair_points_zero_constant (q3 0) (q3 2)) (pair_points_zero_constant (q3 1) (q3 2)) (pair_points_zero_constant gF3 (q3 2))
  have ccL1 := gt_cc3_lemma lam hl0' _ _ _ (pair_points_zero_constant (q3 0) (q3 2)) (pair_points_zero_constant (q3 1) (q3 2)) (pair_points_zero_constant gF3' (q3 2))
  have ccM2 := gt_cc3_lemma h hh0 _ _ _ (pair_points_zero_constant (q3 0) (q3 1)) (pair_points_zero_constant (q3 0) (q3 2)) (pair_points_zero_constant (q3 0) gG3)
  have ccL2 := gt_cc3_lemma lam hl0' _ _ _ (pair_points_zero_constant (q3 0) (q3 1)) (pair_points_zero_constant (q3 0) (q3 2)) (pair_points_zero_constant (q3 0) gG3')
  have ccS : constantCoeff (ev (n := 2) ![pt k (n := 2) d 1, pt k (n := 2) d 0] h - h) = 0 := by
    rw [map_sub, gt_const_ev_eq _ (pair_points_zero_constant (q2 1) (q2 0)), sub_self]
  have ccLS : constantCoeff (ev (n := 2) ![pt k (n := 2) d 1, pt k (n := 2) d 0] lam - lam) = 0 := by
    rw [map_sub, gt_const_ev_eq _ (pair_points_zero_constant (q2 1) (q2 0)), sub_self]
  have f2 : B'.ph1 = FB.expS k (ev (n := 3) ![pt k (n := 3) d 0, pt k (n := 3) d 2] (ev (n := 2) ![comp1 φ (pt k (n := 2) d 0), comp1 φ (pt k (n := 2) d 1)] h + lam) + ev (n := 3) ![pt k (n := 3) d 1, pt k (n := 3) d 2] (ev (n := 2) ![comp1 φ (pt k (n := 2) d 0), comp1 φ (pt k (n := 2) d 1)] h + lam) - ev (n := 3) ![addOf B'.G.F (pt k (n := 3) d 0) (pt k (n := 3) d 1), pt k (n := 3) d 2] (ev (n := 2) ![comp1 φ (pt k (n := 2) d 0), comp1 φ (pt k (n := 2) d 1)] h + lam)) := by
    rw [hp1, e1, gt_ev_expS _ hΦ3 _ ccM, ← gt_expS_add _ _ (gt_const_ev _ hΦ3 _ ccM) ccL1]
    congr 1
    rw [KH _ _ (q3 0) (q3 2), KH _ _ (q3 1) (q3 2), KH _ _ gF3' (q3 2), TI' _ _ (q3 0) (q3 1),
      gt_ev_sub _ hΦ3, gt_ev_add _ hΦ3,
      gt_ev2_lemma _ hΦ3 _ _ (q3 0) (q3 2), gt_ev2_lemma _ hΦ3 _ _ (q3 1) (q3 2), gt_ev2_lemma _ hΦ3 _ _ gF3 (q3 2),
      evP_addOf _ hΦ3 _ _ _ (q3 0) (q3 1), ev30, ev31, ev32]
    ring
  have f3 : B'.ph2 = FB.expS k (ev (n := 3) ![pt k (n := 3) d 0, pt k (n := 3) d 1] (ev (n := 2) ![comp1 φ (pt k (n := 2) d 0), comp1 φ (pt k (n := 2) d 1)] h + lam) + ev (n := 3) ![pt k (n := 3) d 0, pt k (n := 3) d 2] (ev (n := 2) ![comp1 φ (pt k (n := 2) d 0), comp1 φ (pt k (n := 2) d 1)] h + lam) - ev (n := 3) ![pt k (n := 3) d 0, addOf B'.G.F (pt k (n := 3) d 1) (pt k (n := 3) d 2)] (ev (n := 2) ![comp1 φ (pt k (n := 2) d 0), comp1 φ (pt k (n := 2) d 1)] h + lam)) := by
    rw [hp2, e2, gt_ev_expS _ hΦ3 _ ccM2, ← gt_expS_add _ _ (gt_const_ev _ hΦ3 _ ccM2) ccL2]
    congr 1
    rw [KH _ _ (q3 0) (q3 1), KH _ _ (q3 0) (q3 2), KH _ _ (q3 0) gG3', TI' _ _ (q3 1) (q3 2),
      gt_ev_sub _ hΦ3, gt_ev_add _ hΦ3,
      gt_ev2_lemma _ hΦ3 _ _ (q3 0) (q3 1), gt_ev2_lemma _ hΦ3 _ _ (q3 0) (q3 2), gt_ev2_lemma _ hΦ3 _ _ (q3 0) gG3,
      evP_addOf _ hΦ3 _ _ _ (q3 1) (q3 2), ev30, ev31, ev32]
    ring
  have f4 : B'.sy = FB.expS k (ev (n := 2) ![pt k (n := 2) d 1, pt k (n := 2) d 0] (ev (n := 2) ![comp1 φ (pt k (n := 2) d 0), comp1 φ (pt k (n := 2) d 1)] h + lam) - (ev (n := 2) ![comp1 φ (pt k (n := 2) d 0), comp1 φ (pt k (n := 2) d 1)] h + lam)) := by
    rw [hsy, esy, gt_ev_expS _ hΦ2 _ ccS, ← gt_expS_add _ _ (gt_const_ev _ hΦ2 _ ccS) ccLS]
    congr 1
    rw [KH _ _ (q2 1) (q2 0), gt_ev_sub _ hΦ2, gt_ev2_lemma _ hΦ2 _ _ (q2 1) (q2 0), ev21, ev20]
    ring
  have f5 : ∀ a, B'.ad a = FB.expS k (ev (n := 2) ![comp1 (B'.A.act a) (pt k (n := 2) d 0), pt k (n := 2) d 1] (ev (n := 2) ![comp1 φ (pt k (n := 2) d 0), comp1 φ (pt k (n := 2) d 1)] h + lam) - ev (n := 2) ![pt k (n := 2) d 0, comp1 (B'.A.act (star a)) (pt k (n := 2) d 1)] (ev (n := 2) ![comp1 φ (pt k (n := 2) d 0), comp1 φ (pt k (n := 2) d 1)] h + lam)) := by
    intro a
    have ccA := gt_cc2_lemma h hh0 _ _ (pair_points_zero_constant (gp_comp1 _ _ (hAc a) (q2 0)) (q2 1))
      (pair_points_zero_constant (q2 0) (gp_comp1 _ _ (hAc (star a)) (q2 1)))
    have ccLA := gt_cc2_lemma lam hl0' _ _ (pair_points_zero_constant (gp_comp1 _ _ (hAc' a) (q2 0)) (q2 1))
      (pair_points_zero_constant (q2 0) (gp_comp1 _ _ (hAc' (star a)) (q2 1)))
    rw [had a, ead a, gt_ev_expS _ hΦ2 _ ccA, ← gt_expS_add _ _ (gt_const_ev _ hΦ2 _ ccA) ccLA]
    congr 1
    rw [KH _ _ (gp_comp1 _ _ (hAc' a) (q2 0)) (q2 1), KH _ _ (q2 0) (gp_comp1 _ _ (hAc' (star a)) (q2 1)),
      TA a _ (q2 0), TA (star a) _ (q2 1),
      gt_ev_sub _ hΦ2, gt_ev2_lemma _ hΦ2 _ _ (gp_comp1 _ _ (hAc a) (q2 0)) (q2 1),
      gt_ev2_lemma _ hΦ2 _ _ (q2 0) (gp_comp1 _ _ (hAc (star a)) (q2 1)),
      evP_comp1 _ hΦ2 _ _ (q2 0), evP_comp1 _ hΦ2 _ _ (q2 1), ev20, ev21]
    ring
  refine ⟨f0, f1, ?_, ?_, ?_, ?_⟩
  · rw [hFK']
    exact (gt_map_id _).trans f2
  · rw [hFK']
    exact (gt_map_id _).trans f3
  · exact (gt_map_id _).trans f4
  · intro a
    rw [hAK' a, hAK' (star a)]
    exact (gt_map_id _).trans (f5 a)
end ReciprocityTheory.ChartRestriction.G.TB.WickVanishing
