-- Prove2me | solution 1 for ZhengQR.CostBounds.eoq_optimum
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-29T03:58:31.058898+00:00
-- url     : https://prove2.me/submissions/b5b50d8f-6e5d-48eb-ab56-c13b593101bf

import Mathlib
import Definitions.Def_ZhengQR_CostBounds_QRMachinery
import Definitions.Def_ZhengQR_CostBounds_Model

namespace ZhengQR.CostBounds

/-- Antiderivative of the EOQ inventory-cost rate. -/
noncomputable def aux_eoqopt_Psi (a h p : ℝ) (y : ℝ) : ℝ :=
  h / 2 * (max (y - a) 0) ^ 2 - p / 2 * (max (a - y) 0) ^ 2

lemma aux_eoqopt_cont (lam L h p : ℝ) : Continuous (eoqInvCost lam L h p) := by
  unfold eoqInvCost
  fun_prop

lemma aux_eoqopt_Psi_cont (a h p : ℝ) : Continuous (aux_eoqopt_Psi a h p) := by
  unfold aux_eoqopt_Psi
  fun_prop

lemma aux_eoqopt_hasDeriv (lam L h p : ℝ) (y : ℝ) :
    HasDerivAt (aux_eoqopt_Psi (lam * L) h p) (eoqInvCost lam L h p y) y := by
  apply hasDerivAt_of_hasDerivAt_of_ne' (x := lam * L)
  · intro z hz
    rcases lt_or_gt_of_ne hz with hlt | hgt
    · have hev : aux_eoqopt_Psi (lam * L) h p =ᶠ[nhds z]
          fun w => -(p / 2) * (lam * L - w) ^ 2 := by
        filter_upwards [eventually_lt_nhds hlt] with w hw
        simp only [aux_eoqopt_Psi]
        rw [max_eq_right (by linarith : w - lam * L ≤ 0),
          max_eq_left (by linarith : 0 ≤ lam * L - w)]
        ring
      have hd : HasDerivAt (fun w => -(p / 2) * (lam * L - w) ^ 2)
          (eoqInvCost lam L h p z) z := by
        refine ((((hasDerivAt_id z).const_sub (lam * L)).pow 2).const_mul (-(p / 2))).congr_deriv ?_
        simp only [eoqInvCost, id]
        rw [max_eq_right (by linarith : z - lam * L ≤ 0),
          max_eq_left (by linarith : 0 ≤ lam * L - z)]
        push_cast
        ring
      exact hd.congr_of_eventuallyEq hev
    · have hev : aux_eoqopt_Psi (lam * L) h p =ᶠ[nhds z]
          fun w => (h / 2) * (w - lam * L) ^ 2 := by
        filter_upwards [eventually_gt_nhds hgt] with w hw
        simp only [aux_eoqopt_Psi]
        rw [max_eq_left (by linarith : 0 ≤ w - lam * L),
          max_eq_right (by linarith : lam * L - w ≤ 0)]
        ring
      have hd : HasDerivAt (fun w => (h / 2) * (w - lam * L) ^ 2)
          (eoqInvCost lam L h p z) z := by
        refine ((((hasDerivAt_id z).sub_const (lam * L)).pow 2).const_mul (h / 2)).congr_deriv ?_
        simp only [eoqInvCost, id]
        rw [max_eq_left (by linarith : 0 ≤ z - lam * L),
          max_eq_right (by linarith : lam * L - z ≤ 0)]
        push_cast
        ring
      exact hd.congr_of_eventuallyEq hev
  · exact (aux_eoqopt_Psi_cont _ _ _).continuousAt
  · exact (aux_eoqopt_cont _ _ _ _).continuousAt

lemma aux_eoqopt_integral (lam L h p s t : ℝ) :
    ∫ y in s..t, eoqInvCost lam L h p y
      = aux_eoqopt_Psi (lam * L) h p t - aux_eoqopt_Psi (lam * L) h p s :=
  intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun y _ => aux_eoqopt_hasDeriv lam L h p y)
    ((aux_eoqopt_cont lam L h p).intervalIntegrable s t)

lemma aux_eoqopt_Fbound (a h p Q r : ℝ) (hh : 0 < h) (hp : 0 < p) (hQ : 0 < Q) :
    h * p * Q ^ 2 / 2 ≤ (h + p) * (aux_eoqopt_Psi a h p (r + Q) - aux_eoqopt_Psi a h p r) ∧
    ((h + p) * (aux_eoqopt_Psi a h p (r + Q) - aux_eoqopt_Psi a h p r) = h * p * Q ^ 2 / 2 →
      (h + p) * (r - a) + h * Q = 0) := by
  unfold aux_eoqopt_Psi
  rcases le_total 0 (r - a) with hu | hu
  · rw [max_eq_left (by linarith : 0 ≤ r + Q - a), max_eq_right (by linarith : a - (r + Q) ≤ 0),
      max_eq_left hu, max_eq_right (by linarith : a - r ≤ 0)]
    have key : (h + p) * (h / 2 * (r + Q - a) ^ 2 - p / 2 * 0 ^ 2 - (h / 2 * (r - a) ^ 2 - p / 2 * 0 ^ 2))
        - h * p * Q ^ 2 / 2 = (h + p) * h * (r - a) * Q + h ^ 2 * Q ^ 2 / 2 := by ring
    have h1 : 0 ≤ (h + p) * h * (r - a) * Q := by positivity
    have h2 : 0 < h ^ 2 * Q ^ 2 / 2 := by positivity
    constructor
    · linarith
    · intro heq; exfalso; linarith
  · rcases le_total 0 (r + Q - a) with hv | hv
    · rw [max_eq_left hv, max_eq_right (by linarith : a - (r + Q) ≤ 0),
        max_eq_right hu, max_eq_left (by linarith : 0 ≤ a - r)]
      have key : (h + p) * (h / 2 * (r + Q - a) ^ 2 - p / 2 * 0 ^ 2 - (h / 2 * 0 ^ 2 - p / 2 * (a - r) ^ 2))
          - h * p * Q ^ 2 / 2 = ((h + p) * (r - a) + h * Q) ^ 2 / 2 := by ring
      have h1 : 0 ≤ ((h + p) * (r - a) + h * Q) ^ 2 := sq_nonneg _
      constructor
      · linarith
      · intro heq
        have h2 : ((h + p) * (r - a) + h * Q) ^ 2 = 0 := by linarith
        exact pow_eq_zero_iff (n := 2) (by norm_num) |>.mp h2
    · rw [max_eq_right hv, max_eq_left (by linarith : 0 ≤ a - (r + Q)),
        max_eq_right hu, max_eq_left (by linarith : 0 ≤ a - r)]
      have key : (h + p) * (h / 2 * 0 ^ 2 - p / 2 * (a - (r + Q)) ^ 2 - (h / 2 * 0 ^ 2 - p / 2 * (a - r) ^ 2))
          - h * p * Q ^ 2 / 2 = (h + p) * p * (-(r + Q - a)) * Q + p ^ 2 * Q ^ 2 / 2 := by ring
      have h0 : 0 ≤ -(r + Q - a) := by linarith
      have h1 : 0 ≤ (h + p) * p * (-(r + Q - a)) * Q := by positivity
      have h2 : 0 < p ^ 2 * Q ^ 2 / 2 := by positivity
      constructor
      · linarith
      · intro heq; exfalso; linarith

lemma aux_eoqopt_Fval (a h p Q : ℝ) (hh : 0 < h) (hp : 0 < p) (hQ : 0 < Q) :
    aux_eoqopt_Psi a h p (a - h * Q / (h + p) + Q) - aux_eoqopt_Psi a h p (a - h * Q / (h + p))
      = h * p / (h + p) * Q ^ 2 / 2 := by
  have hhp : 0 < h + p := by linarith
  have e1 : a - h * Q / (h + p) + Q - a = p * Q / (h + p) := by field_simp; ring
  have e2 : a - (a - h * Q / (h + p) + Q) = -(p * Q / (h + p)) := by field_simp; ring
  have e3 : a - h * Q / (h + p) - a = -(h * Q / (h + p)) := by ring
  have e4 : a - (a - h * Q / (h + p)) = h * Q / (h + p) := by ring
  have p1 : 0 ≤ p * Q / (h + p) := by positivity
  have p2 : 0 ≤ h * Q / (h + p) := by positivity
  unfold aux_eoqopt_Psi
  rw [e1, e2, e3, e4, max_eq_left p1, max_eq_right (by linarith : -(p * Q / (h + p)) ≤ 0),
    max_eq_right (by linarith : -(h * Q / (h + p)) ≤ 0), max_eq_left p2]
  field_simp
  ring

end ZhengQR.CostBounds

open ZhengQR.CostBounds

theorem solution (M : QRModel) :
    (∀ Q : ℝ, 0 ≤ Q → Hfun M.Gd M.lam M.K Q = M.h * M.p / (M.h + M.p) * Q) ∧
    (∀ Q : ℝ, IsOptQty M.Gd M.lam M.K Q ↔ Q = M.Qd) ∧
    Cfun M.Gd M.lam M.K M.Qd = Hfun M.Gd M.lam M.K M.Qd := by
  have hlam := M.lam_pos
  have hK := M.K_pos
  have hh := M.h_pos
  have hp := M.p_pos
  have hhp : 0 < M.h + M.p := by linarith
  have hqr : ∀ Q r : ℝ, qrCost M.Gd M.lam M.K Q r
      = (M.lam * M.K + (aux_eoqopt_Psi (M.lam * M.L) M.h M.p (r + Q)
          - aux_eoqopt_Psi (M.lam * M.L) M.h M.p r)) / Q := by
    intro Q r
    simp only [qrCost, QRModel.Gd]
    rw [aux_eoqopt_integral]
  have hr0 : ∀ Q : ℝ, 0 < Q →
      reorderPt M.Gd M.lam M.K Q = M.lam * M.L - M.h * Q / (M.h + M.p) := by
    intro Q hQ
    have hval := aux_eoqopt_Fval (M.lam * M.L) M.h M.p Q hh hp hQ
    have hopt : IsOptReorder M.Gd M.lam M.K Q (M.lam * M.L - M.h * Q / (M.h + M.p)) := by
      intro r'
      rw [hqr, hqr]
      apply div_le_div_of_nonneg_right _ hQ.le
      have h1 := (aux_eoqopt_Fbound (M.lam * M.L) M.h M.p Q r' hh hp hQ).1
      rw [hval]
      have h2 : M.h * M.p / (M.h + M.p) * Q ^ 2 / 2 * (M.h + M.p) = M.h * M.p * Q ^ 2 / 2 := by
        field_simp
      nlinarith
    have hex : ∃ r, IsOptReorder M.Gd M.lam M.K Q r := ⟨_, hopt⟩
    unfold reorderPt
    rw [dif_pos hex]
    have hc := hex.choose_spec (M.lam * M.L - M.h * Q / (M.h + M.p))
    rw [hqr, hqr] at hc
    have hc' := (div_le_div_iff_of_pos_right hQ).mp hc
    have hb := aux_eoqopt_Fbound (M.lam * M.L) M.h M.p Q hex.choose hh hp hQ
    rw [hval] at hc'
    have h2 : M.h * M.p / (M.h + M.p) * Q ^ 2 / 2 * (M.h + M.p) = M.h * M.p * Q ^ 2 / 2 := by
      field_simp
    have heq : (M.h + M.p) * (aux_eoqopt_Psi (M.lam * M.L) M.h M.p (hex.choose + Q)
        - aux_eoqopt_Psi (M.lam * M.L) M.h M.p hex.choose) = M.h * M.p * Q ^ 2 / 2 := by
      apply le_antisymm _ hb.1
      nlinarith
    have hlin := hb.2 heq
    field_simp
    linarith
  -- values of H
  have hH : ∀ Q : ℝ, 0 ≤ Q → Hfun M.Gd M.lam M.K Q = M.h * M.p / (M.h + M.p) * Q := by
    intro Q hQ
    rcases hQ.lt_or_eq with hQ | hQ
    · unfold Hfun
      rw [if_pos hQ, hr0 Q hQ]
      simp only [QRModel.Gd, eoqInvCost]
      have p2 : 0 ≤ M.h * Q / (M.h + M.p) := by positivity
      rw [max_eq_right (by linarith : M.lam * M.L - M.h * Q / (M.h + M.p) - M.lam * M.L ≤ 0),
        max_eq_left (by linarith : 0 ≤ M.lam * M.L - (M.lam * M.L - M.h * Q / (M.h + M.p)))]
      field_simp
      ring
    · subst hQ
      unfold Hfun
      rw [if_neg (lt_irrefl 0)]
      have hnn : ∀ y, 0 ≤ M.Gd y := by
        intro y
        simp only [QRModel.Gd, eoqInvCost]
        have := le_max_right (y - M.lam * M.L) 0
        have := le_max_right (M.lam * M.L - y) 0
        positivity
      have hzero : M.Gd (M.lam * M.L) = 0 := by
        simp [QRModel.Gd, eoqInvCost]
      have hex : ∃ y, ∀ z, M.Gd y ≤ M.Gd z := ⟨M.lam * M.L, fun z => by rw [hzero]; exact hnn z⟩
      unfold idealPt
      rw [dif_pos hex]
      have := hex.choose_spec (M.lam * M.L)
      rw [hzero] at this
      have := hnn hex.choose
      simp only [mul_zero]
      linarith
  -- values of C
  have hC : ∀ Q : ℝ, 0 < Q →
      Cfun M.Gd M.lam M.K Q = (M.lam * M.K + M.h * M.p / (M.h + M.p) * Q ^ 2 / 2) / Q := by
    intro Q hQ
    unfold Cfun
    rw [hr0 Q hQ, hqr, aux_eoqopt_Fval _ _ _ _ hh hp hQ]
  -- properties of Qd
  set c := M.h * M.p / (M.h + M.p) with hc_def
  have hc : 0 < c := by positivity
  have hQd_pos : 0 < M.Qd := by
    unfold QRModel.Qd eoqQty
    apply Real.sqrt_pos.mpr
    positivity
  have hQd_sq : M.Qd ^ 2 = 2 * M.lam * M.K * (M.h + M.p) / (M.h * M.p) := by
    unfold QRModel.Qd eoqQty
    rw [Real.sq_sqrt]
    positivity
  have hkey : M.lam * M.K = c * M.Qd ^ 2 / 2 := by
    rw [hQd_sq, hc_def]
    field_simp
  refine ⟨hH, ?_, ?_⟩
  · intro Q
    constructor
    · rintro ⟨hQ, hall⟩
      have h1 := hall M.Qd hQd_pos
      rw [hC Q hQ, hC M.Qd hQd_pos, hkey, div_le_div_iff₀ hQ hQd_pos] at h1
      have h2 : c * M.Qd * (Q - M.Qd) ^ 2 ≤ 0 := by nlinarith
      have h3 : 0 < c * M.Qd := by positivity
      have h4 : (Q - M.Qd) ^ 2 ≤ 0 := by
        by_contra hne
        push Not at hne
        have := mul_pos h3 hne
        linarith
      have h5 : (Q - M.Qd) ^ 2 = 0 := le_antisymm h4 (sq_nonneg _)
      have := pow_eq_zero_iff (n := 2) (by norm_num) |>.mp h5
      linarith
    · rintro rfl
      refine ⟨hQd_pos, fun Q' hQ' => ?_⟩
      rw [hC _ hQd_pos, hC Q' hQ', hkey, div_le_div_iff₀ hQd_pos hQ']
      have h3 : 0 ≤ c * M.Qd * (Q' - M.Qd) ^ 2 := by positivity
      nlinarith
  · rw [hC _ hQd_pos, hH _ hQd_pos.le, hkey]
    field_simp
    ring
