-- Prove2me | solution 1 for ReactiveCapacity.supplier_response_high
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-12T01:53:04.539395+00:00
-- url     : https://prove2.me/submissions/82ae8dff-d5d1-4293-8ed3-2571306a1e20

import Mathlib
import Definitions.Def_ReactiveCapacity_Model
import Definitions.Def_ReactiveCapacity_Game
import Theorems.Thm_ReactiveCapacity_retailer_stage_rule

open ReactiveCapacity

theorem solution (P : Params) (hP : P.Standing) (Qbar : ℝ) (hQ : 1 - P.αg ≤ Qbar)
    (σ : Profile) (hσ : IsPostInventorySPE P Qbar σ) (q w : ℝ) (hq : 0 < q)
    (hw : P.cost q < w) (hlow : (q * P.θH - w) * P.αb < q * P.θL - w) :
    {I : ℝ | 0 ≤ I ∧ ∀ I' : ℝ, 0 ≤ I' → σ.supplierValue P q w I' ≤ σ.supplierValue P q w I} =
      Set.Icc (max 0 (1 - Qbar)) P.αg := by
  rcases hP with ⟨hθL, hθLH, hk, hρ0, hρ1, hαb0, _hαb_lt, hαg_gt, hαg1⟩
  have hStand : P.Standing := ⟨hθL, hθLH, hk, hρ0, hρ1, hαb0, _hαb_lt, hαg_gt, hαg1⟩
  have hθH : 0 < P.θH := lt_trans hθL hθLH
  have hαg0 : 0 < P.αg := pos_of_mul_pos_left (lt_trans hθL hαg_gt) hθH.le
  have hαb1 : P.αb < 1 := by
    by_contra h
    have hge : 1 ≤ P.αb := le_of_not_gt h
    have := mul_le_mul_of_nonneg_right hge hθH.le
    linarith
  have hc_pos : 0 < P.cost q := mul_pos hk (pow_pos hq 2)
  have hw_pos : 0 < w := lt_trans hc_pos hw
  have hwc_pos : 0 < w - P.cost q := sub_pos.mpr hw
  have hQ_pos : 0 < Qbar := by linarith
  have hwL : w < q * P.θL := by
    have h1 : 0 < 1 - P.αb := sub_pos.mpr hαb1
    have h2 : (q * P.θL) * P.αb < (q * P.θH) * P.αb :=
      mul_lt_mul_of_pos_right (mul_lt_mul_of_pos_left hθLH hq) hαb0
    have h3 : w * (1 - P.αb) < (q * P.θL) * (1 - P.αb) := by linarith
    exact lt_of_mul_lt_mul_right h3 h1.le
  have hwH : w < q * P.θH := lt_trans hwL (mul_lt_mul_of_pos_left hθLH hq)
  have hreact_eq : ∀ I : ℝ, ∀ s : State, ∀ Q : ℝ, 0 ≤ I → I < Q →
      σ.react q w I s Q = min Qbar (Q - I) := by
    intro I s Q hI hIQ
    obtain ⟨hr0, hrQ, hropt⟩ := hσ.2.1 q w I s Q hq.le hw_pos.le hI hIQ
    let Istar := min Qbar (Q - I)
    have hIs0 : 0 ≤ Istar := le_min hQ_pos.le (sub_pos.mpr hIQ).le
    have hIsQ : Istar ≤ Qbar := min_le_left _ _
    have hge := hropt Istar hIs0 hIsQ
    have hIIs_le : I + Istar ≤ Q := by
      have := min_le_right Qbar (Q - I)
      dsimp [Istar]
      linarith
    have hval_star : P.supplierState q w I (received I Q Istar) Istar =
        (w - P.cost q) * (I + Istar) := by
      unfold Params.supplierState received
      rw [if_neg (not_le_of_gt hIQ), min_eq_left hIIs_le]
      ring
    rcases lt_trichotomy (σ.react q w I s Q) Istar with hlt | heq | hgt
    · exfalso
      have hleQ : I + σ.react q w I s Q ≤ Q := by linarith
      have hval_r : P.supplierState q w I (received I Q (σ.react q w I s Q))
          (σ.react q w I s Q) = (w - P.cost q) * (I + σ.react q w I s Q) := by
        unfold Params.supplierState received
        rw [if_neg (not_le_of_gt hIQ), min_eq_left hleQ]
        ring
      rw [hval_star, hval_r] at hge
      have := mul_lt_mul_of_pos_left (by linarith : I + σ.react q w I s Q < I + Istar) hwc_pos
      linarith
    · exact heq
    · exfalso
      have hIs_eq : Istar = Q - I := by
        dsimp [Istar] at hgt ⊢
        rcases le_or_gt Qbar (Q - I) with h1 | h1
        · exfalso
          rw [min_eq_left h1] at hgt
          linarith
        · exact min_eq_right h1.le
      have hgtQ : Q < I + σ.react q w I s Q := by linarith
      have hval_r : P.supplierState q w I (received I Q (σ.react q w I s Q))
          (σ.react q w I s Q) = w * Q - P.cost q * (I + σ.react q w I s Q) := by
        unfold Params.supplierState received
        rw [if_neg (not_le_of_gt hIQ), min_eq_right hgtQ.le]
      rw [hval_star, hval_r, hIs_eq] at hge
      have h1 : I + (Q - I) = Q := by ring
      rw [h1] at hge
      have := mul_lt_mul_of_pos_left hgtQ hc_pos
      linarith
  have hmade_bds : ∀ I : ℝ, ∀ s : State, ∀ Q : ℝ, 0 ≤ I →
      0 ≤ σ.made q w I s Q ∧ σ.made q w I s Q ≤ Qbar := by
    intro I s Q hI
    unfold Profile.made inSeason
    rcases le_or_gt Q I with hQI | hIQ
    · rw [if_pos hQI]
      exact ⟨le_refl 0, hQ_pos.le⟩
    · rw [if_neg (not_le_of_gt hIQ)]
      obtain ⟨hr0, hrQ, _⟩ := hσ.2.1 q w I s Q hq.le hw_pos.le hI hIQ
      exact ⟨hr0, hrQ⟩
  have hrecv_Imade : ∀ I : ℝ, ∀ s : State, ∀ Q : ℝ, 0 ≤ I →
      σ.recv q w I s Q = min Q (I + Qbar) ∧
      I + σ.made q w I s Q = max I (min Q (I + Qbar)) := by
    intro I s Q hI
    unfold Profile.recv Profile.made received inSeason
    rcases le_or_gt Q I with hQI | hIQ
    · rw [if_pos hQI, if_pos hQI]
      have hQIQ : Q ≤ I + Qbar := by linarith
      rw [min_eq_left hQIQ, max_eq_left hQI, add_zero]
      exact ⟨rfl, rfl⟩
    · rw [if_neg (not_le_of_gt hIQ), if_neg (not_le_of_gt hIQ), hreact_eq I s Q hI hIQ]
      have hsum : I + min Qbar (Q - I) = min Q (I + Qbar) := by
        rcases le_or_gt Qbar (Q - I) with h1 | h1
        · rw [min_eq_left h1, min_eq_right (by linarith)]
        · rw [min_eq_right h1.le, min_eq_left (by linarith)]
          ring
      rw [hsum, min_eq_left (min_le_left Q (I + Qbar)),
        max_eq_right (le_min hIQ.le (by linarith))]
      exact ⟨rfl, rfl⟩
  have hstep_opt : ∀ I : ℝ, ∀ s : State, 0 ≤ I →
      0 ≤ σ.order q w I s ∧
      0 ≤ σ.priceAfter q w I s (σ.order q w I s) ∧
      ∀ Q' p' : ℝ, 0 ≤ Q' → 0 ≤ p' →
        P.stepOnePayoff q w (P.alpha s) (I + Qbar) Q' p' ≤
          P.stepOnePayoff q w (P.alpha s) (I + Qbar) (σ.order q w I s)
            (σ.priceAfter q w I s (σ.order q w I s)) := by
    intro I s hI
    obtain ⟨hQo0, hQo_opt⟩ := hσ.2.2 q w I s hq.le hw_pos.le hI
    obtain ⟨hm0, hmQ⟩ := hmade_bds I s (σ.order q w I s) hI
    obtain ⟨hp0, _⟩ := hσ.1 q w I s (σ.order q w I s) (σ.made q w I s (σ.order q w I s))
      hq.le hw_pos.le hI hQo0 hm0 hmQ
    refine ⟨hQo0, hp0, fun Q' p' hQ' hp' => ?_⟩
    obtain ⟨hm'0, hm'Q⟩ := hmade_bds I s Q' hI
    obtain ⟨_, hp'_opt⟩ := hσ.1 q w I s Q' (σ.made q w I s Q') hq.le hw_pos.le hI hQ' hm'0 hm'Q
    have hrec_made : received I Q' (σ.made q w I s Q') = σ.recv q w I s Q' := by
      unfold Profile.made Profile.recv received inSeason
      rcases le_or_gt Q' I with h1 | h1
      · rw [if_pos h1, if_pos h1]
      · rw [if_neg (not_le_of_gt h1), if_neg (not_le_of_gt h1), if_neg (not_le_of_gt h1)]
    have hrec' : σ.recv q w I s Q' = min Q' (I + Qbar) := (hrecv_Imade I s Q' hI).1
    have hrec_o : σ.recv q w I s (σ.order q w I s) = min (σ.order q w I s) (I + Qbar) :=
      (hrecv_Imade I s (σ.order q w I s) hI).1
    have h1 : P.stepOnePayoff q w (P.alpha s) (I + Qbar) Q' p' ≤ σ.orderValue P q w I s Q' := by
      unfold Params.stepOnePayoff Profile.orderValue Params.retailerState Profile.priceAfter
      rw [← hrec', ← hrec_made]
      have := hp'_opt p' hp'
      unfold Params.retailerState at this
      exact this
    have h2 := hQo_opt Q' hQ'
    have h3 : σ.orderValue P q w I s (σ.order q w I s) =
        P.stepOnePayoff q w (P.alpha s) (I + Qbar) (σ.order q w I s)
          (σ.priceAfter q w I s (σ.order q w I s)) := by
      unfold Profile.orderValue Params.retailerState Params.stepOnePayoff
      rw [hrec_o]
    linarith
  have hmin_eq_of_pay : ∀ θ α S R : ℝ, 0 ≤ α → 0 ≤ R → R ≤ S → w < θ →
      (θ - w) * min α S ≤ θ * min α R - w * R → R = min α S := by
    intro θ α S R _hα0 _hR0 hRS hwθ hge
    have hwθ0 : 0 < θ - w := sub_pos.mpr hwθ
    rcases lt_trichotomy R (min α S) with hlt | heq | hgt
    · exfalso
      have hαR : min α R = R := min_eq_right (le_trans hlt.le (min_le_left α S))
      rw [hαR] at hge
      have := mul_lt_mul_of_pos_left hlt hwθ0
      linarith
    · exact heq
    · exfalso
      have hα_le_S : α ≤ S := by
        by_contra hc
        have hgt_S : S < α := lt_of_not_ge hc
        rw [min_eq_right hgt_S.le] at hgt
        linarith
      have hminS : min α S = α := min_eq_left hα_le_S
      rw [hminS] at hgt hge
      rw [min_eq_left hgt.le] at hge
      have := mul_lt_mul_of_pos_left hgt hw_pos
      linarith
  have hR_good : ∀ I : ℝ, 0 ≤ I →
      σ.recv q w I .good (σ.order q w I .good) = min P.αg (I + Qbar) := by
    intro I hI
    obtain ⟨hQo0, hp0, hopt⟩ := hstep_opt I .good hI
    have hS_pos : 0 < I + Qbar := by linarith
    have hS0 : 0 ≤ I + Qbar := hS_pos.le
    have hrule := retailer_stage_rule P hStand q w (I + Qbar) hq hw_pos.le hwH hS0
    have hp_eq : σ.priceAfter q w I .good (σ.order q w I .good) = q * P.θH :=
      hrule.2.1 hS_pos _ _ hQo0 hp0 hopt
    let R := min (σ.order q w I .good) (I + Qbar)
    have hR_eq : σ.recv q w I .good (σ.order q w I .good) = R := (hrecv_Imade I .good _ hI).1
    rw [hR_eq]
    have hQ'0 : 0 ≤ min P.αg (I + Qbar) := le_min hαg0.le hS0
    have hp'0 : 0 ≤ q * P.θH := (lt_trans hw_pos hwH).le
    have hge := hopt (min P.αg (I + Qbar)) (q * P.θH) hQ'0 hp'0
    rw [hp_eq] at hge
    have hqLH : q * P.θL < q * P.θH := mul_lt_mul_of_pos_left hθLH hq
    unfold Params.stepOnePayoff Params.demand Params.alpha at hge
    rw [if_neg (not_le_of_gt hqLH), if_pos (le_refl _), zero_add,
      min_eq_left (min_le_right P.αg (I + Qbar)), min_eq_right (min_le_left P.αg (I + Qbar))] at hge
    exact hmin_eq_of_pay (q * P.θH) P.αg (I + Qbar) R hαg0.le (le_min hQo0 hS0)
      (min_le_right _ _) hwH (by linarith)
  have hR_bad_ge1 : ∀ I : ℝ, 0 ≤ I → 1 ≤ I + Qbar →
      σ.recv q w I .bad (σ.order q w I .bad) = 1 := by
    intro I hI hS1
    obtain ⟨hQo0, hp0, hopt⟩ := hstep_opt I .bad hI
    have hS0 : 0 ≤ I + Qbar := by linarith
    have hrule := retailer_stage_rule P hStand q w (I + Qbar) hq hw_pos.le hwH hS0
    have hmin_ab : min P.αb (I + Qbar) = P.αb := min_eq_left (by linarith)
    have hmin_1 : min (I + Qbar) 1 = 1 := min_eq_right hS1
    have hcmp : (q * P.θH - w) * min P.αb (I + Qbar) < (q * P.θL - w) * min (I + Qbar) 1 := by
      rw [hmin_ab, hmin_1]
      linarith
    have hp_eq : σ.priceAfter q w I .bad (σ.order q w I .bad) = q * P.θL :=
      hrule.2.2.1 hcmp _ _ hQo0 hp0 hopt
    let R := min (σ.order q w I .bad) (I + Qbar)
    have hR_eq : σ.recv q w I .bad (σ.order q w I .bad) = R := (hrecv_Imade I .bad _ hI).1
    rw [hR_eq]
    have hp'0 : 0 ≤ q * P.θL := (lt_trans hw_pos hwL).le
    have hge := hopt 1 (q * P.θL) zero_le_one hp'0
    rw [hp_eq] at hge
    have hqLH : q * P.θL < q * P.θH := mul_lt_mul_of_pos_left hθLH hq
    unfold Params.stepOnePayoff Params.demand Params.alpha at hge
    rw [if_pos (le_refl _), if_pos hqLH.le, sub_add_cancel,
      min_eq_left hS1, min_eq_left (le_refl 1)] at hge
    have hR1 := hmin_eq_of_pay (q * P.θL) 1 (I + Qbar) R zero_le_one (le_min hQo0 hS0)
      (min_le_right _ _) hwL (by rw [min_eq_left hS1]; linarith)
    rwa [min_eq_left hS1] at hR1
  let Vstar : ℝ := P.ρ * ((w - P.cost q) * P.αg) + (1 - P.ρ) * (w - P.cost q)
  have h_in_Icc : ∀ I : ℝ, max 0 (1 - Qbar) ≤ I → I ≤ P.αg →
      σ.supplierValue P q w I = Vstar := by
    intro I hI_lo hI_hi
    have hI0 : 0 ≤ I := le_trans (le_max_left 0 (1 - Qbar)) hI_lo
    have h1_le : 1 ≤ I + Qbar := by
      have := le_trans (le_max_right 0 (1 - Qbar)) hI_lo
      linarith
    have hRg : σ.recv q w I .good (σ.order q w I .good) = P.αg := by
      rw [hR_good I hI0]
      exact min_eq_left (by linarith)
    have hImg : I + σ.made q w I .good (σ.order q w I .good) = P.αg := by
      rw [(hrecv_Imade I .good _ hI0).2, ← (hrecv_Imade I .good _ hI0).1, hRg]
      exact max_eq_right hI_hi
    have hRb : σ.recv q w I .bad (σ.order q w I .bad) = 1 := hR_bad_ge1 I hI0 h1_le
    have hImb : I + σ.made q w I .bad (σ.order q w I .bad) = 1 := by
      rw [(hrecv_Imade I .bad _ hI0).2, ← (hrecv_Imade I .bad _ hI0).1, hRb]
      exact max_eq_right (by linarith)
    unfold Profile.supplierValue Profile.supplierStateValue Params.supplierState Params.prob
    rw [hRg, hImg, hRb, hImb]
    dsimp [Vstar]
    ring
  have h_lt_lo : ∀ I : ℝ, 0 ≤ I → I < 1 - Qbar → σ.supplierValue P q w I < Vstar := by
    intro I hI0 hI_lt
    have hRg := hR_good I hI0
    have hImg : I + σ.made q w I .good (σ.order q w I .good) =
        max I (min P.αg (I + Qbar)) := by
      rw [(hrecv_Imade I .good _ hI0).2, ← (hrecv_Imade I .good _ hI0).1, hRg]
    have hg_le : σ.supplierStateValue P q w I .good ≤ (w - P.cost q) * P.αg := by
      unfold Profile.supplierStateValue Params.supplierState
      rw [hRg, hImg]
      have h1 : P.cost q * min P.αg (I + Qbar) ≤ P.cost q * max I (min P.αg (I + Qbar)) :=
        mul_le_mul_of_nonneg_left (le_max_right _ _) hc_pos.le
      have h2 : (w - P.cost q) * min P.αg (I + Qbar) ≤ (w - P.cost q) * P.αg :=
        mul_le_mul_of_nonneg_left (min_le_left _ _) hwc_pos.le
      linarith
    let Rb := min (σ.order q w I .bad) (I + Qbar)
    have hRb_eq : σ.recv q w I .bad (σ.order q w I .bad) = Rb := (hrecv_Imade I .bad _ hI0).1
    have hImb_eq : I + σ.made q w I .bad (σ.order q w I .bad) = max I Rb :=
      (hrecv_Imade I .bad _ hI0).2
    have hb_lt : σ.supplierStateValue P q w I .bad < w - P.cost q := by
      unfold Profile.supplierStateValue Params.supplierState
      rw [hRb_eq, hImb_eq]
      have hRb_lt1 : Rb < 1 := lt_of_le_of_lt (min_le_right _ _) (by linarith)
      have h1 : P.cost q * Rb ≤ P.cost q * max I Rb :=
        mul_le_mul_of_nonneg_left (le_max_right _ _) hc_pos.le
      have h2 : (w - P.cost q) * Rb < (w - P.cost q) * 1 :=
        mul_lt_mul_of_pos_left hRb_lt1 hwc_pos
      linarith
    unfold Profile.supplierValue Params.prob
    have h1 : P.ρ * σ.supplierStateValue P q w I .good ≤ P.ρ * ((w - P.cost q) * P.αg) :=
      mul_le_mul_of_nonneg_left hg_le hρ0.le
    have h2 : (1 - P.ρ) * σ.supplierStateValue P q w I .bad < (1 - P.ρ) * (w - P.cost q) :=
      mul_lt_mul_of_pos_left hb_lt (sub_pos.mpr hρ1)
    dsimp [Vstar]
    linarith
  have h_gt_hi : ∀ I : ℝ, P.αg < I → σ.supplierValue P q w I < Vstar := by
    intro I hI_gt
    have hI0 : 0 ≤ I := (lt_trans hαg0 hI_gt).le
    have h1_le : 1 ≤ I + Qbar := by linarith
    have hRg : σ.recv q w I .good (σ.order q w I .good) = P.αg := by
      rw [hR_good I hI0]
      exact min_eq_left (by linarith)
    have hImg : I + σ.made q w I .good (σ.order q w I .good) = I := by
      rw [(hrecv_Imade I .good _ hI0).2, ← (hrecv_Imade I .good _ hI0).1, hRg]
      exact max_eq_left hI_gt.le
    have hg_lt : σ.supplierStateValue P q w I .good < (w - P.cost q) * P.αg := by
      unfold Profile.supplierStateValue Params.supplierState
      rw [hRg, hImg]
      have := mul_lt_mul_of_pos_left hI_gt hc_pos
      linarith
    have hRb : σ.recv q w I .bad (σ.order q w I .bad) = 1 := hR_bad_ge1 I hI0 h1_le
    have hImb : I + σ.made q w I .bad (σ.order q w I .bad) = max I 1 := by
      rw [(hrecv_Imade I .bad _ hI0).2, ← (hrecv_Imade I .bad _ hI0).1, hRb]
    have hb_le : σ.supplierStateValue P q w I .bad ≤ w - P.cost q := by
      unfold Profile.supplierStateValue Params.supplierState
      rw [hRb, hImb]
      have := mul_le_mul_of_nonneg_left (le_max_right I 1) hc_pos.le
      linarith
    unfold Profile.supplierValue Params.prob
    have h1 : P.ρ * σ.supplierStateValue P q w I .good < P.ρ * ((w - P.cost q) * P.αg) :=
      mul_lt_mul_of_pos_left hg_lt hρ0
    have h2 : (1 - P.ρ) * σ.supplierStateValue P q w I .bad ≤ (1 - P.ρ) * (w - P.cost q) :=
      mul_le_mul_of_nonneg_left hb_le (sub_pos.mpr hρ1).le
    dsimp [Vstar]
    linarith
  have h_le_all : ∀ I' : ℝ, 0 ≤ I' → σ.supplierValue P q w I' ≤ Vstar := by
    intro I' hI'0
    rcases lt_or_ge I' (1 - Qbar) with hlo | hlo
    · exact (h_lt_lo I' hI'0 hlo).le
    · rcases le_or_gt I' P.αg with hhi | hhi
      · exact (h_in_Icc I' (max_le hI'0 hlo) hhi).le
      · exact (h_gt_hi I' hhi).le
  ext I
  simp only [Set.mem_ofPred_eq, Set.mem_Icc]
  constructor
  · rintro ⟨hI0, hopt⟩
    have hαg_lo : max 0 (1 - Qbar) ≤ P.αg := max_le hαg0.le (by linarith)
    have hV_le : Vstar ≤ σ.supplierValue P q w I := by
      rw [← h_in_Icc P.αg hαg_lo (le_refl _)]
      exact hopt P.αg hαg0.le
    refine ⟨max_le hI0 ?_, ?_⟩
    · by_contra hc
      have hlt_c : I < 1 - Qbar := lt_of_not_ge hc
      have := h_lt_lo I hI0 hlt_c
      linarith
    · by_contra hc
      have hgt_c : P.αg < I := lt_of_not_ge hc
      have := h_gt_hi I hgt_c
      linarith
  · rintro ⟨hlo, hhi⟩
    have hI0 : 0 ≤ I := le_trans (le_max_left 0 (1 - Qbar)) hlo
    refine ⟨hI0, fun I' hI'0 => ?_⟩
    rw [h_in_Icc I hlo hhi]
    exact h_le_all I' hI'0
