-- Prove2me | solution 1 for ReactiveCapacity.table_B
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-12T05:04:16.111203+00:00
-- url     : https://prove2.me/submissions/cf455a49-60b9-4bb5-b7d6-db6d2dbd6389

import Mathlib
import Definitions.Def_ReactiveCapacity_Model
import Definitions.Def_ReactiveCapacity_Game
import Definitions.Def_ReactiveCapacity_ClosedForms
import Theorems.Thm_ReactiveCapacity_retailer_stage_rule
import Theorems.Thm_ReactiveCapacity_supplier_response_medium
import Theorems.Thm_ReactiveCapacity_supplier_response_high
import Theorems.Thm_ReactiveCapacity_table_C

open ReactiveCapacity

private noncomputable def argmaxList_tb (f : ℝ → ℝ) : List ℝ → ℝ
  | [] => 0
  | [x] => x
  | x :: y :: xs =>
      let m := argmaxList_tb f (y :: xs)
      if f m ≤ f x then x else m

private lemma argmaxList_tb_mem {f : ℝ → ℝ} :
    ∀ {l : List ℝ}, l ≠ [] → argmaxList_tb f l ∈ l
  | [], h => absurd rfl h
  | [x], _ => by simp [argmaxList_tb]
  | x :: y :: xs, _ => by
      simp only [argmaxList_tb]
      split_ifs
      · simp
      · exact List.mem_cons_of_mem x (argmaxList_tb_mem (List.cons_ne_nil y xs))

private lemma argmaxList_tb_le {f : ℝ → ℝ} :
    ∀ {l : List ℝ} {z : ℝ}, z ∈ l → f z ≤ f (argmaxList_tb f l)
  | [], _, hz => by cases hz
  | [x], z, hz => by
      simp only [List.mem_singleton] at hz
      subst hz
      exact le_refl _
  | x :: y :: xs, z, hz => by
      simp only [argmaxList_tb]
      rcases List.mem_cons.mp hz with rfl | hzy
      · split_ifs with h
        · exact le_refl _
        · exact le_of_lt (lt_of_not_ge h)
      · have ih := argmaxList_tb_le (f := f) hzy
        split_ifs with h
        · exact le_trans ih h
        · exact ih

private lemma argmaxList_tb_head {f : ℝ → ℝ} {x : ℝ} :
    ∀ {xs : List ℝ}, (∀ z ∈ xs, f z ≤ f x) → argmaxList_tb f (x :: xs) = x
  | [], _ => rfl
  | y :: ys, h => by
      simp only [argmaxList_tb]
      have hm := argmaxList_tb_mem (f := f) (List.cons_ne_nil y ys)
      rw [if_pos (h _ hm)]

private lemma affine_le_max_tb {a b x m c fa fb : ℝ} (hab : a ≤ x) (hxb : x ≤ b)
    (ha : m * a + c ≤ fa) (hb : m * b + c ≤ fb) : m * x + c ≤ max fa fb := by
  rcases le_or_gt 0 m with hm | hm
  · exact le_trans (by have := mul_le_mul_of_nonneg_left hxb hm; linarith) (le_max_right fa fb)
  · exact le_trans (by have := mul_le_mul_of_nonpos_left hab hm.le; linarith) (le_max_left fa fb)

private noncomputable def basePost_tb (P : Params) (Qbar : ℝ) : Profile where
  q := 0
  w := 0
  inv := fun _ _ => 0
  order := fun q w I s =>
    let S := if P.cost q ≤ w then I + Qbar else I
    let α := P.alpha s
    let vH := (q * P.θH - w) * min α S
    let vL := (q * P.θL - w) * min 1 S
    if max vH vL ≤ 0 then 0
    else if vH ≤ vL then min 1 S else min α S
  react := fun q w I _s Q =>
    if P.cost q ≤ w then min Qbar (max 0 (Q - I)) else 0
  price := fun q _w I s Q I' =>
    let R := received I Q I'
    let α := P.alpha s
    if (q * P.θL) * min 1 R ≤ (q * P.θH) * min α R then q * P.θH else q * P.θL

private noncomputable def candList_tb (P : Params) (Qbar q w : ℝ) : List ℝ :=
  [P.αg, max 0 (1 - Qbar), 0, P.αb, max P.αb (P.αg - Qbar),
    max 0 ((q * P.θH - w) * P.αb / (q * P.θL - w) - Qbar)]

private noncomputable def fullProfile_tb (P : Params) (Qbar q0 w0 I_pref : ℝ) : Profile :=
  { basePost_tb P Qbar with
    q := q0
    w := w0
    inv := fun q w =>
      argmaxList_tb (fun I => (basePost_tb P Qbar).supplierValue P q w I)
        (I_pref :: candList_tb P Qbar q w) }

private lemma isPostSPE_full_tb (P : Params) (hStand : P.Standing) (Qbar : ℝ) (hQ0 : 0 ≤ Qbar)
    (q0 w0 I_pref : ℝ) : IsPostInventorySPE P Qbar (fullProfile_tb P Qbar q0 w0 I_pref) := by
  rcases hStand with ⟨hθL, hθLH, hk, _hρ0, _hρ1, hαb0, hαb_lt, hαg_gt, hαg1⟩
  have hθH : 0 < P.θH := lt_trans hθL hθLH
  have hαg0 : 0 < P.αg := pos_of_mul_pos_left (lt_trans hθL hαg_gt) hθH.le
  have hα_bds : ∀ s : State, 0 < P.alpha s ∧ P.alpha s < 1 := by
    rintro (_ | _)
    · exact ⟨hαg0, hαg1⟩
    · refine ⟨hαb0, ?_⟩
      by_contra hc
      have hge : 1 ≤ P.αb := le_of_not_gt hc
      have := mul_le_mul_of_nonneg_right hge hθH.le
      linarith
  have hrecv_nonneg : ∀ I Q I' : ℝ, 0 ≤ I → 0 ≤ Q → 0 ≤ I' → 0 ≤ received I Q I' := by
    intro I Q I' hI hQ hI'
    unfold received
    split_ifs
    · exact hQ
    · exact le_min (add_nonneg hI hI') hQ
  have hrev_price : ∀ q : ℝ, ∀ s : State, ∀ R : ℝ, 0 ≤ q → 0 ≤ R →
      let p0 := if (q * P.θL) * min 1 R ≤ (q * P.θH) * min (P.alpha s) R then q * P.θH else q * P.θL
      0 ≤ p0 ∧
      p0 * min (P.demand q (P.alpha s) p0) R =
        max ((q * P.θH) * min (P.alpha s) R) ((q * P.θL) * min 1 R) ∧
      ∀ p : ℝ, 0 ≤ p →
        p * min (P.demand q (P.alpha s) p) R ≤
          max ((q * P.θH) * min (P.alpha s) R) ((q * P.θL) * min 1 R) := by
    intro q s R hq hR
    obtain ⟨hα0, _hα1⟩ := hα_bds s
    dsimp only
    have hp0_nonneg : 0 ≤ (if (q * P.θL) * min 1 R ≤ (q * P.θH) * min (P.alpha s) R
        then q * P.θH else q * P.θL) := by
      split_ifs <;> exact mul_nonneg hq (by linarith)
    have hval_p0 : (let p0 := if (q * P.θL) * min 1 R ≤ (q * P.θH) * min (P.alpha s) R
          then q * P.θH else q * P.θL
        p0 * min (P.demand q (P.alpha s) p0) R) =
        max ((q * P.θH) * min (P.alpha s) R) ((q * P.θL) * min 1 R) := by
      rcases eq_or_lt_of_le hq with rfl | hq_pos
      · simp
      · have hqLH : q * P.θL < q * P.θH := mul_lt_mul_of_pos_left hθLH hq_pos
        dsimp only
        split_ifs with hcmp
        · unfold Params.demand
          rw [if_neg (not_le_of_gt hqLH), if_pos (le_refl _), zero_add, max_eq_left hcmp]
        · unfold Params.demand
          rw [if_pos (le_refl _), if_pos hqLH.le, sub_add_cancel, max_eq_right (le_of_not_ge hcmp)]
    refine ⟨hp0_nonneg, hval_p0, fun p _hp => ?_⟩
    unfold Params.demand
    rcases le_or_gt p (q * P.θL) with hpL | hpL
    · have hpH : p ≤ q * P.θH := le_trans hpL (mul_le_mul_of_nonneg_left hθLH.le hq)
      rw [if_pos hpL, if_pos hpH, sub_add_cancel]
      exact le_trans (mul_le_mul_of_nonneg_right hpL (le_min zero_le_one hR)) (le_max_right _ _)
    · rcases le_or_gt p (q * P.θH) with hpH | hpH
      · rw [if_neg (not_le_of_gt hpL), if_pos hpH, zero_add]
        exact le_trans (mul_le_mul_of_nonneg_right hpH (le_min hα0.le hR)) (le_max_left _ _)
      · rw [if_neg (not_le_of_gt hpL), if_neg (not_le_of_gt hpH), add_zero,
          min_eq_left hR, mul_zero]
        exact le_trans (mul_nonneg (mul_nonneg hq hθL.le) (le_min zero_le_one hR)) (le_max_right _ _)
  have hrecv_full : ∀ q w I : ℝ, ∀ s : State, ∀ Q : ℝ, 0 ≤ I → 0 ≤ Q →
      (fullProfile_tb P Qbar q0 w0 I_pref).recv q w I s Q =
        min Q (if P.cost q ≤ w then I + Qbar else I) ∧
      0 ≤ (fullProfile_tb P Qbar q0 w0 I_pref).made q w I s Q ∧
      (fullProfile_tb P Qbar q0 w0 I_pref).made q w I s Q ≤ Qbar := by
    intro q w I s Q _hI _hQ
    change received I Q (if P.cost q ≤ w then min Qbar (max 0 (Q - I)) else 0) =
        min Q (if P.cost q ≤ w then I + Qbar else I) ∧
      0 ≤ inSeason I Q (if P.cost q ≤ w then min Qbar (max 0 (Q - I)) else 0) ∧
      inSeason I Q (if P.cost q ≤ w then min Qbar (max 0 (Q - I)) else 0) ≤ Qbar
    unfold received inSeason
    rcases le_or_gt Q I with hQI | hIQ
    · rw [if_pos hQI, if_pos hQI]
      refine ⟨?_, le_refl 0, hQ0⟩
      split_ifs
      · exact (min_eq_left (by linarith)).symm
      · exact (min_eq_left hQI).symm
    · rw [if_neg (not_le_of_gt hIQ), if_neg (not_le_of_gt hIQ)]
      split_ifs with hcw
      · rw [max_eq_right (sub_pos.mpr hIQ).le]
        refine ⟨?_, le_min hQ0 (sub_pos.mpr hIQ).le, min_le_left _ _⟩
        rcases le_or_gt Qbar (Q - I) with h1 | h1
        · rw [min_eq_left h1, min_eq_left (by linarith), min_eq_right (by linarith)]
        · rw [min_eq_right h1.le, show I + (Q - I) = Q by ring, min_self,
            min_eq_left (by linarith)]
      · rw [add_zero, min_comm I Q]
        exact ⟨rfl, le_refl 0, hQ0⟩
  refine ⟨?_, ?_, ?_⟩
  · intro q w I s Q I' hq _hw hI hQ hI'0 _hI'Q
    have hR0 := hrecv_nonneg I Q I' hI hQ hI'0
    obtain ⟨hp0, hval0, hmax⟩ := hrev_price q s (received I Q I') hq hR0
    refine ⟨hp0, fun p hp => ?_⟩
    have hpr : (fullProfile_tb P Qbar q0 w0 I_pref).price q w I s Q I' =
        if (q * P.θL) * min 1 (received I Q I') ≤ (q * P.θH) * min (P.alpha s) (received I Q I')
        then q * P.θH else q * P.θL := rfl
    unfold Params.retailerState
    rw [hpr, hval0]
    have := hmax p hp
    linarith
  · intro q w I s Q _hq _hw _hI hIQ
    have hre : (fullProfile_tb P Qbar q0 w0 I_pref).react q w I s Q =
        if P.cost q ≤ w then min Qbar (max 0 (Q - I)) else 0 := rfl
    rw [hre]
    split_ifs with hcw
    · rw [max_eq_right (sub_pos.mpr hIQ).le]
      let Is := min Qbar (Q - I)
      refine ⟨le_min hQ0 (sub_pos.mpr hIQ).le, min_le_left _ _, fun I' _hI'0 _hI'Q => ?_⟩
      change P.supplierState q w I (received I Q I') I' ≤
        P.supplierState q w I (received I Q Is) Is
      unfold Params.supplierState received
      simp only [if_neg (not_le_of_gt hIQ)]
      have hIIs : I + Is ≤ Q := by
        have := min_le_right Qbar (Q - I)
        dsimp [Is]
        linarith
      rw [min_eq_left hIIs]
      rcases le_or_gt I' Is with hle | hgt
      · rw [min_eq_left (by linarith)]
        have := mul_le_mul_of_nonneg_left (by linarith : I + I' ≤ I + Is) (sub_nonneg.mpr hcw)
        linarith
      · have hIs_eq : Is = Q - I := by
          dsimp [Is] at hgt ⊢
          rcases le_or_gt Qbar (Q - I) with h1 | h1
          · exfalso
            rw [min_eq_left h1] at hgt
            linarith
          · exact min_eq_right h1.le
        rw [hIs_eq] at hgt ⊢
        rw [min_eq_right (by linarith : Q ≤ I + I'), show I + (Q - I) = Q by ring]
        have hc0 : 0 ≤ P.cost q := mul_nonneg hk.le (sq_nonneg q)
        have := mul_le_mul_of_nonneg_left (by linarith : Q ≤ I + I') hc0
        linarith
    · have hw_lt : w < P.cost q := lt_of_not_ge hcw
      refine ⟨le_refl 0, hQ0, fun I' hI'0 _hI'Q => ?_⟩
      unfold Params.supplierState received
      simp only [if_neg (not_le_of_gt hIQ), add_zero, min_eq_left hIQ.le]
      have h1 : I ≤ min (I + I') Q := le_min (by linarith) hIQ.le
      have h2 : min (I + I') Q ≤ I + I' := min_le_left _ _
      have hc0 : 0 ≤ P.cost q := mul_nonneg hk.le (sq_nonneg q)
      have h3 : (w - P.cost q) * (min (I + I') Q - I) ≤ 0 :=
        mul_nonpos_of_nonpos_of_nonneg (by linarith) (by linarith)
      have h4 : 0 ≤ P.cost q * (I + I' - min (I + I') Q) :=
        mul_nonneg hc0 (by linarith)
      linarith
  · intro q w I s hq hw hI
    obtain ⟨hα0, _hα1⟩ := hα_bds s
    let S := if P.cost q ≤ w then I + Qbar else I
    have hS0 : 0 ≤ S := by
      dsimp [S]
      split_ifs <;> linarith
    let vH := (q * P.θH - w) * min (P.alpha s) S
    let vL := (q * P.θL - w) * min 1 S
    have hQo_bds : 0 ≤ (fullProfile_tb P Qbar q0 w0 I_pref).order q w I s ∧
        (fullProfile_tb P Qbar q0 w0 I_pref).order q w I s ≤ S := by
      change 0 ≤ (if max vH vL ≤ 0 then 0 else if vH ≤ vL then min 1 S else min (P.alpha s) S) ∧
        (if max vH vL ≤ 0 then 0 else if vH ≤ vL then min 1 S else min (P.alpha s) S) ≤ S
      split_ifs
      · exact ⟨le_refl 0, hS0⟩
      · exact ⟨le_min zero_le_one hS0, min_le_right 1 S⟩
      · exact ⟨le_min hα0.le hS0, min_le_right (P.alpha s) S⟩
    refine ⟨hQo_bds.1, fun Q hQ => ?_⟩
    have hov_eq : ∀ Q1 : ℝ, 0 ≤ Q1 →
        (fullProfile_tb P Qbar q0 w0 I_pref).orderValue P q w I s Q1 =
          let R := min Q1 S
          max ((q * P.θH) * min (P.alpha s) R) ((q * P.θL) * min 1 R) - w * R := by
      intro Q1 hQ1
      obtain ⟨hrec, _hm0, _hmQ⟩ := hrecv_full q w I s Q1 hI hQ1
      have hrecS : (fullProfile_tb P Qbar q0 w0 I_pref).recv q w I s Q1 = min Q1 S := hrec
      have hR0 : 0 ≤ min Q1 S := le_min hQ1 hS0
      obtain ⟨_, hval0, _⟩ := hrev_price q s (min Q1 S) hq hR0
      dsimp only at hval0 ⊢
      have hrec2 : received I Q1 ((fullProfile_tb P Qbar q0 w0 I_pref).made q w I s Q1) = min Q1 S := by
        have h1 := hrecS
        unfold Profile.recv received at h1
        unfold Profile.made inSeason received
        rcases le_or_gt Q1 I with hQI | hIQ
        · rw [if_pos hQI] at h1 ⊢; exact h1
        · rw [if_neg (not_le_of_gt hIQ), if_neg (not_le_of_gt hIQ)]; rw [if_neg (not_le_of_gt hIQ)] at h1; exact h1
      have hp_eq : (fullProfile_tb P Qbar q0 w0 I_pref).priceAfter q w I s Q1 =
          if (q * P.θL) * min 1 (min Q1 S) ≤ (q * P.θH) * min (P.alpha s) (min Q1 S)
          then q * P.θH else q * P.θL := by
        change (let R := received I Q1 ((fullProfile_tb P Qbar q0 w0 I_pref).made q w I s Q1)
          if (q * P.θL) * min 1 R ≤ (q * P.θH) * min (P.alpha s) R then q * P.θH else q * P.θL) = _
        dsimp only
        rw [hrec2]
      unfold Profile.orderValue Params.retailerState
      rw [hrecS, hp_eq, hval0]
    rw [hov_eq Q hQ, hov_eq _ hQo_bds.1]
    dsimp only
    rw [min_eq_left hQo_bds.2]
    let R := min Q S
    have hR0 : 0 ≤ R := le_min hQ hS0
    have hRS : R ≤ S := min_le_right Q S
    have hub_Q : max ((q * P.θH) * min (P.alpha s) R) ((q * P.θL) * min 1 R) - w * R ≤
        max (max vH vL) 0 := by
      have h1 : (q * P.θH) * min (P.alpha s) R - w * R ≤ max vH 0 := by
        have hm_le : min (P.alpha s) R ≤ R := min_le_right _ _
        have hm0 : 0 ≤ min (P.alpha s) R := le_min hα0.le hR0
        have hw_le : w * min (P.alpha s) R ≤ w * R := mul_le_mul_of_nonneg_left hm_le hw
        rcases le_or_gt 0 (q * P.θH - w) with hpos | hneg
        · have := mul_le_mul_of_nonneg_left (min_le_min_left (P.alpha s) hRS) hpos
          exact le_trans (by linarith) (le_max_left vH 0)
        · have := mul_nonpos_of_nonpos_of_nonneg hneg.le hm0
          exact le_trans (by linarith) (le_max_right vH 0)
      have h2 : (q * P.θL) * min 1 R - w * R ≤ max vL 0 := by
        have hm_le : min 1 R ≤ R := min_le_right _ _
        have hm0 : 0 ≤ min 1 R := le_min zero_le_one hR0
        have hw_le : w * min 1 R ≤ w * R := mul_le_mul_of_nonneg_left hm_le hw
        rcases le_or_gt 0 (q * P.θL - w) with hpos | hneg
        · have := mul_le_mul_of_nonneg_left (min_le_min_left 1 hRS) hpos
          exact le_trans (by linarith) (le_max_left vL 0)
        · have := mul_nonpos_of_nonpos_of_nonneg hneg.le hm0
          exact le_trans (by linarith) (le_max_right vL 0)
      rcases max_choice ((q * P.θH) * min (P.alpha s) R) ((q * P.θL) * min 1 R) with hH | hL
      · rw [hH]
        exact le_trans h1 (max_le (le_trans (le_max_left vH vL) (le_max_left _ 0)) (le_max_right _ 0))
      · rw [hL]
        exact le_trans h2 (max_le (le_trans (le_max_right vH vL) (le_max_left _ 0)) (le_max_right _ 0))
    have hatt : max (max vH vL) 0 ≤
        max ((q * P.θH) * min (P.alpha s) ((fullProfile_tb P Qbar q0 w0 I_pref).order q w I s))
          ((q * P.θL) * min 1 ((fullProfile_tb P Qbar q0 w0 I_pref).order q w I s)) -
        w * (fullProfile_tb P Qbar q0 w0 I_pref).order q w I s := by
      change max (max vH vL) 0 ≤
        (let r0 := if max vH vL ≤ 0 then 0 else if vH ≤ vL then min 1 S else min (P.alpha s) S
         max ((q * P.θH) * min (P.alpha s) r0) ((q * P.θL) * min 1 r0) - w * r0)
      dsimp only
      split_ifs with h0 hHL
      · rw [max_eq_right h0]
        simp
      · have h0' : 0 < max vH vL := lt_of_not_ge h0
        rw [max_eq_left h0'.le, max_eq_right hHL, min_eq_right (min_le_left 1 S)]
        have h2 := le_max_right ((q * P.θH) * min (P.alpha s) (min 1 S)) ((q * P.θL) * min 1 S)
        dsimp [vL]
        linarith
      · have h0' : 0 < max vH vL := lt_of_not_ge h0
        have hHL' : vL < vH := lt_of_not_ge hHL
        rw [max_eq_left h0'.le, max_eq_left hHL'.le, min_eq_right (min_le_left (P.alpha s) S)]
        have h1 := le_max_left ((q * P.θH) * min (P.alpha s) S)
          ((q * P.θL) * min 1 (min (P.alpha s) S))
        dsimp [vH]
        linarith
    exact le_trans hub_Q hatt

private lemma isInvSPE_full_tb (P : Params) (hStand : P.Standing) (Qbar : ℝ) (hQ0 : 0 ≤ Qbar)
    (q0 w0 I_pref : ℝ) (hIp : 0 ≤ I_pref) :
    ∀ q w : ℝ, 0 ≤ q → 0 ≤ w →
      0 ≤ (fullProfile_tb P Qbar q0 w0 I_pref).inv q w ∧
      ∀ I : ℝ, 0 ≤ I →
        (fullProfile_tb P Qbar q0 w0 I_pref).supplierValue P q w I ≤
          (fullProfile_tb P Qbar q0 w0 I_pref).supplierValue P q w
            ((fullProfile_tb P Qbar q0 w0 I_pref).inv q w) := by
  rcases hStand with ⟨hθL, hθLH, hk, hρ0, hρ1, hαb0, hαb_lt, hαg_gt, hαg1⟩
  have hθH : 0 < P.θH := lt_trans hθL hθLH
  have hαg0 : 0 < P.αg := pos_of_mul_pos_left (lt_trans hθL hαg_gt) hθH.le
  have hαb_αg : P.αb < P.αg := lt_of_mul_lt_mul_right (lt_trans hαb_lt hαg_gt) hθH.le
  have hpost0 := isPostSPE_full_tb P ⟨hθL, hθLH, hk, hρ0, hρ1, hαb0, hαb_lt, hαg_gt, hαg1⟩
    Qbar hQ0 0 0 0
  intro q w hq hw
  let sv := fun I => (basePost_tb P Qbar).supplierValue P q w I
  let l := I_pref :: candList_tb P Qbar q w
  have hl_ne : l ≠ [] := List.cons_ne_nil _ _
  have hl_nonneg : ∀ z ∈ l, 0 ≤ z := by
    intro z hz
    simp only [l, candList_tb, List.mem_cons, List.not_mem_nil, or_false] at hz
    rcases hz with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact hIp
    · exact hαg0.le
    · exact le_max_left _ _
    · exact le_refl 0
    · exact hαb0.le
    · exact le_trans hαb0.le (le_max_left _ _)
    · exact le_max_left _ _
  have hinv_0 : 0 ≤ (fullProfile_tb P Qbar q0 w0 I_pref).inv q w :=
    hl_nonneg _ (argmaxList_tb_mem hl_ne)
  refine ⟨hinv_0, fun I hI => ?_⟩
  suffices hdom : ∃ z ∈ candList_tb P Qbar q w, sv I ≤ sv z by
    rcases hdom with ⟨z, hz, hle⟩
    exact le_trans hle (argmaxList_tb_le (List.mem_cons_of_mem I_pref hz))
  have hQo_0 : ∀ J : ℝ, ∀ s : State, 0 ≤ J → 0 ≤ (basePost_tb P Qbar).order q w J s :=
    fun J s hJ => (hpost0.2.2 q w J s hq hw hJ).1
  have hrm_cw : P.cost q ≤ w → ∀ J : ℝ, ∀ s : State, 0 ≤ J →
      (basePost_tb P Qbar).recv q w J s ((basePost_tb P Qbar).order q w J s) =
        min ((basePost_tb P Qbar).order q w J s) (J + Qbar) ∧
      J + (basePost_tb P Qbar).made q w J s ((basePost_tb P Qbar).order q w J s) =
        max J (min ((basePost_tb P Qbar).order q w J s) (J + Qbar)) := by
    intro hcw J s _hJ
    let Q := (basePost_tb P Qbar).order q w J s
    have hre : (basePost_tb P Qbar).react q w J s Q = min Qbar (max 0 (Q - J)) := by
      change (if P.cost q ≤ w then min Qbar (max 0 (Q - J)) else 0) = _
      rw [if_pos hcw]
    change received J Q ((basePost_tb P Qbar).react q w J s Q) = min Q (J + Qbar) ∧
      J + inSeason J Q ((basePost_tb P Qbar).react q w J s Q) = max J (min Q (J + Qbar))
    rw [hre]
    unfold received inSeason
    rcases le_or_gt Q J with hQJ | hJQ
    · rw [if_pos hQJ, if_pos hQJ, min_eq_left (by linarith), max_eq_left hQJ, add_zero]
      exact ⟨rfl, rfl⟩
    · rw [if_neg (not_le_of_gt hJQ), if_neg (not_le_of_gt hJQ), max_eq_right (sub_pos.mpr hJQ).le]
      have hsum : J + min Qbar (Q - J) = min Q (J + Qbar) := by
        rcases le_or_gt Qbar (Q - J) with h1 | h1
        · rw [min_eq_left h1, min_eq_right (by linarith)]
        · rw [min_eq_right h1.le, min_eq_left (by linarith)]
          ring
      rw [hsum, min_eq_left (min_le_left Q (J + Qbar)), max_eq_right (le_min hJQ.le (by linarith))]
      exact ⟨rfl, rfl⟩
  by_cases hcase : P.cost q ≤ w ∧ 0 < q ∧ w < q * P.θH
  · rcases hcase with ⟨hcw, hq_pos, hwH⟩
    have hc0 : 0 < P.cost q := mul_pos hk (pow_pos hq_pos 2)
    have hwc0 : 0 ≤ w - P.cost q := sub_nonneg.mpr hcw
    have hwH0 : 0 < q * P.θH - w := sub_pos.mpr hwH
    have hgood_R : ∀ J : ℝ, 0 ≤ J →
        (basePost_tb P Qbar).recv q w J .good ((basePost_tb P Qbar).order q w J .good) =
          min P.αg (J + Qbar) := by
      intro J hJ
      have hrm := hrm_cw hcw J .good hJ
      rw [hrm.1]
      unfold basePost_tb
      dsimp only
      rw [if_pos hcw]
      change min (if max ((q * P.θH - w) * min P.αg (J + Qbar))
            ((q * P.θL - w) * min 1 (J + Qbar)) ≤ 0 then 0
          else if (q * P.θH - w) * min P.αg (J + Qbar) ≤ (q * P.θL - w) * min 1 (J + Qbar)
          then min 1 (J + Qbar) else min P.αg (J + Qbar)) (J + Qbar) = min P.αg (J + Qbar)
      rcases eq_or_lt_of_le (add_nonneg hJ hQ0) with hS0 | hS_pos
      · rw [← hS0]
        simp [min_eq_right hαg0.le]
      · have hvH_pos : 0 < (q * P.θH - w) * min P.αg (J + Qbar) :=
          mul_pos hwH0 (lt_min hαg0 hS_pos)
        have hvL_lt : (q * P.θL - w) * min 1 (J + Qbar) <
            (q * P.θH - w) * min P.αg (J + Qbar) := by
          rcases le_or_gt (q * P.θL - w) 0 with hL0 | hL_pos
          · exact lt_of_le_of_lt
              (mul_nonpos_of_nonpos_of_nonneg hL0 (le_min zero_le_one hS_pos.le)) hvH_pos
          · rcases le_or_gt (J + Qbar) P.αg with hSα | hSα
            · rw [min_eq_right (le_trans hSα hαg1.le), min_eq_right hSα]
              exact mul_lt_mul_of_pos_right
                (by have := mul_lt_mul_of_pos_left hθLH hq_pos; linarith) hS_pos
            · rw [min_eq_left hSα.le]
              have h1 : (q * P.θL - w) * min 1 (J + Qbar) ≤ q * P.θL - w := by
                have := mul_le_mul_of_nonneg_left (min_le_left 1 (J + Qbar)) hL_pos.le
                linarith
              have h2 : q * P.θL < q * (P.αg * P.θH) := mul_lt_mul_of_pos_left hαg_gt hq_pos
              have h3 : w * P.αg ≤ w := by
                have := mul_le_mul_of_nonneg_left hαg1.le hw
                linarith
              linarith
        rw [if_neg (not_le_of_gt (lt_of_lt_of_le hvH_pos (le_max_left _ _))),
          if_neg (not_le_of_gt hvL_lt), min_eq_left (min_le_right _ _)]
    have hgood_val : ∀ J : ℝ, 0 ≤ J →
        (basePost_tb P Qbar).supplierStateValue P q w J .good =
          w * min P.αg (J + Qbar) - P.cost q * max J (min P.αg (J + Qbar)) := by
      intro J hJ
      have hrm := hrm_cw hcw J .good hJ
      have hRg := hgood_R J hJ
      unfold Profile.supplierStateValue Params.supplierState
      rw [hRg, hrm.2, ← hrm.1, hRg]
    have hbad_R : ∀ J : ℝ, 0 ≤ J →
        ((basePost_tb P Qbar).recv q w J .bad ((basePost_tb P Qbar).order q w J .bad) =
          min P.αb (J + Qbar)) ∨
        (0 < J + Qbar ∧
          (q * P.θH - w) * min P.αb (J + Qbar) ≤ (q * P.θL - w) * min 1 (J + Qbar) ∧
          (basePost_tb P Qbar).recv q w J .bad ((basePost_tb P Qbar).order q w J .bad) =
            min 1 (J + Qbar)) := by
      intro J hJ
      have hrm := hrm_cw hcw J .bad hJ
      rw [hrm.1]
      have hord : (basePost_tb P Qbar).order q w J .bad =
          if max ((q * P.θH - w) * min P.αb (J + Qbar)) ((q * P.θL - w) * min 1 (J + Qbar)) ≤ 0 then 0
          else if (q * P.θH - w) * min P.αb (J + Qbar) ≤ (q * P.θL - w) * min 1 (J + Qbar)
          then min 1 (J + Qbar) else min P.αb (J + Qbar) := by
        unfold basePost_tb
        dsimp only
        rw [if_pos hcw, Params.alpha]
      rw [hord]
      rcases eq_or_lt_of_le (add_nonneg hJ hQ0) with hS0 | hS_pos
      · left
        have hS0' : J + Qbar = 0 := hS0.symm
        rw [hS0', min_eq_right hαb0.le, min_eq_right zero_le_one, mul_zero, mul_zero, max_self,
          if_pos (le_refl 0), min_self]
      · have hvH_pos : 0 < (q * P.θH - w) * min P.αb (J + Qbar) :=
          mul_pos hwH0 (lt_min hαb0 hS_pos)
        rw [if_neg (not_le_of_gt (lt_of_lt_of_le hvH_pos (le_max_left _ _)))]
        split_ifs with hHL
        · right
          exact ⟨hS_pos, hHL, min_eq_left (min_le_right _ _)⟩
        · left
          exact min_eq_left (min_le_right _ _)
    let FH : ℝ → ℝ := fun J =>
      P.ρ * (w * min P.αg (J + Qbar) - P.cost q * max J (min P.αg (J + Qbar))) +
        (1 - P.ρ) * (w * min P.αb (J + Qbar) - P.cost q * max J (min P.αb (J + Qbar)))
    let FL : ℝ → ℝ := fun J =>
      P.ρ * (w * min P.αg (J + Qbar) - P.cost q * max J (min P.αg (J + Qbar))) +
        (1 - P.ρ) * (w * min 1 (J + Qbar) - P.cost q * max J (min 1 (J + Qbar)))
    have hFH_le_sv : ∀ J : ℝ, 0 ≤ J → J ≤ 1 → FH J ≤ sv J := by
      intro J hJ0 hJ1
      dsimp [sv]
      unfold Profile.supplierValue Params.prob
      rw [hgood_val J hJ0]
      have hrm := hrm_cw hcw J .bad hJ0
      rcases hbad_R J hJ0 with hRb | ⟨_, _, hRb⟩
      · unfold Profile.supplierStateValue Params.supplierState
        rw [hRb, hrm.2, ← hrm.1, hRb]
      · unfold Profile.supplierStateValue Params.supplierState
        rw [hRb, hrm.2, ← hrm.1, hRb]
        have hJ_le : J ≤ min 1 (J + Qbar) := le_min hJ1 (by linarith)
        rw [max_eq_right hJ_le]
        have h1 : P.cost q * min P.αb (J + Qbar) ≤ P.cost q * max J (min P.αb (J + Qbar)) :=
          mul_le_mul_of_nonneg_left (le_max_right _ _) hc0.le
        have h2 : min P.αb (J + Qbar) ≤ min 1 (J + Qbar) :=
          min_le_min_right (J + Qbar) (le_trans hαb_αg.le hαg1.le)
        have h3 : (w - P.cost q) * min P.αb (J + Qbar) ≤ (w - P.cost q) * min 1 (J + Qbar) :=
          mul_le_mul_of_nonneg_left h2 hwc0
        have hb : w * min P.αb (J + Qbar) - P.cost q * max J (min P.αb (J + Qbar)) ≤
            w * min 1 (J + Qbar) - P.cost q * min 1 (J + Qbar) := by linarith
        have := mul_le_mul_of_nonneg_left hb (sub_pos.mpr hρ1).le
        dsimp [FH]
        linarith
    rcases hbad_R I hI with hRb_I | ⟨hS_pos_I, hHL_I, hRb_I⟩
    · have hsv_eq : sv I = FH I := by
        dsimp [sv, FH]
        unfold Profile.supplierValue Params.prob Profile.supplierStateValue Params.supplierState
        have hrm := hrm_cw hcw I .bad hI
        have hgood := hgood_val I hI
        unfold Profile.supplierStateValue Params.supplierState at hgood
        rw [hgood, hRb_I, hrm.2, ← hrm.1, hRb_I]
      rw [hsv_eq]
      rcases le_or_gt I P.αb with hI_ab | hI_ab
      · refine ⟨P.αb, by simp [candList_tb], le_trans ?_ (hFH_le_sv P.αb hαb0.le (by linarith))⟩
        dsimp [FH]
        have hg1 : max I (min P.αg (I + Qbar)) = min P.αg (I + Qbar) :=
          max_eq_right (le_min (by linarith) (by linarith))
        have hg2 : max P.αb (min P.αg (P.αb + Qbar)) = min P.αg (P.αb + Qbar) :=
          max_eq_right (le_min hαb_αg.le (by linarith))
        have hb1 : max I (min P.αb (I + Qbar)) = min P.αb (I + Qbar) :=
          max_eq_right (le_min hI_ab (by linarith))
        have hb2 : min P.αb (P.αb + Qbar) = P.αb := min_eq_left (by linarith)
        rw [hg1, hg2, hb1, hb2, max_self]
        have hmg : (w - P.cost q) * min P.αg (I + Qbar) ≤ (w - P.cost q) * min P.αg (P.αb + Qbar) :=
          mul_le_mul_of_nonneg_left (min_le_min_left P.αg (by linarith)) hwc0
        have hmb : (w - P.cost q) * min P.αb (I + Qbar) ≤ (w - P.cost q) * P.αb :=
          mul_le_mul_of_nonneg_left (min_le_left _ _) hwc0
        have := mul_le_mul_of_nonneg_left (by linarith :
          w * min P.αg (I + Qbar) - P.cost q * min P.αg (I + Qbar) ≤
            w * min P.αg (P.αb + Qbar) - P.cost q * min P.αg (P.αb + Qbar)) hρ0.le
        have := mul_le_mul_of_nonneg_left (by linarith :
          w * min P.αb (I + Qbar) - P.cost q * min P.αb (I + Qbar) ≤
            w * P.αb - P.cost q * P.αb) (sub_pos.mpr hρ1).le
        linarith
      · rcases le_or_gt I P.αg with hI_ag | hI_ag
        · let km := max P.αb (P.αg - Qbar)
          have hkm0 : 0 ≤ km := le_trans hαb0.le (le_max_left _ _)
          have hkm1 : km ≤ 1 := le_trans (max_le hαb_αg.le (by linarith)) hαg1.le
          rcases le_or_gt I km with hI_km | hI_km
          · have hab_lt_sub : P.αb < P.αg - Qbar := by
              by_contra hc
              have hge : P.αg - Qbar ≤ P.αb := le_of_not_gt hc
              have hkm_eq : km = P.αb := max_eq_left hge
              linarith
            have hkm_eq : km = P.αg - Qbar := max_eq_right hab_lt_sub.le
            have h_aff : ∀ J : ℝ, P.αb ≤ J → J ≤ km →
                FH J = (P.ρ * w - P.cost q) * J +
                  (P.ρ * (w - P.cost q) * Qbar + (1 - P.ρ) * w * P.αb) := by
              intro J hJlo hJhi
              have hJQ : J + Qbar ≤ P.αg := by linarith
              dsimp [FH]
              rw [min_eq_right hJQ, max_eq_right (by linarith : J ≤ J + Qbar),
                min_eq_left (by linarith : P.αb ≤ J + Qbar), max_eq_left hJlo]
              ring
            have hle_max : FH I ≤ max (sv P.αb) (sv km) := by
              rw [h_aff I hI_ab.le hI_km]
              refine affine_le_max_tb hI_ab.le hI_km ?_ ?_
              · rw [← h_aff P.αb (le_refl _) (le_max_left _ _)]
                exact hFH_le_sv P.αb hαb0.le (by linarith)
              · rw [← h_aff km (le_max_left _ _) (le_refl _)]
                exact hFH_le_sv km hkm0 hkm1
            rcases max_choice (sv P.αb) (sv km) with h1 | h1
            · rw [h1] at hle_max
              exact ⟨P.αb, by simp [candList_tb], hle_max⟩
            · rw [h1] at hle_max
              exact ⟨km, by simp [km, candList_tb], hle_max⟩
          · refine ⟨km, by simp [km, candList_tb], le_trans ?_ (hFH_le_sv km hkm0 hkm1)⟩
            have h_dec : ∀ J : ℝ, km ≤ J → J ≤ P.αg →
                FH J = P.ρ * (w - P.cost q) * P.αg + (1 - P.ρ) * (w * P.αb - P.cost q * J) := by
              intro J hJlo hJhi
              have h1 : P.αg - Qbar ≤ J := le_trans (le_max_right _ _) hJlo
              have h2 : P.αb ≤ J := le_trans (le_max_left _ _) hJlo
              dsimp [FH]
              rw [min_eq_left (by linarith), max_eq_right hJhi,
                min_eq_left (by linarith), max_eq_left h2]
              ring
            rw [h_dec I hI_km.le hI_ag, h_dec km (le_refl _) (max_le hαb_αg.le (by linarith))]
            have := mul_le_mul_of_nonneg_left hI_km.le (mul_nonneg (sub_pos.mpr hρ1).le hc0.le)
            linarith
        · refine ⟨P.αg, by simp [candList_tb], le_trans ?_ (hFH_le_sv P.αg hαg0.le hαg1.le)⟩
          have h_gt : ∀ J : ℝ, P.αg ≤ J →
              FH J = P.ρ * (w * P.αg - P.cost q * J) + (1 - P.ρ) * (w * P.αb - P.cost q * J) := by
            intro J hJ
            dsimp [FH]
            rw [min_eq_left (by linarith), max_eq_left hJ,
              min_eq_left (by linarith), max_eq_left (le_trans hαb_αg.le hJ)]
          rw [h_gt I hI_ag.le, h_gt P.αg (le_refl _)]
          have := mul_le_mul_of_nonneg_left hI_ag.le hc0.le
          linarith
    · have hsv_I : sv I = FL I := by
        dsimp [sv, FL]
        unfold Profile.supplierValue Params.prob Profile.supplierStateValue Params.supplierState
        have hrm := hrm_cw hcw I .bad hI
        have hgood := hgood_val I hI
        unfold Profile.supplierStateValue Params.supplierState at hgood
        rw [hgood, hRb_I, hrm.2, ← hrm.1, hRb_I]
      rw [hsv_I]
      have hwL : w < q * P.θL := by
        have hpos : 0 < (q * P.θH - w) * min P.αb (I + Qbar) :=
          mul_pos hwH0 (lt_min hαb0 hS_pos_I)
        have hLpos : 0 < (q * P.θL - w) * min 1 (I + Qbar) := lt_of_lt_of_le hpos hHL_I
        have hm0 : 0 ≤ min 1 (I + Qbar) := le_min zero_le_one hS_pos_I.le
        by_contra hc
        have hle : q * P.θL - w ≤ 0 := by linarith
        have := mul_nonpos_of_nonpos_of_nonneg hle hm0
        linarith
      have hwL0 : 0 < q * P.θL - w := sub_pos.mpr hwL
      have hS_gt_ab : P.αb < I + Qbar := by
        by_contra hc
        have hle : I + Qbar ≤ P.αb := le_of_not_gt hc
        rw [min_eq_right hle, min_eq_right (le_trans hle (le_trans hαb_αg.le hαg1.le))] at hHL_I
        have h1 : q * P.θH - w ≤ q * P.θL - w := le_of_mul_le_mul_right hHL_I hS_pos_I
        have := mul_lt_mul_of_pos_left hθLH hq_pos
        linarith
      let S0 := (q * P.θH - w) * P.αb / (q * P.θL - w)
      let J0 := max 0 (S0 - Qbar)
      have hS0_gt_ab : P.αb < S0 := by
        dsimp [S0]
        rw [lt_div_iff₀ hwL0, mul_comm P.αb]
        have := mul_lt_mul_of_pos_left hθLH hq_pos
        exact mul_lt_mul_of_pos_right (by linarith) hαb0
      have hS0_le_min : S0 ≤ min 1 (I + Qbar) := by
        dsimp [S0]
        rw [div_le_iff₀ hwL0, mul_comm _ (q * P.θL - w)]
        rw [min_eq_left hS_gt_ab.le] at hHL_I
        exact hHL_I
      have hS0_le1 : S0 ≤ 1 := le_trans hS0_le_min (min_le_left _ _)
      have hJ0_le_I : J0 ≤ I := by
        have := le_trans hS0_le_min (min_le_right _ _)
        exact max_le hI (by linarith)
      have hsv_FL : ∀ J : ℝ, J0 ≤ J → sv J = FL J := by
        intro J hJ
        have hJ0 : 0 ≤ J := le_trans (le_max_left _ _) hJ
        have hJQ_S0 : S0 ≤ J + Qbar := by
          have := le_trans (le_max_right _ _) hJ
          linarith
        have hJQ_ab : P.αb < J + Qbar := lt_of_lt_of_le hS0_gt_ab hJQ_S0
        have hJQ_pos : 0 < J + Qbar := lt_trans hαb0 hJQ_ab
        have hmin_ge : S0 ≤ min 1 (J + Qbar) := le_min hS0_le1 hJQ_S0
        have hcmp : (q * P.θH - w) * min P.αb (J + Qbar) ≤
            (q * P.θL - w) * min 1 (J + Qbar) := by
          rw [min_eq_left hJQ_ab.le]
          have h1 : (q * P.θH - w) * P.αb = (q * P.θL - w) * S0 := by
            dsimp [S0]
            rw [mul_div_cancel₀ _ hwL0.ne']
          rw [h1]
          exact mul_le_mul_of_nonneg_left hmin_ge hwL0.le
        have hRb_J : (basePost_tb P Qbar).recv q w J .bad
            ((basePost_tb P Qbar).order q w J .bad) = min 1 (J + Qbar) := by
          have hrm := hrm_cw hcw J .bad hJ0
          rw [hrm.1]
          have hord : (basePost_tb P Qbar).order q w J .bad = min 1 (J + Qbar) := by
            unfold basePost_tb
            dsimp only
            rw [if_pos hcw, Params.alpha]
            have hvH_pos : 0 < (q * P.θH - w) * min P.αb (J + Qbar) :=
              mul_pos hwH0 (lt_min hαb0 hJQ_pos)
            rw [if_neg (not_le_of_gt (lt_of_lt_of_le hvH_pos (le_max_left _ _))), if_pos hcmp]
          rw [hord, min_eq_left (min_le_right _ _)]
        dsimp [sv, FL]
        unfold Profile.supplierValue Params.prob Profile.supplierStateValue Params.supplierState
        have hrm := hrm_cw hcw J .bad hJ0
        have hgood := hgood_val J hJ0
        unfold Profile.supplierStateValue Params.supplierState at hgood
        rw [hgood, hRb_J, hrm.2, ← hrm.1, hRb_J]
      rcases le_or_gt I P.αg with hI_ag | hI_ag
      · refine ⟨P.αg, by simp [candList_tb], ?_⟩
        rw [hsv_FL P.αg (le_trans hJ0_le_I hI_ag)]
        have hFL_lo : ∀ J : ℝ, 0 ≤ J → J ≤ P.αg →
            FL J = P.ρ * ((w - P.cost q) * min P.αg (J + Qbar)) +
              (1 - P.ρ) * ((w - P.cost q) * min 1 (J + Qbar)) := by
          intro J _hJ0 hJhi
          dsimp [FL]
          rw [max_eq_right (le_min hJhi (by linarith)),
            max_eq_right (le_min (le_trans hJhi hαg1.le) (by linarith))]
          ring
        rw [hFL_lo I hI hI_ag, hFL_lo P.αg hαg0.le (le_refl _)]
        have h1 : (w - P.cost q) * min P.αg (I + Qbar) ≤
            (w - P.cost q) * min P.αg (P.αg + Qbar) :=
          mul_le_mul_of_nonneg_left (min_le_min_left P.αg (by linarith)) hwc0
        have h2 : (w - P.cost q) * min 1 (I + Qbar) ≤
            (w - P.cost q) * min 1 (P.αg + Qbar) :=
          mul_le_mul_of_nonneg_left (min_le_min_left 1 (by linarith)) hwc0
        have := mul_le_mul_of_nonneg_left h1 hρ0.le
        have := mul_le_mul_of_nonneg_left h2 (sub_pos.mpr hρ1).le
        linarith
      · let M := max P.αg (max 0 (1 - Qbar))
        have hM_mem : M ∈ candList_tb P Qbar q w := by
          rcases max_choice P.αg (max 0 (1 - Qbar)) with h1 | h1 <;>
          · dsimp [M]; rw [h1]; simp [candList_tb]
        rcases le_or_gt M I with hMI | hIM
        · refine ⟨M, hM_mem, ?_⟩
          have hJ0_M : J0 ≤ M := by
            refine max_le (le_trans hαg0.le (le_max_left _ _)) ?_
            exact le_trans (by linarith : S0 - Qbar ≤ 1 - Qbar)
              (le_trans (le_max_right 0 (1 - Qbar)) (le_max_right _ _))
          rw [hsv_FL M hJ0_M]
          have hFL_hi : ∀ J : ℝ, M ≤ J →
              FL J = P.ρ * (w * P.αg - P.cost q * J) +
                (1 - P.ρ) * (w - P.cost q * max J 1) := by
            intro J hJ
            have hJag : P.αg ≤ J := le_trans (le_max_left _ _) hJ
            have hJ1Q : 1 - Qbar ≤ J :=
              le_trans (le_max_right 0 (1 - Qbar)) (le_trans (le_max_right _ _) hJ)
            dsimp [FL]
            rw [min_eq_left (by linarith), max_eq_left hJag, min_eq_left (by linarith)]
            ring
          rw [hFL_hi I hMI, hFL_hi M (le_refl _)]
          have h1 : P.cost q * M ≤ P.cost q * I := mul_le_mul_of_nonneg_left hMI hc0.le
          have h2 : P.cost q * max M 1 ≤ P.cost q * max I 1 :=
            mul_le_mul_of_nonneg_left (max_le_max_right 1 hMI) hc0.le
          have := mul_le_mul_of_nonneg_left (by linarith : w * P.αg - P.cost q * I ≤
            w * P.αg - P.cost q * M) hρ0.le
          have := mul_le_mul_of_nonneg_left (by linarith : w - P.cost q * max I 1 ≤
            w - P.cost q * max M 1) (sub_pos.mpr hρ1).le
          linarith
        · have hI_lt_1Q : I < 1 - Qbar := by
            have h1 : I < max P.αg (max 0 (1 - Qbar)) := hIM
            rcases lt_max_iff.mp h1 with h2 | h2
            · linarith
            · rcases lt_max_iff.mp h2 with h3 | h3
              · linarith
              · exact h3
          let L := max P.αg J0
          let U := max 0 (1 - Qbar)
          have hU_eq : U = 1 - Qbar := max_eq_right (by linarith)
          have hI_le_U : I ≤ U := by rw [hU_eq]; exact hI_lt_1Q.le
          have hL_le_U : L ≤ U := le_trans (max_le hI_ag.le hJ0_le_I) hI_le_U
          have hL_le_I : L ≤ I := max_le hI_ag.le hJ0_le_I
          have h_aff : ∀ J : ℝ, L ≤ J → J ≤ U →
              FL J = ((1 - P.ρ) * w - P.cost q) * J +
                (P.ρ * w * P.αg + (1 - P.ρ) * (w - P.cost q) * Qbar) := by
            intro J hJlo hJhi
            have hJag : P.αg ≤ J := le_trans (le_max_left _ _) hJlo
            have hJQ1 : J + Qbar ≤ 1 := by linarith
            dsimp [FL]
            rw [min_eq_left (by linarith), max_eq_left hJag,
              min_eq_right hJQ1, max_eq_right (by linarith : J ≤ J + Qbar)]
            ring
          have hle_max : FL I ≤ max (sv L) (sv U) := by
            rw [h_aff I hL_le_I hI_le_U]
            refine affine_le_max_tb hL_le_I hI_le_U ?_ ?_
            · rw [← h_aff L (le_refl _) hL_le_U, hsv_FL L (le_max_right _ _)]
            · rw [← h_aff U hL_le_U (le_refl _),
                hsv_FL U (le_trans hJ0_le_I hI_le_U)]
          rcases max_choice (sv L) (sv U) with h1 | h1
          · rw [h1] at hle_max
            have hL_mem : L ∈ candList_tb P Qbar q w := by
              rcases max_choice P.αg J0 with h2 | h2 <;>
              · dsimp [L, J0, S0] at h2 ⊢; rw [h2]; simp [candList_tb]
            exact ⟨L, hL_mem, hle_max⟩
          · rw [h1] at hle_max
            exact ⟨U, by simp [U, candList_tb], hle_max⟩
  · refine ⟨0, by simp [candList_tb], ?_⟩
    rcases lt_or_ge w (P.cost q) with hw_lt | hcw
    · have hstate_le : ∀ s : State,
          (basePost_tb P Qbar).supplierStateValue P q w I s ≤ 0 ∧
          (basePost_tb P Qbar).supplierStateValue P q w 0 s = 0 := by
        intro s
        have hQoI := hQo_0 I s hI
        have hQo0 := hQo_0 0 s (le_refl 0)
        let QI := (basePost_tb P Qbar).order q w I s
        let Q0 := (basePost_tb P Qbar).order q w 0 s
        have hreJ : ∀ J : ℝ, (basePost_tb P Qbar).react q w J s ((basePost_tb P Qbar).order q w J s) = 0 := by
          intro J
          change (if P.cost q ≤ w then _ else 0) = 0
          rw [if_neg (not_le_of_gt hw_lt)]
        change (w * received I QI ((basePost_tb P Qbar).react q w I s QI) -
            P.cost q * (I + inSeason I QI ((basePost_tb P Qbar).react q w I s QI)) ≤ 0) ∧
          (w * received 0 Q0 ((basePost_tb P Qbar).react q w 0 s Q0) -
            P.cost q * (0 + inSeason 0 Q0 ((basePost_tb P Qbar).react q w 0 s Q0)) = 0)
        rw [hreJ I, hreJ 0]
        unfold received inSeason
        have hI_part : w * (if QI ≤ I then QI else min (I + 0) QI) -
            P.cost q * (I + if QI ≤ I then 0 else 0) ≤ 0 := by
          split_ifs with h1
          · have := mul_le_mul_of_nonneg_left h1 hw
            have := mul_nonpos_of_nonpos_of_nonneg (by linarith : w - P.cost q ≤ 0) hI
            linarith
          · simp only [add_zero, min_eq_left (le_of_not_ge h1)]
            have := mul_nonpos_of_nonpos_of_nonneg (by linarith : w - P.cost q ≤ 0) hI
            linarith
        have h0_part : w * (if Q0 ≤ 0 then Q0 else min (0 + 0) Q0) -
            P.cost q * (0 + if Q0 ≤ 0 then 0 else 0) = 0 := by
          split_ifs with h1
          · have hQ0_eq : Q0 = 0 := le_antisymm h1 hQo0
            simp [hQ0_eq]
          · simp only [add_zero, min_eq_left (le_of_not_ge h1), mul_zero, sub_zero]
        exact ⟨hI_part, h0_part⟩
      dsimp [sv]
      unfold Profile.supplierValue Params.prob
      rw [(hstate_le .good).2, (hstate_le .bad).2]
      have := mul_nonpos_of_nonneg_of_nonpos hρ0.le (hstate_le .good).1
      have := mul_nonpos_of_nonneg_of_nonpos (sub_pos.mpr hρ1).le (hstate_le .bad).1
      linarith
    · have hw_ge_H : q * P.θH ≤ w := by
        rcases eq_or_lt_of_le hq with rfl | hq_pos
        · simp [hw]
        · by_contra hc
          exact hcase ⟨hcw, hq_pos, lt_of_not_ge hc⟩
      have hw_ge_L : q * P.θL ≤ w :=
        le_trans (mul_le_mul_of_nonneg_left hθLH.le hq) hw_ge_H
      have hstate_zero : ∀ J : ℝ, ∀ s : State, 0 ≤ J →
          (basePost_tb P Qbar).supplierStateValue P q w J s = -P.cost q * J := by
        intro J s hJ
        have hS0 : 0 ≤ J + Qbar := add_nonneg hJ hQ0
        obtain ⟨hα0, _⟩ : 0 ≤ P.alpha s ∧ True := by
          cases s <;> exact ⟨by simp [Params.alpha]; linarith, trivial⟩
        have hvH_le : (q * P.θH - w) * min (P.alpha s) (J + Qbar) ≤ 0 :=
          mul_nonpos_of_nonpos_of_nonneg (by linarith) (le_min hα0 hS0)
        have hvL_le : (q * P.θL - w) * min 1 (J + Qbar) ≤ 0 :=
          mul_nonpos_of_nonpos_of_nonneg (by linarith) (le_min zero_le_one hS0)
        have hord0 : (basePost_tb P Qbar).order q w J s = 0 := by
          unfold basePost_tb
          dsimp only
          rw [if_pos hcw, if_pos (max_le hvH_le hvL_le)]
        unfold Profile.supplierStateValue Params.supplierState Profile.recv Profile.made
          received inSeason
        rw [hord0, if_pos hJ, if_pos hJ]
        ring
      dsimp [sv]
      unfold Profile.supplierValue Params.prob
      rw [hstate_zero I .good hI, hstate_zero I .bad hI,
        hstate_zero 0 .good (le_refl 0), hstate_zero 0 .bad (le_refl 0)]
      have hc0 : 0 ≤ P.cost q := mul_nonneg hk.le (sq_nonneg q)
      have : 0 ≤ P.cost q * I := mul_nonneg hc0 hI
      linarith

private lemma focus_Y_props_tb (P : Params) (hStand : P.Standing) (hFocus : P.Focus)
    (S : ℝ) (hSag : P.αg ≤ S) (hS1 : S ≤ 1) :
    0 < P.ρ * P.αg + (1 - P.ρ) * S ∧
    0 < P.Y S ∧
    0 < P.X ∧
    P.X ≤ P.Y S ∧
    P.Y S ≤ P.ρ * P.θH + (1 - P.ρ) * P.θL ∧
    P.Y S < 2 * P.θL ∧
    P.X < 2 * P.θL ∧
    P.Y S * (S - P.αb) < 2 * (P.θL * S - P.θH * P.αb) ∧
    P.X * (S - P.αb) < 2 * (P.θL * S - P.θH * P.αb) := by
  rcases hStand with ⟨hθL, hθLH, _hk, hρ0, hρ1, hαb0, hαb_lt, hαg_gt, hαg1⟩
  have hθH : 0 < P.θH := lt_trans hθL hθLH
  have hαg0 : 0 < P.αg := pos_of_mul_pos_left (lt_trans hθL hαg_gt) hθH.le
  have hαb_αg : P.αb < P.αg := lt_of_mul_lt_mul_right (lt_trans hαb_lt hαg_gt) hθH.le
  have h1ρ : 0 < 1 - P.ρ := sub_pos.mpr hρ1
  have hS0 : 0 < S := lt_of_lt_of_le hαg0 hSag
  have hDS : 0 < P.ρ * P.αg + (1 - P.ρ) * S :=
    add_pos (mul_pos hρ0 hαg0) (mul_pos h1ρ hS0)
  have hD1 : 0 < P.ρ * P.αg + (1 - P.ρ) * 1 :=
    add_pos (mul_pos hρ0 hαg0) (mul_pos h1ρ zero_lt_one)
  have hYS_pos : 0 < P.Y S := by
    unfold Params.Y
    exact div_pos (add_pos (mul_pos (mul_pos hρ0 hαg0) hθH) (mul_pos (mul_pos h1ρ hS0) hθL)) hDS
  have hX_pos : 0 < P.X := by
    unfold Params.X Params.Y
    exact div_pos (add_pos (mul_pos (mul_pos hρ0 hαg0) hθH) (mul_pos (mul_pos h1ρ zero_lt_one) hθL)) hD1
  have hX_le_YS : P.X ≤ P.Y S := by
    unfold Params.X Params.Y
    rw [div_le_div_iff₀ hD1 hDS]
    have : 0 ≤ P.ρ * (1 - P.ρ) * P.αg * (1 - S) * (P.θH - P.θL) :=
      mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hρ0.le h1ρ.le) hαg0.le) (by linarith)) (by linarith)
    linarith
  have hYS_le_Y0 : P.Y S ≤ P.ρ * P.θH + (1 - P.ρ) * P.θL := by
    unfold Params.Y
    rw [div_le_iff₀ hDS]
    have : 0 ≤ P.ρ * (1 - P.ρ) * (S - P.αg) * (P.θH - P.θL) :=
      mul_nonneg (mul_nonneg (mul_nonneg hρ0.le h1ρ.le) (by linarith)) (by linarith)
    linarith
  have hY0_lt_2θL : P.ρ * P.θH + (1 - P.ρ) * P.θL < 2 * P.θL := by
    have h1 : 2 * (P.θL * P.αg - P.θH * P.αb) < 2 * P.θL * (P.αg - P.αb) := by
      have : 0 < (P.θH - P.θL) * P.αb := mul_pos (by linarith) hαb0
      linarith
    exact lt_of_mul_lt_mul_right (lt_trans hFocus h1) (by linarith : 0 ≤ P.αg - P.αb)
  have hYS_lt_2θL : P.Y S < 2 * P.θL := lt_of_le_of_lt hYS_le_Y0 hY0_lt_2θL
  have hX_lt_2θL : P.X < 2 * P.θL := lt_of_le_of_lt hX_le_YS hYS_lt_2θL
  have hYS_focus : P.Y S * (S - P.αb) < 2 * (P.θL * S - P.θH * P.αb) := by
    have h1 : P.Y S * (S - P.αb) * (P.αg - P.αb) ≤
        (P.ρ * P.θH + (1 - P.ρ) * P.θL) * (P.αg - P.αb) * (S - P.αb) := by
      have := mul_le_mul_of_nonneg_right hYS_le_Y0
        (mul_nonneg (by linarith : 0 ≤ S - P.αb) (by linarith : 0 ≤ P.αg - P.αb))
      linarith
    have h2 : (P.ρ * P.θH + (1 - P.ρ) * P.θL) * (P.αg - P.αb) * (S - P.αb) <
        2 * (P.θL * P.αg - P.θH * P.αb) * (S - P.αb) :=
      mul_lt_mul_of_pos_right hFocus (by linarith)
    have h3 : 2 * (P.θL * P.αg - P.θH * P.αb) * (S - P.αb) ≤
        2 * (P.θL * S - P.θH * P.αb) * (P.αg - P.αb) := by
      have : 0 ≤ 2 * (P.θH - P.θL) * P.αb * (S - P.αg) :=
        mul_nonneg (mul_nonneg (by linarith) hαb0.le) (by linarith)
      linarith
    exact lt_of_mul_lt_mul_right (lt_of_le_of_lt h1 (lt_of_lt_of_le h2 h3)) (by linarith)
  have hX_focus : P.X * (S - P.αb) < 2 * (P.θL * S - P.θH * P.αb) :=
    lt_of_le_of_lt (mul_le_mul_of_nonneg_right hX_le_YS (by linarith)) hYS_focus
  exact ⟨hDS, hYS_pos, hX_pos, hX_le_YS, hYS_le_Y0, hYS_lt_2θL, hX_lt_2θL, hYS_focus, hX_focus⟩

private lemma vos_num_mono_tb (ρ αg θH θL S : ℝ) :
    (ρ * αg * θH + (1 - ρ) * S * θL) ^ 2 -
      αg * (ρ * θH + (1 - ρ) * θL) ^ 2 * (ρ * αg + (1 - ρ) * S) =
    (1 - ρ) * (S - αg) * ((ρ * αg + (1 - ρ) * S) * θL ^ 2 - αg * ρ ^ 2 * (θH - θL) ^ 2) := by
  ring

private lemma oo_margin_id_tb (ρ X θ k : ℝ) (hk : k ≠ 0) :
    (1 - ρ) * X / (2 * k) * θ - (1 - ρ) * X ^ 2 / (4 * k) =
      (1 - ρ) * X / (4 * k) * (2 * θ - X) := by
  field_simp [hk]; ring

private lemma os_margin_id_tb (Y θ k : ℝ) (hk : k ≠ 0) :
    Y / (2 * k) * θ - Y ^ 2 / (4 * k) =
      Y / (4 * k) * (2 * θ - Y) := by
  field_simp [hk]; ring

private lemma hod_med_tb (P : Params) (hP : P.Dom) (Qbar : ℝ) (h0 : 0 ≤ Qbar) (h1 : Qbar ≤ 1 - P.αg) :
    (P.ρ * P.αg + (1 - P.ρ) * P.αb) * P.θH ^ 2 / (4 * P.k) < max (P.V_OS Qbar) P.V_OO := by
  rcases hP with ⟨hStand, hFocus, hHOD⟩
  obtain ⟨hDS, _hYS_pos, _hX_pos, _hX_le, _hYS_le, _hYS_lt, _hX_lt, _hYS_f, _hX_f⟩ :=
    focus_Y_props_tb P hStand hFocus (P.αg + Qbar) (by linarith) (by linarith)
  obtain ⟨_hD0, _hY0_pos, _hX_pos2, _hX_le2, _hY0_le, hY0_lt, _, _, _⟩ :=
    focus_Y_props_tb P hStand hFocus P.αg (le_refl _) (by rcases hStand with ⟨_, _, _, _, _, _, _, _, hαg1⟩; exact hαg1.le)
  rcases hStand with ⟨hθL, hθLH, hk, hρ0, hρ1, _hαb0, _hαb_lt, hαg_gt, _hαg1⟩
  have hθH : 0 < P.θH := lt_trans hθL hθLH
  have hαg0 : 0 < P.αg := pos_of_mul_pos_left (lt_trans hθL hαg_gt) hθH.le
  have h1ρ : 0 < 1 - P.ρ := sub_pos.mpr hρ1
  have hD1 : 0 < P.ρ * P.αg + 1 - P.ρ := by
    have : 0 < P.ρ * P.αg := mul_pos hρ0 hαg0
    linarith
  have h4k : 0 < 4 * P.k := by linarith
  unfold Params.HighOnlyDominated at hHOD
  have hVOO_eq : P.V_OO =
      ((1 - P.ρ) * (P.ρ * P.αg * P.θH + (1 - P.ρ) * P.θL) ^ 2 / (P.ρ * P.αg + 1 - P.ρ)) / (4 * P.k) := by
    unfold Params.V_OO Params.X Params.Y
    have hd : P.ρ * P.αg + (1 - P.ρ) * 1 = P.ρ * P.αg + 1 - P.ρ := by ring
    rw [hd]
    field_simp [hD1.ne', hk.ne']
  have hVOS_eq : P.V_OS Qbar =
      ((P.ρ * P.αg * P.θH + (1 - P.ρ) * (P.αg + Qbar) * P.θL) ^ 2 /
        (P.ρ * P.αg + (1 - P.ρ) * (P.αg + Qbar))) / (4 * P.k) := by
    unfold Params.V_OS Params.supplyS Params.Y
    rw [min_eq_left (by linarith : P.αg + Qbar ≤ 1)]
    field_simp [hDS.ne', hk.ne']
  have hVOS_ge0 : P.αg * (P.ρ * P.θH + (1 - P.ρ) * P.θL) ^ 2 ≤
      (P.ρ * P.αg * P.θH + (1 - P.ρ) * (P.αg + Qbar) * P.θL) ^ 2 /
        (P.ρ * P.αg + (1 - P.ρ) * (P.αg + Qbar)) := by
    rw [le_div_iff₀ hDS]
    have hY0_def : P.Y P.αg = P.ρ * P.θH + (1 - P.ρ) * P.θL := by
      unfold Params.Y
      have hd0 : P.ρ * P.αg + (1 - P.ρ) * P.αg = P.αg := by ring
      rw [hd0]
      field_simp [hαg0.ne']
    have hρ_diff : P.ρ * (P.θH - P.θL) < P.θL := by
      rw [hY0_def] at hY0_lt
      linarith
    have hρ_diff_nonneg : 0 ≤ P.ρ * (P.θH - P.θL) := mul_nonneg hρ0.le (by linarith)
    have hsq_le : (P.ρ * (P.θH - P.θL)) ^ 2 ≤ P.θL ^ 2 :=
      sq_le_sq' (by linarith) hρ_diff.le
    have h1_le : P.αg * P.ρ ^ 2 * (P.θH - P.θL) ^ 2 ≤ P.αg * P.θL ^ 2 := by
      have hmul := mul_le_mul_of_nonneg_left hsq_le hαg0.le
      have heq : P.αg * (P.ρ * (P.θH - P.θL)) ^ 2 = P.αg * P.ρ ^ 2 * (P.θH - P.θL) ^ 2 := by ring
      linarith
    have hu_ge : P.αg ≤ P.ρ * P.αg + (1 - P.ρ) * (P.αg + Qbar) := by
      have : 0 ≤ (1 - P.ρ) * Qbar := mul_nonneg h1ρ.le h0
      linarith
    have h2_le : P.αg * P.θL ^ 2 ≤ (P.ρ * P.αg + (1 - P.ρ) * (P.αg + Qbar)) * P.θL ^ 2 :=
      mul_le_mul_of_nonneg_right hu_ge (sq_nonneg P.θL)
    have hpos : 0 ≤ (1 - P.ρ) * ((P.αg + Qbar) - P.αg) *
        ((P.ρ * P.αg + (1 - P.ρ) * (P.αg + Qbar)) * P.θL ^ 2 -
          P.αg * P.ρ ^ 2 * (P.θH - P.θL) ^ 2) :=
      mul_nonneg (mul_nonneg h1ρ.le (by linarith)) (by linarith)
    have hid := vos_num_mono_tb P.ρ P.αg P.θH P.θL (P.αg + Qbar)
    linarith
  have hlt1 : (P.ρ * P.αg + (1 - P.ρ) * P.αb) * P.θH ^ 2 <
      max ((P.ρ * P.αg * P.θH + (1 - P.ρ) * (P.αg + Qbar) * P.θL) ^ 2 /
          (P.ρ * P.αg + (1 - P.ρ) * (P.αg + Qbar)))
        ((1 - P.ρ) * (P.ρ * P.αg * P.θH + (1 - P.ρ) * P.θL) ^ 2 / (P.ρ * P.αg + 1 - P.ρ)) := by
    refine lt_of_lt_of_le hHOD (max_le (le_max_right _ _) (le_trans hVOS_ge0 (le_max_left _ _)))
  rw [hVOS_eq, hVOO_eq]
  rcases max_choice ((P.ρ * P.αg * P.θH + (1 - P.ρ) * (P.αg + Qbar) * P.θL) ^ 2 /
      (P.ρ * P.αg + (1 - P.ρ) * (P.αg + Qbar)))
    ((1 - P.ρ) * (P.ρ * P.αg * P.θH + (1 - P.ρ) * P.θL) ^ 2 / (P.ρ * P.αg + 1 - P.ρ)) with hm | hm
  · rw [hm] at hlt1
    exact lt_of_lt_of_le (div_lt_div_of_pos_right hlt1 h4k) (le_max_left _ _)
  · rw [hm] at hlt1
    exact lt_of_lt_of_le (div_lt_div_of_pos_right hlt1 h4k) (le_max_right _ _)

private lemma lin_id_os_tb (P : Params) (Qbar q : ℝ) (hk : 0 < P.k)
    (h1 : Qbar ≤ 1 - P.αg) (hDS : 0 < P.ρ * P.αg + (1 - P.ρ) * (P.αg + Qbar)) :
    P.ρ * ((q * P.θH - P.cost q) * P.αg) + (1 - P.ρ) * ((q * P.θL - P.cost q) * (P.αg + Qbar)) =
      P.V_OS Qbar - (P.ρ * P.αg + (1 - P.ρ) * (P.αg + Qbar)) * P.k *
        (q - P.Y (P.αg + Qbar) / (2 * P.k)) ^ 2 := by
  unfold Params.V_OS Params.supplyS Params.Y Params.cost
  rw [min_eq_left (by linarith : P.αg + Qbar ≤ 1)]
  field_simp [hDS.ne', hk.ne']
  ring

private lemma val_qos_tb (P : Params) (Qbar : ℝ) (hk : 0 < P.k)
    (h1 : Qbar ≤ 1 - P.αg) (hDS : 0 < P.ρ * P.αg + (1 - P.ρ) * (P.αg + Qbar)) :
    P.ρ * ((P.Y (P.αg + Qbar) / (2 * P.k) * P.θH - P.Y (P.αg + Qbar) ^ 2 / (4 * P.k)) * P.αg) +
      (1 - P.ρ) * ((P.Y (P.αg + Qbar) / (2 * P.k) * P.θL - P.Y (P.αg + Qbar) ^ 2 / (4 * P.k)) *
        (P.αg + Qbar)) = P.V_OS Qbar := by
  unfold Params.V_OS Params.supplyS Params.Y
  rw [min_eq_left (by linarith : P.αg + Qbar ≤ 1)]
  field_simp [hDS.ne', hk.ne']
  ring

private lemma lin_id_oo_tb (P : Params) (q : ℝ) (hk : 0 < P.k) (h1ρ : 0 < 1 - P.ρ)
    (hD1 : 0 < P.ρ * P.αg + 1 - P.ρ) :
    P.ρ * ((q * P.θH - P.cost q / (1 - P.ρ)) * P.αg) +
      (1 - P.ρ) * (q * P.θL - P.cost q / (1 - P.ρ)) =
      P.V_OO - (P.ρ * P.αg + 1 - P.ρ) / (1 - P.ρ) * P.k *
        (q - (1 - P.ρ) * P.X / (2 * P.k)) ^ 2 := by
  unfold Params.V_OO Params.X Params.Y Params.cost
  have hd : P.ρ * P.αg + (1 - P.ρ) * 1 = P.ρ * P.αg + 1 - P.ρ := by ring
  rw [hd]
  field_simp [hD1.ne', h1ρ.ne', hk.ne']
  ring

private lemma val_qoo_tb (P : Params) (Qbar : ℝ) (hk : 0 < P.k) (h1ρ : 0 < 1 - P.ρ)
    (hD1 : 0 < P.ρ * P.αg + 1 - P.ρ) :
    P.cost ((1 - P.ρ) * P.X / (2 * P.k)) = (1 - P.ρ) ^ 2 * P.X ^ 2 / (4 * P.k) ∧
    P.cost ((1 - P.ρ) * P.X / (2 * P.k)) / (1 - P.ρ) = (1 - P.ρ) * P.X ^ 2 / (4 * P.k) ∧
    P.ρ * (((1 - P.ρ) * P.X / (2 * P.k) * P.θH - (1 - P.ρ) * P.X ^ 2 / (4 * P.k)) * P.αg) +
      (1 - P.ρ) * ((1 - P.ρ) * P.X / (2 * P.k) * P.θL - (1 - P.ρ) * P.X ^ 2 / (4 * P.k)) = P.V_OO ∧
    P.ρ * ((1 - P.ρ) * P.X ^ 2 / (4 * P.k) * P.αg -
        (1 - P.ρ) ^ 2 * P.X ^ 2 / (4 * P.k) * (1 - Qbar)) +
      (1 - P.ρ) * ((1 - P.ρ) * P.X ^ 2 / (4 * P.k) - (1 - P.ρ) ^ 2 * P.X ^ 2 / (4 * P.k)) =
      P.ρ * (1 - P.ρ) * (P.αg + (1 - P.ρ) * Qbar) * P.X ^ 2 / (4 * P.k) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · unfold Params.cost; field_simp [hk.ne']; ring
  · unfold Params.cost; field_simp [hk.ne', h1ρ.ne']; ring
  · unfold Params.V_OO Params.X Params.Y
    have hd : P.ρ * P.αg + (1 - P.ρ) * 1 = P.ρ * P.αg + 1 - P.ρ := by ring
    rw [hd]
    field_simp [hD1.ne', hk.ne']
    ring
  · field_simp [hk.ne']; ring

private lemma inv_le_ag_of_lt_oo_tb (P : Params) (hStand : P.Standing)
    (Qbar : ℝ) (hQ0 : 0 ≤ Qbar) (hQ1 : Qbar < 1 - P.αg)
    (σ : Profile) (hpost : IsPostInventorySPE P Qbar σ)
    (q w : ℝ) (hq_pos : 0 < q) (hcw : P.cost q ≤ w) (hw_lt_c1ρ : w < P.cost q / (1 - P.ρ))
    (hwL : w < q * P.θL)
    (hI0 : 0 ≤ σ.inv q w)
    (hI_opt : ∀ I' : ℝ, 0 ≤ I' → σ.supplierValue P q w I' ≤ σ.supplierValue P q w (σ.inv q w))
    (hsv_I_nonneg : 0 ≤ σ.supplierValue P q w (σ.inv q w))
    (hBrL : (q * P.θH - w) * min P.αb (σ.inv q w + Qbar) <
      (q * P.θL - w) * min (σ.inv q w + Qbar) 1) :
    σ.inv q w ≤ P.αg := by
  rcases hStand with ⟨hθL, hθLH, hk, hρ0, hρ1, hαb0, hαb_lt, hαg_gt, hαg1⟩
  have hStand : P.Standing := ⟨hθL, hθLH, hk, hρ0, hρ1, hαb0, hαb_lt, hαg_gt, hαg1⟩
  have hθH : 0 < P.θH := lt_trans hθL hθLH
  have hαg0 : 0 < P.αg := pos_of_mul_pos_left (lt_trans hθL hαg_gt) hθH.le
  have hαb_αg : P.αb < P.αg := lt_of_mul_lt_mul_right (lt_trans hαb_lt hαg_gt) hθH.le
  have h1ρ : 0 < 1 - P.ρ := sub_pos.mpr hρ1
  have hc_pos : 0 < P.cost q := mul_pos hk (pow_pos hq_pos 2)
  have hw_pos : 0 < w := lt_of_lt_of_le hc_pos hcw
  have hqLH : q * P.θL < q * P.θH := mul_lt_mul_of_pos_left hθLH hq_pos
  have hwH : w < q * P.θH := lt_trans hwL hqLH
  have hwL0 : 0 < q * P.θL - w := sub_pos.mpr hwL
  have hwH0 : 0 < q * P.θH - w := sub_pos.mpr hwH
  let I := σ.inv q w
  by_contra hI_not_le
  have hI_gt : P.αg < I := lt_of_not_ge hI_not_le
  rcases eq_or_lt_of_le hcw with hw_eq_c | hc_lt_w
  · -- Subcase A: w = P.cost q
    have hw_mul : ∀ x : ℝ, w * x = P.cost q * x := fun x => by rw [← hw_eq_c]
    have hsv_state_c : ∀ s : State,
        σ.supplierStateValue P q w I s ≤ 0 ∧
        (σ.recv q w I s (σ.order q w I s) < I → σ.supplierStateValue P q w I s < 0) := by
      intro s
      unfold Profile.supplierStateValue Params.supplierState Profile.recv Profile.made
        received inSeason
      rcases le_or_gt (σ.order q w I s) I with hQI | hIQ
      · rw [if_pos hQI, if_pos hQI, add_zero, hw_mul]
        refine ⟨?_, fun hlt => ?_⟩
        · have := mul_le_mul_of_nonneg_left hQI hc_pos.le; linarith
        · have := mul_lt_mul_of_pos_left hlt hc_pos; linarith
      · obtain ⟨hr0, _, hropt_fn⟩ := hpost.2.1 q w I s (σ.order q w I s) hq_pos.le hw_pos.le hI0 hIQ
        have hropt := hropt_fn 0 (le_refl 0) hQ0
        unfold Params.supplierState received at hropt
        simp only [if_neg (not_le_of_gt hIQ), add_zero, min_eq_left hIQ.le, hw_mul] at hropt
        simp only [if_neg (not_le_of_gt hIQ), hw_mul]
        have hle_min : P.cost q * min (I + σ.react q w I s (σ.order q w I s))
            (σ.order q w I s) ≤ P.cost q * (I + σ.react q w I s (σ.order q w I s)) :=
          mul_le_mul_of_nonneg_left (min_le_left _ _) hc_pos.le
        have hII_le : I + σ.react q w I s (σ.order q w I s) ≤ σ.order q w I s := by
          by_contra hc
          have hgt : σ.order q w I s < I + σ.react q w I s (σ.order q w I s) := lt_of_not_ge hc
          rw [min_eq_right hgt.le] at hropt
          have := mul_lt_mul_of_pos_left hgt hc_pos
          linarith
        refine ⟨by linarith, fun hlt => ?_⟩
        rw [min_eq_left hII_le] at hlt
        linarith
    let Qg := σ.order q w I .good
    let Rg := σ.recv q w I .good Qg
    let pg := σ.priceAfter q w I .good Qg
    have hI_le_Rg : I ≤ Rg := by
      by_contra hc
      have hlt := (hsv_state_c .good).2 (lt_of_not_ge hc)
      have hb0 := (hsv_state_c .bad).1
      unfold Profile.supplierValue Params.prob at hsv_I_nonneg
      have := mul_lt_mul_of_pos_left hlt hρ0
      have := mul_nonpos_of_nonneg_of_nonpos h1ρ.le hb0
      linarith
    have hRg_gt : P.αg < Rg := lt_of_lt_of_le hI_gt hI_le_Rg
    -- Ordering Q' = αg ≤ I uses zero reactive capacity and yields at least (q * θH - w) * αg
    have h1 := (hpost.2.2 q w I .good hq_pos.le hw_pos.le hI0).2 P.αg hαg0.le
    have hm0 : σ.made q w I .good P.αg = 0 := by
      unfold Profile.made inSeason; rw [if_pos hI_gt.le]
    have hrec_ag : σ.recv q w I .good P.αg = P.αg := by
      unfold Profile.recv received; rw [if_pos hI_gt.le]
    have hp_opt := (hpost.1 q w I .good P.αg (σ.made q w I .good P.αg)
      hq_pos.le hw_pos.le hI0 hαg0.le (by rw [hm0]) (by rw [hm0]; exact hQ0)).2
      (q * P.θH) (mul_pos hq_pos hθH).le
    have hrm_ag : received I P.αg (σ.made q w I .good P.αg) = P.αg := by
      rw [hm0]; unfold received; rw [if_pos hI_gt.le]
    unfold Profile.orderValue Profile.priceAfter at h1
    rw [hrec_ag] at h1
    rw [hrm_ag] at hp_opt
    have hlhs : P.retailerState q w .good P.αg (q * P.θH) = (q * P.θH - w) * P.αg := by
      unfold Params.retailerState Params.demand Params.alpha
      rw [if_neg (not_le_of_gt hqLH), if_pos (le_refl _), zero_add, min_self]
      ring
    rw [hlhs] at hp_opt
    have hov_ge : (q * P.θH - w) * P.αg ≤ σ.orderValue P q w I .good Qg := le_trans hp_opt h1
    -- Yet Rg > αg forces orderValue .good < (q * θH - w) * αg
    have hov_lt : σ.orderValue P q w I .good Qg < (q * P.θH - w) * P.αg := by
      unfold Profile.orderValue Params.retailerState Params.demand Params.alpha
      change pg * min ((if pg ≤ q * P.θL then 1 - P.αg else 0) +
          if pg ≤ q * P.θH then P.αg else 0) Rg - w * Rg < (q * P.θH - w) * P.αg
      rcases le_or_gt pg (q * P.θL) with hpL | hpL
      · have hpH : pg ≤ q * P.θH := le_trans hpL hqLH.le
        rw [if_pos hpL, if_pos hpH, sub_add_cancel]
        have hm0' : 0 ≤ min 1 Rg := le_min zero_le_one (lt_trans hαg0 hRg_gt).le
        have h_p_le : pg * min 1 Rg ≤ q * P.θL * min 1 Rg := mul_le_mul_of_nonneg_right hpL hm0'
        have h_w_le : w * min 1 Rg ≤ w * Rg := mul_le_mul_of_nonneg_left (min_le_right 1 Rg) hw_pos.le
        have h_m1 : (q * P.θL - w) * min 1 Rg ≤ q * P.θL - w := by
          have := mul_le_mul_of_nonneg_left (min_le_left 1 Rg) hwL0.le; linarith
        have h2 : q * P.θL < q * (P.αg * P.θH) := mul_lt_mul_of_pos_left hαg_gt hq_pos
        have h3 : w * P.αg ≤ w := by
          have := mul_le_mul_of_nonneg_left hαg1.le hw_pos.le; linarith
        linarith
      · rcases le_or_gt pg (q * P.θH) with hpH | hpH
        · rw [if_neg (not_le_of_gt hpL), if_pos hpH, zero_add, min_eq_left hRg_gt.le]
          have h_p_le : pg * P.αg ≤ q * P.θH * P.αg := mul_le_mul_of_nonneg_right hpH hαg0.le
          have h_w_lt : w * P.αg < w * Rg := mul_lt_mul_of_pos_left hRg_gt hw_pos
          linarith
        · rw [if_neg (not_le_of_gt hpL), if_neg (not_le_of_gt hpH), add_zero,
            min_eq_left (lt_trans hαg0 hRg_gt).le, mul_zero]
          have : 0 < w * Rg := mul_pos hw_pos (lt_trans hαg0 hRg_gt)
          have : 0 < (q * P.θH - w) * P.αg := mul_pos hwH0 hαg0
          linarith
    linarith
  · -- Subcase B: P.cost q < w < P.cost q / (1 - P.ρ)
    have hwc_pos : 0 < w - P.cost q := sub_pos.mpr hc_lt_w
    have hslope_neg : (1 - P.ρ) * w - P.cost q < 0 := by
      have := (lt_div_iff₀' h1ρ).mp hw_lt_c1ρ
      linarith
    have hreact_eq : ∀ J : ℝ, ∀ s : State, ∀ Q : ℝ, 0 ≤ J → J < Q →
        σ.react q w J s Q = min Qbar (Q - J) := by
      intro J s Q hJ hJQ
      obtain ⟨_hr0, _hrQ, hropt⟩ := hpost.2.1 q w J s Q hq_pos.le hw_pos.le hJ hJQ
      let Is := min Qbar (Q - J)
      have hge := hropt Is (le_min hQ0 (sub_pos.mpr hJQ).le) (min_le_left _ _)
      have hJIs : J + Is ≤ Q := by have := min_le_right Qbar (Q - J); dsimp [Is]; linarith
      unfold Params.supplierState received at hge
      simp only [if_neg (not_le_of_gt hJQ), min_eq_left hJIs] at hge
      rcases lt_trichotomy (σ.react q w J s Q) Is with hlt | heq | hgt
      · exfalso
        rw [min_eq_left (by linarith)] at hge
        have := mul_lt_mul_of_pos_left (by linarith : J + σ.react q w J s Q < J + Is) hwc_pos
        linarith
      · exact heq
      · exfalso
        have hIs_eq : Is = Q - J := by
          dsimp [Is] at hgt ⊢
          rcases le_or_gt Qbar (Q - J) with h1 | h1
          · rw [min_eq_left h1] at hgt; linarith
          · exact min_eq_right h1.le
        have hgtQ : Q < J + σ.react q w J s Q := by linarith
        rw [min_eq_right hgtQ.le, hIs_eq, show J + (Q - J) = Q by ring] at hge
        have := mul_lt_mul_of_pos_left hgtQ hc_pos
        linarith
    have hrecv_Imade : ∀ J : ℝ, ∀ s : State, ∀ Q : ℝ, 0 ≤ J →
        σ.recv q w J s Q = min Q (J + Qbar) ∧
        J + σ.made q w J s Q = max J (min Q (J + Qbar)) := by
      intro J s Q hJ
      unfold Profile.recv Profile.made received inSeason
      rcases le_or_gt Q J with hQJ | hJQ
      · rw [if_pos hQJ, if_pos hQJ, min_eq_left (by linarith), max_eq_left hQJ, add_zero]
        exact ⟨rfl, rfl⟩
      · rw [if_neg (not_le_of_gt hJQ), if_neg (not_le_of_gt hJQ), hreact_eq J s Q hJ hJQ]
        have hsum : J + min Qbar (Q - J) = min Q (J + Qbar) := by
          rcases le_or_gt Qbar (Q - J) with h1 | h1
          · rw [min_eq_left h1, min_eq_right (by linarith)]
          · rw [min_eq_right h1.le, min_eq_left (by linarith)]; ring
        rw [hsum, min_eq_left (min_le_left Q (J + Qbar)),
          max_eq_right (le_min hJQ.le (by linarith))]
        exact ⟨rfl, rfl⟩
    have hmade_bds : ∀ J : ℝ, ∀ s : State, ∀ Q : ℝ, 0 ≤ J →
        0 ≤ σ.made q w J s Q ∧ σ.made q w J s Q ≤ Qbar := by
      intro J s Q hJ
      unfold Profile.made inSeason
      rcases le_or_gt Q J with hQJ | hJQ
      · rw [if_pos hQJ]; exact ⟨le_refl 0, hQ0⟩
      · rw [if_neg (not_le_of_gt hJQ)]
        obtain ⟨hr0, hrQ, _⟩ := hpost.2.1 q w J s Q hq_pos.le hw_pos.le hJ hJQ
        exact ⟨hr0, hrQ⟩
    have hstep_opt : ∀ J : ℝ, ∀ s : State, 0 ≤ J →
        0 ≤ σ.order q w J s ∧
        0 ≤ σ.priceAfter q w J s (σ.order q w J s) ∧
        ∀ Q' p' : ℝ, 0 ≤ Q' → 0 ≤ p' →
          P.stepOnePayoff q w (P.alpha s) (J + Qbar) Q' p' ≤
            P.stepOnePayoff q w (P.alpha s) (J + Qbar) (σ.order q w J s)
              (σ.priceAfter q w J s (σ.order q w J s)) := by
      intro J s hJ
      obtain ⟨hQo0, hQo_opt⟩ := hpost.2.2 q w J s hq_pos.le hw_pos.le hJ
      obtain ⟨hm0, hmQ⟩ := hmade_bds J s (σ.order q w J s) hJ
      obtain ⟨hp0, _⟩ := hpost.1 q w J s (σ.order q w J s) (σ.made q w J s (σ.order q w J s))
        hq_pos.le hw_pos.le hJ hQo0 hm0 hmQ
      refine ⟨hQo0, hp0, fun Q' p' hQ' hp' => ?_⟩
      obtain ⟨hm'0, hm'Q⟩ := hmade_bds J s Q' hJ
      obtain ⟨_, hp'_opt⟩ := hpost.1 q w J s Q' (σ.made q w J s Q') hq_pos.le hw_pos.le hJ hQ' hm'0 hm'Q
      have hrec_made : received J Q' (σ.made q w J s Q') = σ.recv q w J s Q' := by
        unfold Profile.made Profile.recv received inSeason
        rcases le_or_gt Q' J with h1 | h1
        · rw [if_pos h1, if_pos h1]
        · rw [if_neg (not_le_of_gt h1), if_neg (not_le_of_gt h1), if_neg (not_le_of_gt h1)]
      have hrec' : σ.recv q w J s Q' = min Q' (J + Qbar) := (hrecv_Imade J s Q' hJ).1
      have hrec_o : σ.recv q w J s (σ.order q w J s) = min (σ.order q w J s) (J + Qbar) :=
        (hrecv_Imade J s (σ.order q w J s) hJ).1
      have h1 : P.stepOnePayoff q w (P.alpha s) (J + Qbar) Q' p' ≤ σ.orderValue P q w J s Q' := by
        unfold Params.stepOnePayoff Profile.orderValue Params.retailerState Profile.priceAfter
        rw [← hrec', ← hrec_made]
        exact hp'_opt p' hp'
      have h2 := hQo_opt Q' hQ'
      have h3 : σ.orderValue P q w J s (σ.order q w J s) =
          P.stepOnePayoff q w (P.alpha s) (J + Qbar) (σ.order q w J s)
            (σ.priceAfter q w J s (σ.order q w J s)) := by
        unfold Profile.orderValue Params.retailerState Params.stepOnePayoff
        rw [hrec_o]
      linarith
    have hmin_eq_of_pay : ∀ θ α S R : ℝ, 0 ≤ α → 0 ≤ R → R ≤ S → w < θ →
        (θ - w) * min α S ≤ θ * min α R - w * R → R = min α S := by
      intro θ α S R _hα0 _hR0 hRS hwθ hge
      have hwθ0 : 0 < θ - w := sub_pos.mpr hwθ
      rcases lt_trichotomy R (min α S) with hlt | heq | hgt
      · exfalso
        rw [min_eq_right (le_trans hlt.le (min_le_left α S))] at hge
        have := mul_lt_mul_of_pos_left hlt hwθ0
        linarith
      · exact heq
      · exfalso
        have hα_le_S : α ≤ S := by
          by_contra hc
          rw [min_eq_right (lt_of_not_ge hc).le] at hgt
          linarith
        rw [min_eq_left hα_le_S] at hgt hge
        rw [min_eq_left hgt.le] at hge
        have := mul_lt_mul_of_pos_left hgt hw_pos
        linarith
    have hR_good : ∀ J : ℝ, P.αg ≤ J →
        σ.recv q w J .good (σ.order q w J .good) = P.αg := by
      intro J hJ_ag
      have hJ0 : 0 ≤ J := le_trans hαg0.le hJ_ag
      obtain ⟨hQo0, hp0, hopt⟩ := hstep_opt J .good hJ0
      have hS_pos : 0 < J + Qbar := by linarith
      have hrule := retailer_stage_rule P hStand q w (J + Qbar) hq_pos hw_pos.le hwH hS_pos.le
      have hp_eq : σ.priceAfter q w J .good (σ.order q w J .good) = q * P.θH :=
        hrule.2.1 hS_pos _ _ hQo0 hp0 hopt
      let R := min (σ.order q w J .good) (J + Qbar)
      rw [(hrecv_Imade J .good _ hJ0).1]
      have hge := hopt P.αg (q * P.θH) hαg0.le (mul_pos hq_pos hθH).le
      rw [hp_eq] at hge
      unfold Params.stepOnePayoff Params.demand Params.alpha at hge
      rw [if_neg (not_le_of_gt hqLH), if_pos (le_refl _), zero_add,
        min_eq_left (by linarith : P.αg ≤ J + Qbar), min_self] at hge
      have hR := hmin_eq_of_pay (q * P.θH) P.αg (J + Qbar) R hαg0.le (le_min hQo0 hS_pos.le)
        (min_le_right _ _) hwH (by rw [min_eq_left (by linarith : P.αg ≤ J + Qbar)]; linarith)
      rwa [min_eq_left (by linarith : P.αg ≤ J + Qbar)] at hR
    have hR_bad_of_strictL : ∀ J : ℝ, P.αg ≤ J →
        (q * P.θH - w) * min P.αb (J + Qbar) < (q * P.θL - w) * min (J + Qbar) 1 →
        σ.recv q w J .bad (σ.order q w J .bad) = min (J + Qbar) 1 := by
      intro J hJ_ag hcmp
      have hJ0 : 0 ≤ J := le_trans hαg0.le hJ_ag
      obtain ⟨hQo0, hp0, hopt⟩ := hstep_opt J .bad hJ0
      have hS0 : 0 ≤ J + Qbar := add_nonneg hJ0 hQ0
      have hrule := retailer_stage_rule P hStand q w (J + Qbar) hq_pos hw_pos.le hwH hS0
      have hp_eq : σ.priceAfter q w J .bad (σ.order q w J .bad) = q * P.θL :=
        hrule.2.2.1 hcmp _ _ hQo0 hp0 hopt
      let R := min (σ.order q w J .bad) (J + Qbar)
      rw [(hrecv_Imade J .bad _ hJ0).1]
      have hge := hopt (min (J + Qbar) 1) (q * P.θL) (le_min hS0 zero_le_one) (mul_pos hq_pos hθL).le
      rw [hp_eq] at hge
      unfold Params.stepOnePayoff Params.demand Params.alpha at hge
      rw [if_pos (le_refl _), if_pos hqLH.le, sub_add_cancel,
        min_eq_left (min_le_left (J + Qbar) 1), min_eq_right (min_le_right (J + Qbar) 1)] at hge
      have hR1 := hmin_eq_of_pay (q * P.θL) 1 (J + Qbar) R zero_le_one (le_min hQo0 hS0)
        (min_le_right _ _) hwL (by rw [min_comm 1 (J + Qbar)]; linarith)
      rwa [min_comm 1 (J + Qbar)] at hR1
    let S0 := (q * P.θH - w) * P.αb / (q * P.θL - w)
    have hS0_lt_min : S0 < min (I + Qbar) 1 := by
      dsimp [S0]
      rw [div_lt_iff₀ hwL0, mul_comm _ (q * P.θL - w)]
      have hmin_ab : min P.αb (I + Qbar) = P.αb := min_eq_left (by linarith)
      rwa [hmin_ab] at hBrL
    let J_lo := max P.αg (S0 - Qbar)
    let J_hi := min I (1 - Qbar)
    have hJlo_lt_Jhi : J_lo < J_hi := by
      have hS0_lt_IQ : S0 < I + Qbar := lt_of_lt_of_le hS0_lt_min (min_le_left _ _)
      have hS0_lt_1 : S0 < 1 := lt_of_lt_of_le hS0_lt_min (min_le_right _ _)
      exact max_lt (lt_min hI_gt (by linarith)) (lt_min (by linarith) (by linarith))
    let J' := (J_lo + J_hi) / 2
    have hJ'_gt_lo : J_lo < J' := by dsimp [J']; linarith
    have hJ'_lt_hi : J' < J_hi := by dsimp [J']; linarith
    have hJ'_ag : P.αg < J' := lt_of_le_of_lt (le_max_left _ _) hJ'_gt_lo
    have hJ'0 : 0 ≤ J' := (lt_trans hαg0 hJ'_ag).le
    have hJ'_lt_I : J' < I := lt_of_lt_of_le hJ'_lt_hi (min_le_left _ _)
    have hJ'_lt_1Q : J' < 1 - Qbar := lt_of_lt_of_le hJ'_lt_hi (min_le_right _ _)
    have hS0_lt_J'Q : S0 < J' + Qbar := by
      have := lt_of_le_of_lt (le_max_right _ _) hJ'_gt_lo
      linarith
    have hcmp_J' : (q * P.θH - w) * min P.αb (J' + Qbar) < (q * P.θL - w) * min (J' + Qbar) 1 := by
      rw [min_eq_left (by linarith : P.αb ≤ J' + Qbar), min_eq_left (by linarith : J' + Qbar ≤ 1)]
      have h1 : (q * P.θH - w) * P.αb = (q * P.θL - w) * S0 := by
        dsimp [S0]; rw [mul_div_cancel₀ _ hwL0.ne']
      rw [h1]
      exact mul_lt_mul_of_pos_left hS0_lt_J'Q hwL0
    have hsv_J' : σ.supplierValue P q w J' =
        ((1 - P.ρ) * w - P.cost q) * J' +
          (P.ρ * w * P.αg + (1 - P.ρ) * (w - P.cost q) * Qbar) := by
      have hRg := hR_good J' hJ'_ag.le
      have hImg : J' + σ.made q w J' .good (σ.order q w J' .good) = J' := by
        rw [(hrecv_Imade J' .good _ hJ'0).2, ← (hrecv_Imade J' .good _ hJ'0).1, hRg,
          max_eq_left hJ'_ag.le]
      have hRb : σ.recv q w J' .bad (σ.order q w J' .bad) = J' + Qbar := by
        rw [hR_bad_of_strictL J' hJ'_ag.le hcmp_J', min_eq_left (by linarith)]
      have hImb : J' + σ.made q w J' .bad (σ.order q w J' .bad) = J' + Qbar := by
        rw [(hrecv_Imade J' .bad _ hJ'0).2, ← (hrecv_Imade J' .bad _ hJ'0).1, hRb,
          max_eq_right (by linarith)]
      unfold Profile.supplierValue Profile.supplierStateValue Params.supplierState Params.prob
      rw [hRg, hImg, hRb, hImb]
      ring
    have hsv_I_val : σ.supplierValue P q w I =
        P.ρ * (w * P.αg - P.cost q * I) +
          (1 - P.ρ) * (w * min (I + Qbar) 1 - P.cost q * max I (min (I + Qbar) 1)) := by
      have hRg := hR_good I hI_gt.le
      have hImg : I + σ.made q w I .good (σ.order q w I .good) = I := by
        rw [(hrecv_Imade I .good _ hI0).2, ← (hrecv_Imade I .good _ hI0).1, hRg,
          max_eq_left hI_gt.le]
      have hRb := hR_bad_of_strictL I hI_gt.le hBrL
      have hImb : I + σ.made q w I .bad (σ.order q w I .bad) = max I (min (I + Qbar) 1) := by
        rw [(hrecv_Imade I .bad _ hI0).2, ← (hrecv_Imade I .bad _ hI0).1, hRb]
      unfold Profile.supplierValue Profile.supplierStateValue Params.supplierState Params.prob
      rw [hRg, hImg, hRb, hImb]
    have hopt_J' := hI_opt J' hJ'0
    rw [hsv_J', hsv_I_val] at hopt_J'
    rcases le_or_gt I (1 - Qbar) with hI_le1 | hI_gt1
    · rw [min_eq_left (by linarith : I + Qbar ≤ 1),
        max_eq_right (by linarith : I ≤ I + Qbar)] at hopt_J'
      have hid_I : P.ρ * (w * P.αg - P.cost q * I) +
          (1 - P.ρ) * (w * (I + Qbar) - P.cost q * (I + Qbar)) =
          ((1 - P.ρ) * w - P.cost q) * I +
            (P.ρ * w * P.αg + (1 - P.ρ) * (w - P.cost q) * Qbar) := by ring
      rw [hid_I] at hopt_J'
      have := mul_lt_mul_of_neg_left hJ'_lt_I hslope_neg
      linarith
    · rw [min_eq_right (by linarith : 1 ≤ I + Qbar)] at hopt_J'
      have hg_lt : w * P.αg - P.cost q * I < w * P.αg - P.cost q * (1 - Qbar) := by
        have := mul_lt_mul_of_pos_left hI_gt1 hc_pos; linarith
      have hb_le : w * 1 - P.cost q * max I 1 ≤ w * 1 - P.cost q * 1 := by
        have := mul_le_mul_of_nonneg_left (le_max_right I 1) hc_pos.le; linarith
      have h_le_1Q : P.ρ * (w * P.αg - P.cost q * I) +
          (1 - P.ρ) * (w * 1 - P.cost q * max I 1) <
          ((1 - P.ρ) * w - P.cost q) * (1 - Qbar) +
            (P.ρ * w * P.αg + (1 - P.ρ) * (w - P.cost q) * Qbar) := by
        have := mul_lt_mul_of_pos_left hg_lt hρ0
        have := mul_le_mul_of_nonneg_left hb_le h1ρ.le
        linarith
      have := mul_lt_mul_of_neg_left hJ'_lt_1Q hslope_neg
      linarith

private lemma ub_char_med_L2_tb (P : Params) (hStand : P.Standing)
    (Qbar : ℝ) (hQ0 : 0 ≤ Qbar) (hQ1 : Qbar < 1 - P.αg)
    (hDS : 0 < P.ρ * P.αg + (1 - P.ρ) * (P.αg + Qbar))
    (σ : Profile) (hpost : IsPostInventorySPE P Qbar σ)
    (q w : ℝ) (hq_pos : 0 < q) (hcw : P.cost q ≤ w) (hw_lt_c1ρ : w < P.cost q / (1 - P.ρ))
    (hwL : w < q * P.θL)
    (hI0 : 0 ≤ σ.inv q w)
    (hI_opt : ∀ I' : ℝ, 0 ≤ I' → σ.supplierValue P q w I' ≤ σ.supplierValue P q w (σ.inv q w))
    (hsv_I_nonneg : 0 ≤ σ.supplierValue P q w (σ.inv q w))
    (hS_pos : 0 < σ.inv q w + Qbar)
    (hBrL : (q * P.θH - w) * min P.αb (σ.inv q w + Qbar) <
      (q * P.θL - w) * min (σ.inv q w + Qbar) 1) :
    σ.retailerValue P q w ≤ max (P.V_OS Qbar) P.V_OO ∧
    (σ.retailerValue P q w = max (P.V_OS Qbar) P.V_OO →
      P.V_OO ≤ P.V_OS Qbar ∧ σ.retailerValue P q w = P.V_OS Qbar ∧
      σ.supplierValue P q w (σ.inv q w) = 0 ∧
      q = P.Y (P.αg + Qbar) / (2 * P.k) ∧ w = P.Y (P.αg + Qbar) ^ 2 / (4 * P.k) ∧
      σ.priceAfter q w (σ.inv q w) .good (σ.order q w (σ.inv q w) .good) =
        P.Y (P.αg + Qbar) * P.θH / (2 * P.k) ∧
      σ.priceAfter q w (σ.inv q w) .bad (σ.order q w (σ.inv q w) .bad) =
        P.Y (P.αg + Qbar) * P.θL / (2 * P.k) ∧
      σ.inv q w = P.αg ∧
      σ.recv q w (σ.inv q w) .good (σ.order q w (σ.inv q w) .good) = P.αg ∧
      σ.recv q w (σ.inv q w) .bad (σ.order q w (σ.inv q w) .bad) = P.αg + Qbar) := by
  rcases hStand with ⟨hθL, hθLH, hk, hρ0, hρ1, hαb0, hαb_lt, hαg_gt, hαg1⟩
  have hStand : P.Standing := ⟨hθL, hθLH, hk, hρ0, hρ1, hαb0, hαb_lt, hαg_gt, hαg1⟩
  have hθH : 0 < P.θH := lt_trans hθL hθLH
  have hαg0 : 0 < P.αg := pos_of_mul_pos_left (lt_trans hθL hαg_gt) hθH.le
  have hαb_αg : P.αb < P.αg := lt_of_mul_lt_mul_right (lt_trans hαb_lt hαg_gt) hθH.le
  have hαb1 : P.αb < 1 := lt_trans hαb_αg hαg1
  have h1ρ : 0 < 1 - P.ρ := sub_pos.mpr hρ1
  have hq : 0 ≤ q := hq_pos.le
  have hc_pos : 0 < P.cost q := mul_pos hk (pow_pos hq_pos 2)
  have hw : 0 ≤ w := (lt_of_lt_of_le hc_pos hcw).le
  have hwH : w < q * P.θH := lt_trans hwL (mul_lt_mul_of_pos_left hθLH hq_pos)
  have hwH0 : 0 < q * P.θH - w := sub_pos.mpr hwH
  have hwL0 : 0 < q * P.θL - w := sub_pos.mpr hwL
  let I := σ.inv q w
  let S := I + Qbar
  let Qg := σ.order q w I .good
  let Qb := σ.order q w I .bad
  obtain ⟨hQg0, _⟩ := hpost.2.2 q w I .good hq hw hI0
  obtain ⟨hQb0, _⟩ := hpost.2.2 q w I .bad hq hw hI0
  have hmade_bds : ∀ s : State, ∀ Q : ℝ, 0 ≤ Q →
      0 ≤ σ.made q w I s Q ∧ σ.made q w I s Q ≤ Qbar ∧
      0 ≤ σ.recv q w I s Q ∧ σ.recv q w I s Q ≤ S := by
    intro s Q hQ
    unfold Profile.made Profile.recv inSeason received
    rcases le_or_gt Q I with hQI | hIQ
    · rw [if_pos hQI, if_pos hQI]; exact ⟨le_refl 0, hQ0, hQ, by dsimp [S]; linarith⟩
    · rw [if_neg (not_le_of_gt hIQ), if_neg (not_le_of_gt hIQ)]
      obtain ⟨hr0, hrQ, _⟩ := hpost.2.1 q w I s Q hq hw hI0 hIQ
      exact ⟨hr0, hrQ, le_min (add_nonneg hI0 hr0) hQ, le_trans (min_le_left _ _) (by dsimp [S]; linarith)⟩
  obtain ⟨hmg0, hmgQ, hRg0, hRgS⟩ := hmade_bds .good Qg hQg0
  obtain ⟨hmb0, hmbQ, hRb0, hRbS⟩ := hmade_bds .bad Qb hQb0
  let Rg := σ.recv q w I .good Qg
  let Rb := σ.recv q w I .bad Qb
  let pg := σ.priceAfter q w I .good Qg
  let pb := σ.priceAfter q w I .bad Qb
  obtain ⟨hpg0, _⟩ := hpost.1 q w I .good Qg (σ.made q w I .good Qg) hq hw hI0 hQg0 hmg0 hmgQ
  obtain ⟨hpb0, _⟩ := hpost.1 q w I .bad Qb (σ.made q w I .bad Qb) hq hw hI0 hQb0 hmb0 hmbQ
  have hrule := retailer_stage_rule P hStand q w S hq_pos hw hwH hS_pos.le
  have hov_step : ∀ s : State,
      σ.orderValue P q w I s (σ.order q w I s) =
        P.stepOnePayoff q w (P.alpha s) S (σ.recv q w I s (σ.order q w I s))
          (σ.priceAfter q w I s (σ.order q w I s)) := by
    rintro (_ | _)
    · unfold Profile.orderValue Params.retailerState Params.stepOnePayoff; rw [min_eq_left hRgS]
    · unfold Profile.orderValue Params.retailerState Params.stepOnePayoff; rw [min_eq_left hRbS]
  have hI_le_ag : I ≤ P.αg :=
    inv_le_ag_of_lt_oo_tb P hStand Qbar hQ0 hQ1 σ hpost q w hq_pos hcw hw_lt_c1ρ
      hwL hI0 hI_opt hsv_I_nonneg hBrL
  let S_Q := P.αg + Qbar
  have hS_le_SQ : S ≤ S_Q := by dsimp [S, S_Q]; linarith
  have hS_le1 : S ≤ 1 := by dsimp [S, S_Q] at hS_le_SQ; linarith
  have hminS1 : min S 1 = S := min_eq_left hS_le1
  have hov_good_ub : σ.orderValue P q w I .good Qg ≤ (q * P.θH - w) * min P.αg S := by
    rw [hov_step .good]
    have h1 := (hrule.1 P.αg hαg0.le hαg1.le).2 ⟨Rg, pg, hRg0, hpg0, rfl⟩
    have hvH0 : 0 ≤ (q * P.θH - w) * min P.αg S := mul_nonneg hwH0.le (le_min hαg0.le hS_pos.le)
    have hvL_le : (q * P.θL - w) * min S 1 ≤ (q * P.θH - w) * min P.αg S := by
      rcases le_or_gt S P.αg with hSα | hSα
      · rw [hminS1, min_eq_right hSα]
        exact mul_le_mul_of_nonneg_right (by have := mul_lt_mul_of_pos_left hθLH hq_pos; linarith) hS_pos.le
      · rw [hminS1, min_eq_left hSα.le]
        have hle1 : (q * P.θL - w) * S ≤ q * P.θL - w := by
          have := mul_le_mul_of_nonneg_left hS_le1 hwL0.le; linarith
        have h2 : q * P.θL < q * (P.αg * P.θH) := mul_lt_mul_of_pos_left hαg_gt hq_pos
        have h3 : w * P.αg ≤ w := by have := mul_le_mul_of_nonneg_left hαg1.le hw; linarith
        linarith
    rwa [max_eq_left hvL_le, max_eq_left hvH0] at h1
  have hb_max : σ.orderValue P q w I .bad Qb ≤ (q * P.θL - w) * min S 1 := by
    rw [hov_step .bad]
    have h1 := (hrule.1 P.αb hαb0.le hαb1.le).2 ⟨Rb, pb, hRb0, hpb0, rfl⟩
    have hvH0 : 0 ≤ (q * P.θH - w) * min P.αb S := mul_nonneg hwH0.le (le_min hαb0.le hS_pos.le)
    rw [max_eq_left (le_trans hvH0 (le_max_left _ _)), max_eq_right hBrL.le] at h1
    exact h1
  have hg_s1 : (q * P.θH - w) * min P.αg S ≤ (q * P.θH - w) * P.αg :=
    mul_le_mul_of_nonneg_left (min_le_left _ _) hwH0.le
  have hg_s2 : (q * P.θH - w) * P.αg ≤ (q * P.θH - P.cost q) * P.αg :=
    mul_le_mul_of_nonneg_right (by linarith) hαg0.le
  have hb_s1 : (q * P.θL - w) * min S 1 ≤ (q * P.θL - w) * S_Q := by
    rw [hminS1]; exact mul_le_mul_of_nonneg_left hS_le_SQ hwL0.le
  have hb_s2 : (q * P.θL - w) * S_Q ≤ (q * P.θL - P.cost q) * S_Q :=
    mul_le_mul_of_nonneg_right (by linarith) (by dsimp [S_Q]; linarith)
  have hlin := lin_id_os_tb P Qbar q hk hQ1.le hDS
  have hsq_nonneg : 0 ≤ (P.ρ * P.αg + (1 - P.ρ) * S_Q) * P.k *
      (q - P.Y S_Q / (2 * P.k)) ^ 2 :=
    mul_nonneg (mul_nonneg hDS.le hk.le) (sq_nonneg _)
  have hrv_ub_sum : σ.retailerValue P q w ≤
      P.ρ * ((q * P.θH - P.cost q) * P.αg) + (1 - P.ρ) * ((q * P.θL - P.cost q) * S_Q) := by
    unfold Profile.retailerValue Params.prob
    change P.ρ * σ.orderValue P q w I .good Qg +
      (1 - P.ρ) * σ.orderValue P q w I .bad Qb ≤ _
    have := mul_le_mul_of_nonneg_left
      (le_trans hov_good_ub (le_trans hg_s1 hg_s2)) hρ0.le
    have := mul_le_mul_of_nonneg_left
      (le_trans hb_max (le_trans hb_s1 hb_s2)) h1ρ.le
    linarith
  have hrv_le_VOS : σ.retailerValue P q w ≤ P.V_OS Qbar := by
    dsimp [S_Q] at hrv_ub_sum hsq_nonneg; linarith
  refine ⟨le_trans hrv_le_VOS (le_max_left _ _), fun hrv_eq => ?_⟩
  have hVOO_le_VOS : P.V_OO ≤ P.V_OS Qbar :=
    le_trans (le_max_right _ _) (hrv_eq ▸ hrv_le_VOS)
  have hrv_eq_VOS : σ.retailerValue P q w = P.V_OS Qbar :=
    le_antisymm hrv_le_VOS (hrv_eq.symm ▸ le_max_left _ _)
  have hsq_zero : (P.ρ * P.αg + (1 - P.ρ) * S_Q) * P.k *
      (q - P.Y S_Q / (2 * P.k)) ^ 2 = 0 := by
    dsimp [S_Q] at hrv_ub_sum ⊢; linarith
  have hq_eq : q = P.Y (P.αg + Qbar) / (2 * P.k) := by
    have h1 : (q - P.Y S_Q / (2 * P.k)) ^ 2 = 0 := by
      rcases mul_eq_zero.mp hsq_zero with h0 | h0
      · exfalso; have := mul_pos hDS hk; dsimp [S_Q] at h0; linarith
      · exact h0
    dsimp [S_Q] at h1
    linarith [sq_eq_zero_iff.mp h1]
  have hov_g_eq : σ.orderValue P q w I .good Qg = (q * P.θH - P.cost q) * P.αg := by
    unfold Profile.retailerValue Params.prob at hrv_eq_VOS
    change P.ρ * σ.orderValue P q w I .good Qg +
      (1 - P.ρ) * σ.orderValue P q w I .bad Qb = P.V_OS Qbar at hrv_eq_VOS
    by_contra hne
    have hlt : σ.orderValue P q w I .good Qg < (q * P.θH - P.cost q) * P.αg :=
      lt_of_le_of_ne (le_trans hov_good_ub (le_trans hg_s1 hg_s2)) hne
    have := mul_lt_mul_of_pos_left hlt hρ0
    have := mul_le_mul_of_nonneg_left
      (le_trans hb_max (le_trans hb_s1 hb_s2)) h1ρ.le
    dsimp [S_Q] at *; linarith
  have hov_b_eq : σ.orderValue P q w I .bad Qb = (q * P.θL - P.cost q) * S_Q := by
    unfold Profile.retailerValue Params.prob at hrv_eq_VOS
    change P.ρ * σ.orderValue P q w I .good Qg +
      (1 - P.ρ) * σ.orderValue P q w I .bad Qb = P.V_OS Qbar at hrv_eq_VOS
    by_contra hne
    have hlt : σ.orderValue P q w I .bad Qb < (q * P.θL - P.cost q) * S_Q :=
      lt_of_le_of_ne (le_trans hb_max (le_trans hb_s1 hb_s2)) hne
    have := mul_le_mul_of_nonneg_left
      (le_trans hov_good_ub (le_trans hg_s1 hg_s2)) hρ0.le
    have := mul_lt_mul_of_pos_left hlt h1ρ
    dsimp [S_Q] at *; linarith
  have hw_eq_c : w = P.cost q := by
    by_contra hne
    have hlt : P.cost q < w := lt_of_le_of_ne hcw (Ne.symm hne)
    have : (q * P.θH - w) * P.αg < (q * P.θH - P.cost q) * P.αg :=
      mul_lt_mul_of_pos_right (by linarith) hαg0
    linarith
  have hw_eq : w = P.Y (P.αg + Qbar) ^ 2 / (4 * P.k) := by
    rw [hw_eq_c, hq_eq]; unfold Params.cost; field_simp [hk.ne']; ring
  have hS_eq_SQ : S = S_Q := by
    have h1 : (q * P.θL - w) * min S 1 = (q * P.θL - w) * S_Q := by
      have : (q * P.θL - P.cost q) * S_Q = (q * P.θL - w) * S_Q := by rw [hw_eq_c]
      linarith
    rw [hminS1] at h1
    have h2 : (q * P.θL - w) * (S_Q - S) = 0 := by linarith
    rcases mul_eq_zero.mp h2 with h0 | h0 <;> linarith
  have hI_eq : I = P.αg := by dsimp [S, S_Q] at hS_eq_SQ; linarith
  have hsv_eq0 : σ.supplierValue P q w I = 0 := by
    have hw_mul : ∀ x : ℝ, w * x = P.cost q * x := fun x => by rw [hw_eq_c]
    have hst : ∀ s : State, σ.supplierStateValue P q w I s ≤ 0 := by
      intro s
      unfold Profile.supplierStateValue Params.supplierState Profile.recv Profile.made
        received inSeason
      rcases le_or_gt (σ.order q w I s) I with hQI | hIQ
      · rw [if_pos hQI, if_pos hQI, add_zero, hw_mul]
        have := mul_le_mul_of_nonneg_left hQI hc_pos.le; linarith
      · have hropt := (hpost.2.1 q w I s (σ.order q w I s) hq hw hI0 hIQ).2.2
          0 (le_refl 0) hQ0
        unfold Params.supplierState received at hropt
        simp only [if_neg (not_le_of_gt hIQ), add_zero, min_eq_left hIQ.le, hw_mul] at hropt
        simp only [if_neg (not_le_of_gt hIQ), hw_mul]
        have hle_min : P.cost q * min (I + σ.react q w I s (σ.order q w I s))
            (σ.order q w I s) ≤ P.cost q * (I + σ.react q w I s (σ.order q w I s)) :=
          mul_le_mul_of_nonneg_left (min_le_left _ _) hc_pos.le
        have hII_le : I + σ.react q w I s (σ.order q w I s) ≤ σ.order q w I s := by
          by_contra hc
          have hgt : σ.order q w I s < I + σ.react q w I s (σ.order q w I s) :=
            lt_of_not_ge hc
          rw [min_eq_right hgt.le] at hropt
          have := mul_lt_mul_of_pos_left hgt hc_pos
          linarith
        linarith
    unfold Profile.supplierValue Params.prob at hsv_I_nonneg ⊢
    have := mul_nonpos_of_nonneg_of_nonpos hρ0.le (hst .good)
    have := mul_nonpos_of_nonneg_of_nonpos h1ρ.le (hst .bad)
    linarith
  have hmin_agS : min P.αg S = P.αg := min_eq_left (by dsimp [S, S_Q] at hS_eq_SQ ⊢; linarith)
  have hpay_g : P.stepOnePayoff q w P.αg S Rg pg = (q * P.θH - w) * P.αg := by
    have hstep := hov_step .good
    rw [Params.alpha] at hstep
    change P.stepOnePayoff q w P.αg S Rg pg = (q * P.θH - w) * P.αg
    rw [← hstep, hov_g_eq, hw_eq_c]
  have hopt_g : ∀ Q' p' : ℝ, 0 ≤ Q' → 0 ≤ p' →
      P.stepOnePayoff q w P.αg S Q' p' ≤ P.stepOnePayoff q w P.αg S Rg pg := by
    intro Q' p' hQ' hp'
    have h1 := (hrule.1 P.αg hαg0.le hαg1.le).2 ⟨Q', p', hQ', hp', rfl⟩
    have hvL_le : (q * P.θL - w) * min S 1 ≤ (q * P.θH - w) * min P.αg S := by
      rw [hminS1, hmin_agS]
      have hle1 : (q * P.θL - w) * S ≤ q * P.θL - w := by
        have := mul_le_mul_of_nonneg_left hS_le1 hwL0.le; linarith
      have h2 : q * P.θL < q * (P.αg * P.θH) := mul_lt_mul_of_pos_left hαg_gt hq_pos
      have h3 : w * P.αg ≤ w := by
        have := mul_le_mul_of_nonneg_left hαg1.le hw; linarith
      linarith
    have hvH0 : 0 ≤ (q * P.θH - w) * min P.αg S :=
      mul_nonneg hwH0.le (le_min hαg0.le hS_pos.le)
    rw [max_eq_left hvL_le, max_eq_left hvH0, hmin_agS, ← hpay_g] at h1
    exact h1
  have hpg_eq : pg = P.Y (P.αg + Qbar) * P.θH / (2 * P.k) := by
    rw [hrule.2.1 hS_pos Rg pg hRg0 hpg0 hopt_g, hq_eq, div_mul_eq_mul_div]
  have hRg_eq : Rg = P.αg := by
    have hpay := hpay_g
    have hp_raw : pg = q * P.θH := hrule.2.1 hS_pos Rg pg hRg0 hpg0 hopt_g
    have hqLH : q * P.θL < q * P.θH := mul_lt_mul_of_pos_left hθLH hq_pos
    unfold Params.stepOnePayoff Params.demand at hpay
    rw [hp_raw, if_neg (not_le_of_gt hqLH), if_pos (le_refl _), zero_add,
      min_eq_left hRgS] at hpay
    rcases lt_trichotomy Rg P.αg with hlt | heq | hgt
    · exfalso
      rw [min_eq_right hlt.le] at hpay
      have := mul_lt_mul_of_pos_left hlt hwH0; linarith
    · exact heq
    · exfalso
      rw [min_eq_left hgt.le] at hpay
      have hw_pos : 0 < w := by rw [hw_eq_c]; exact hc_pos
      have := mul_lt_mul_of_pos_left hgt hw_pos; linarith
  have hpay_b : P.stepOnePayoff q w P.αb S Rb pb = (q * P.θL - w) * S := by
    have hstep := hov_step .bad
    rw [Params.alpha] at hstep
    change P.stepOnePayoff q w P.αb S Rb pb = (q * P.θL - w) * S
    rw [← hstep, hov_b_eq, hw_eq_c, hS_eq_SQ]
  have hopt_b : ∀ Q' p' : ℝ, 0 ≤ Q' → 0 ≤ p' →
      P.stepOnePayoff q w P.αb S Q' p' ≤ P.stepOnePayoff q w P.αb S Rb pb := by
    intro Q' p' hQ' hp'
    have h1 := (hrule.1 P.αb hαb0.le hαb1.le).2 ⟨Q', p', hQ', hp', rfl⟩
    have hvL0 : 0 ≤ (q * P.θL - w) * min S 1 :=
      mul_nonneg hwL0.le (le_min hS_pos.le zero_le_one)
    rw [max_eq_right hBrL.le, max_eq_left hvL0, hminS1, ← hpay_b] at h1
    exact h1
  have hpb_eq : pb = P.Y (P.αg + Qbar) * P.θL / (2 * P.k) := by
    rw [hrule.2.2.1 hBrL Rb pb hRb0 hpb0 hopt_b, hq_eq, div_mul_eq_mul_div]
  have hRb_eq : Rb = P.αg + Qbar := by
    have hpay := hpay_b
    have hp_raw : pb = q * P.θL := hrule.2.2.1 hBrL Rb pb hRb0 hpb0 hopt_b
    have hqLH : q * P.θL < q * P.θH := mul_lt_mul_of_pos_left hθLH hq_pos
    unfold Params.stepOnePayoff Params.demand at hpay
    rw [hp_raw, if_pos (le_refl _), if_pos hqLH.le, sub_add_cancel,
      min_eq_left hRbS, min_eq_right (le_trans hRbS hS_le1)] at hpay
    have hSL : (q * P.θL - w) * (S - Rb) = 0 := by linarith
    have hRS : Rb = S := by rcases mul_eq_zero.mp hSL with h0 | h0 <;> linarith
    rw [hRS, hS_eq_SQ]
  exact ⟨hVOO_le_VOS, hrv_eq_VOS, hsv_eq0, hq_eq, hw_eq, hpg_eq, hpb_eq, hI_eq,
    hRg_eq, hRb_eq⟩

private lemma ub_char_med_L1b_tb (P : Params) (hStand : P.Standing)
    (Qbar : ℝ) (hQ0 : 0 ≤ Qbar) (hQ1 : Qbar < 1 - P.αg)
    (σ : Profile) (hpost : IsPostInventorySPE P Qbar σ)
    (q w : ℝ) (hq_pos : 0 < q) (hw_pos : 0 < w)
    (hwL : w < q * P.θL) (hI0 : 0 ≤ σ.inv q w)
    (hq_eq : q = (1 - P.ρ) * P.X / (2 * P.k))
    (hw_eq : w = (1 - P.ρ) * P.X ^ 2 / (4 * P.k))
    (hI_eq : σ.inv q w = 1 - Qbar)
    (hBrL : (q * P.θH - w) * min P.αb (σ.inv q w + Qbar) <
      (q * P.θL - w) * min (σ.inv q w + Qbar) 1)
    (hov_g_eq : σ.orderValue P q w (σ.inv q w) .good (σ.order q w (σ.inv q w) .good) =
      (q * P.θH - w) * P.αg)
    (hov_b_eq : σ.orderValue P q w (σ.inv q w) .bad (σ.order q w (σ.inv q w) .bad) =
      q * P.θL - w) :
    σ.supplierValue P q w (σ.inv q w) =
      P.ρ * (1 - P.ρ) * (P.αg + (1 - P.ρ) * Qbar) * P.X ^ 2 / (4 * P.k) ∧
    σ.priceAfter q w (σ.inv q w) .good (σ.order q w (σ.inv q w) .good) =
      (1 - P.ρ) * P.X * P.θH / (2 * P.k) ∧
    σ.priceAfter q w (σ.inv q w) .bad (σ.order q w (σ.inv q w) .bad) =
      (1 - P.ρ) * P.X * P.θL / (2 * P.k) ∧
    σ.recv q w (σ.inv q w) .good (σ.order q w (σ.inv q w) .good) = P.αg ∧
    σ.recv q w (σ.inv q w) .bad (σ.order q w (σ.inv q w) .bad) = 1 := by
  rcases hStand with ⟨hθL, hθLH, hk, hρ0, hρ1, hαb0, hαb_lt, hαg_gt, hαg1⟩
  have hStand : P.Standing := ⟨hθL, hθLH, hk, hρ0, hρ1, hαb0, hαb_lt, hαg_gt, hαg1⟩
  have hθH : 0 < P.θH := lt_trans hθL hθLH
  have hαg0 : 0 < P.αg := pos_of_mul_pos_left (lt_trans hθL hαg_gt) hθH.le
  have hαb_αg : P.αb < P.αg := lt_of_mul_lt_mul_right (lt_trans hαb_lt hαg_gt) hθH.le
  have hαb1 : P.αb < 1 := lt_trans hαb_αg hαg1
  have h1ρ : 0 < 1 - P.ρ := sub_pos.mpr hρ1
  have hD1 : 0 < P.ρ * P.αg + 1 - P.ρ := by
    have : 0 < P.ρ * P.αg := mul_pos hρ0 hαg0
    linarith
  obtain ⟨hc_oo, _hc1ρ_oo, _hval_oo, hsv_oo_alg⟩ := val_qoo_tb P Qbar hk h1ρ hD1
  have hq : 0 ≤ q := hq_pos.le
  have hw : 0 ≤ w := hw_pos.le
  have hwH : w < q * P.θH := lt_trans hwL (mul_lt_mul_of_pos_left hθLH hq_pos)
  have hwH0 : 0 < q * P.θH - w := sub_pos.mpr hwH
  have hwL0 : 0 < q * P.θL - w := sub_pos.mpr hwL
  let I := σ.inv q w
  let S := I + Qbar
  have hS_eq1 : S = 1 := by dsimp [S, I]; rw [hI_eq]; ring
  have hS_pos : 0 < S := by rw [hS_eq1]; exact zero_lt_one
  have hminS1 : min S 1 = 1 := by rw [hS_eq1, min_self]
  have hmin_agS : min P.αg S = P.αg := min_eq_left (by rw [hS_eq1]; exact hαg1.le)
  let Qg := σ.order q w I .good
  let Qb := σ.order q w I .bad
  obtain ⟨hQg0, _⟩ := hpost.2.2 q w I .good hq hw hI0
  obtain ⟨hQb0, _⟩ := hpost.2.2 q w I .bad hq hw hI0
  have hmade_bds : ∀ s : State, ∀ Q : ℝ, 0 ≤ Q →
      0 ≤ σ.made q w I s Q ∧ σ.made q w I s Q ≤ Qbar ∧
      0 ≤ σ.recv q w I s Q ∧ σ.recv q w I s Q ≤ S := by
    intro s Q hQ
    unfold Profile.made Profile.recv inSeason received
    rcases le_or_gt Q I with hQI | hIQ
    · rw [if_pos hQI, if_pos hQI]; exact ⟨le_refl 0, hQ0, hQ, by dsimp [S]; linarith⟩
    · rw [if_neg (not_le_of_gt hIQ), if_neg (not_le_of_gt hIQ)]
      obtain ⟨hr0, hrQ, _⟩ := hpost.2.1 q w I s Q hq hw hI0 hIQ
      exact ⟨hr0, hrQ, le_min (add_nonneg hI0 hr0) hQ, le_trans (min_le_left _ _) (by dsimp [S]; linarith)⟩
  obtain ⟨hmg0, hmgQ, hRg0, hRgS⟩ := hmade_bds .good Qg hQg0
  obtain ⟨hmb0, hmbQ, hRb0, hRbS⟩ := hmade_bds .bad Qb hQb0
  let Rg := σ.recv q w I .good Qg
  let Rb := σ.recv q w I .bad Qb
  let pg := σ.priceAfter q w I .good Qg
  let pb := σ.priceAfter q w I .bad Qb
  obtain ⟨hpg0, _⟩ := hpost.1 q w I .good Qg (σ.made q w I .good Qg) hq hw hI0 hQg0 hmg0 hmgQ
  obtain ⟨hpb0, _⟩ := hpost.1 q w I .bad Qb (σ.made q w I .bad Qb) hq hw hI0 hQb0 hmb0 hmbQ
  have hrule := retailer_stage_rule P hStand q w S hq_pos hw hwH hS_pos.le
  have hov_step : ∀ s : State,
      σ.orderValue P q w I s (σ.order q w I s) =
        P.stepOnePayoff q w (P.alpha s) S (σ.recv q w I s (σ.order q w I s))
          (σ.priceAfter q w I s (σ.order q w I s)) := by
    rintro (_ | _)
    · unfold Profile.orderValue Params.retailerState Params.stepOnePayoff; rw [min_eq_left hRgS]
    · unfold Profile.orderValue Params.retailerState Params.stepOnePayoff; rw [min_eq_left hRbS]
  have hpay_g : P.stepOnePayoff q w P.αg S Rg pg = (q * P.θH - w) * P.αg := by
    have hstep := hov_step .good
    rw [Params.alpha] at hstep
    change P.stepOnePayoff q w P.αg S Rg pg = (q * P.θH - w) * P.αg
    rw [← hstep, hov_g_eq]
  have hopt_g : ∀ Q' p' : ℝ, 0 ≤ Q' → 0 ≤ p' →
      P.stepOnePayoff q w P.αg S Q' p' ≤ P.stepOnePayoff q w P.αg S Rg pg := by
    intro Q' p' hQ' hp'
    have h1 := (hrule.1 P.αg hαg0.le hαg1.le).2 ⟨Q', p', hQ', hp', rfl⟩
    have hvL_le : (q * P.θL - w) * min S 1 ≤ (q * P.θH - w) * min P.αg S := by
      rw [hminS1, hmin_agS]
      have h2 : q * P.θL < q * (P.αg * P.θH) := mul_lt_mul_of_pos_left hαg_gt hq_pos
      have h3 : w * P.αg ≤ w := by
        have := mul_le_mul_of_nonneg_left hαg1.le hw; linarith
      linarith
    have hvH0 : 0 ≤ (q * P.θH - w) * min P.αg S :=
      mul_nonneg hwH0.le (le_min hαg0.le hS_pos.le)
    rw [max_eq_left hvL_le, max_eq_left hvH0, hmin_agS, ← hpay_g] at h1
    exact h1
  have hpg_eq : pg = (1 - P.ρ) * P.X * P.θH / (2 * P.k) := by
    rw [hrule.2.1 hS_pos Rg pg hRg0 hpg0 hopt_g, hq_eq, div_mul_eq_mul_div]
  have hRg_eq : Rg = P.αg := by
    have hpay := hpay_g
    have hp_raw : pg = q * P.θH := hrule.2.1 hS_pos Rg pg hRg0 hpg0 hopt_g
    have hqLH : q * P.θL < q * P.θH := mul_lt_mul_of_pos_left hθLH hq_pos
    unfold Params.stepOnePayoff Params.demand at hpay
    rw [hp_raw, if_neg (not_le_of_gt hqLH), if_pos (le_refl _), zero_add,
      min_eq_left hRgS] at hpay
    rcases lt_trichotomy Rg P.αg with hlt | heq | hgt
    · exfalso
      rw [min_eq_right hlt.le] at hpay
      have := mul_lt_mul_of_pos_left hlt hwH0; linarith
    · exact heq
    · exfalso
      rw [min_eq_left hgt.le] at hpay
      have := mul_lt_mul_of_pos_left hgt hw_pos; linarith
  have hpay_b : P.stepOnePayoff q w P.αb S Rb pb = q * P.θL - w := by
    have hstep := hov_step .bad
    rw [Params.alpha] at hstep
    change P.stepOnePayoff q w P.αb S Rb pb = q * P.θL - w
    rw [← hstep, hov_b_eq]
  have hopt_b : ∀ Q' p' : ℝ, 0 ≤ Q' → 0 ≤ p' →
      P.stepOnePayoff q w P.αb S Q' p' ≤ P.stepOnePayoff q w P.αb S Rb pb := by
    intro Q' p' hQ' hp'
    have h1 := (hrule.1 P.αb hαb0.le hαb1.le).2 ⟨Q', p', hQ', hp', rfl⟩
    have hvL0 : 0 ≤ (q * P.θL - w) * min S 1 :=
      mul_nonneg hwL0.le (le_min hS_pos.le zero_le_one)
    rw [max_eq_right hBrL.le, max_eq_left hvL0, hminS1, mul_one, ← hpay_b] at h1
    exact h1
  have hpb_eq : pb = (1 - P.ρ) * P.X * P.θL / (2 * P.k) := by
    rw [hrule.2.2.1 hBrL Rb pb hRb0 hpb0 hopt_b, hq_eq, div_mul_eq_mul_div]
  have hRb_eq : Rb = 1 := by
    have hpay := hpay_b
    have hp_raw : pb = q * P.θL := hrule.2.2.1 hBrL Rb pb hRb0 hpb0 hopt_b
    have hqLH : q * P.θL < q * P.θH := mul_lt_mul_of_pos_left hθLH hq_pos
    unfold Params.stepOnePayoff Params.demand at hpay
    rw [hp_raw, if_pos (le_refl _), if_pos hqLH.le, sub_add_cancel,
      min_eq_left hRbS] at hpay
    rcases lt_trichotomy Rb 1 with hlt | heq | hgt
    · exfalso
      rw [min_eq_right hlt.le] at hpay
      have := mul_lt_mul_of_pos_left hlt hwL0; linarith
    · exact heq
    · exfalso
      rw [min_eq_left hgt.le] at hpay
      have := mul_lt_mul_of_pos_left hgt hw_pos; linarith
  have hQg_le_I : Qg ≤ I := by
    by_contra hc
    have hgt : I < Qg := lt_of_not_ge hc
    have hr0 := (hpost.2.1 q w I .good Qg hq hw hI0 hgt).1
    have hrec_ge : I ≤ Rg := by
      change I ≤ received I Qg (σ.react q w I .good Qg)
      unfold received
      rw [if_neg (not_le_of_gt hgt)]
      exact le_min (by linarith) hgt.le
    have hI_gt_ag : P.αg < I := by dsimp [I]; rw [hI_eq]; linarith
    linarith
  have hmg_eq0 : σ.made q w I .good Qg = 0 := by
    unfold Profile.made inSeason; rw [if_pos hQg_le_I]
  have hImb_eq1 : I + σ.made q w I .bad Qb = 1 := by
    have hle1 : I + σ.made q w I .bad Qb ≤ 1 := by
      have : I + Qbar = 1 := hS_eq1
      linarith
    have hge1 : 1 ≤ I + σ.made q w I .bad Qb := by
      have hrb : σ.recv q w I .bad Qb = 1 := hRb_eq
      unfold Profile.recv received at hrb
      unfold Profile.made inSeason
      rcases le_or_gt Qb I with h1 | h1
      · rw [if_pos h1] at hrb ⊢; linarith
      · rw [if_neg (not_le_of_gt h1)] at hrb ⊢
        have := min_le_left (I + σ.react q w I .bad Qb) Qb; linarith
    exact le_antisymm hle1 hge1
  have hsv_eq : σ.supplierValue P q w I =
      P.ρ * (1 - P.ρ) * (P.αg + (1 - P.ρ) * Qbar) * P.X ^ 2 / (4 * P.k) := by
    unfold Profile.supplierValue Profile.supplierStateValue Params.supplierState Params.prob
    change P.ρ * (w * Rg - P.cost q * (I + σ.made q w I .good Qg)) +
      (1 - P.ρ) * (w * Rb - P.cost q * (I + σ.made q w I .bad Qb)) = _
    rw [hRg_eq, hmg_eq0, add_zero, hRb_eq, hImb_eq1, show I = 1 - Qbar from hI_eq,
      mul_one, mul_one, hq_eq, hc_oo, hw_eq]
    exact hsv_oo_alg
  exact ⟨hsv_eq, hpg_eq, hpb_eq, hRg_eq, hRb_eq⟩

private lemma ub_char_med_L1_tb (P : Params) (hStand : P.Standing)
    (Qbar : ℝ) (hQ0 : 0 ≤ Qbar) (hQ1 : Qbar < 1 - P.αg)
    (hX_pos : 0 < P.X)
    (hX_focus : P.X * ((P.αg + Qbar) - P.αb) < 2 * (P.θL * (P.αg + Qbar) - P.θH * P.αb))
    (σ : Profile) (hpost : IsPostInventorySPE P Qbar σ)
    (q w : ℝ) (hq_pos : 0 < q) (hw_ge_c1ρ : P.cost q / (1 - P.ρ) ≤ w)
    (hwL : w < q * P.θL)
    (hI0 : 0 ≤ σ.inv q w)
    (hI_opt : ∀ I' : ℝ, 0 ≤ I' → σ.supplierValue P q w I' ≤ σ.supplierValue P q w (σ.inv q w))
    (hS_pos : 0 < σ.inv q w + Qbar)
    (hBrL : (q * P.θH - w) * min P.αb (σ.inv q w + Qbar) <
      (q * P.θL - w) * min (σ.inv q w + Qbar) 1) :
    σ.retailerValue P q w ≤ max (P.V_OS Qbar) P.V_OO ∧
    (σ.retailerValue P q w = max (P.V_OS Qbar) P.V_OO →
      P.V_OS Qbar ≤ P.V_OO ∧ σ.retailerValue P q w = P.V_OO ∧
      σ.supplierValue P q w (σ.inv q w) =
        P.ρ * (1 - P.ρ) * (P.αg + (1 - P.ρ) * Qbar) * P.X ^ 2 / (4 * P.k) ∧
      q = (1 - P.ρ) * P.X / (2 * P.k) ∧ w = (1 - P.ρ) * P.X ^ 2 / (4 * P.k) ∧
      σ.priceAfter q w (σ.inv q w) .good (σ.order q w (σ.inv q w) .good) =
        (1 - P.ρ) * P.X * P.θH / (2 * P.k) ∧
      σ.priceAfter q w (σ.inv q w) .bad (σ.order q w (σ.inv q w) .bad) =
        (1 - P.ρ) * P.X * P.θL / (2 * P.k) ∧
      σ.inv q w = 1 - Qbar ∧
      σ.recv q w (σ.inv q w) .good (σ.order q w (σ.inv q w) .good) = P.αg ∧
      σ.recv q w (σ.inv q w) .bad (σ.order q w (σ.inv q w) .bad) = 1) := by
  rcases hStand with ⟨hθL, hθLH, hk, hρ0, hρ1, hαb0, hαb_lt, hαg_gt, hαg1⟩
  have hStand : P.Standing := ⟨hθL, hθLH, hk, hρ0, hρ1, hαb0, hαb_lt, hαg_gt, hαg1⟩
  have hθH : 0 < P.θH := lt_trans hθL hθLH
  have hαg0 : 0 < P.αg := pos_of_mul_pos_left (lt_trans hθL hαg_gt) hθH.le
  have hαb_αg : P.αb < P.αg := lt_of_mul_lt_mul_right (lt_trans hαb_lt hαg_gt) hθH.le
  have hαb1 : P.αb < 1 := lt_trans hαb_αg hαg1
  have h1ρ : 0 < 1 - P.ρ := sub_pos.mpr hρ1
  have hD1 : 0 < P.ρ * P.αg + 1 - P.ρ := by
    have : 0 < P.ρ * P.αg := mul_pos hρ0 hαg0
    linarith
  have hq : 0 ≤ q := hq_pos.le
  have hc_pos : 0 < P.cost q := mul_pos hk (pow_pos hq_pos 2)
  have hc_lt_c1ρ : P.cost q < P.cost q / (1 - P.ρ) := by
    rw [lt_div_iff₀ h1ρ]
    have : P.cost q * (1 - P.ρ) < P.cost q * 1 := mul_lt_mul_of_pos_left (by linarith) hc_pos
    linarith
  have hc_lt_w : P.cost q < w := lt_of_lt_of_le hc_lt_c1ρ hw_ge_c1ρ
  have hw_pos : 0 < w := lt_trans hc_pos hc_lt_w
  have hw : 0 ≤ w := hw_pos.le
  have hwH : w < q * P.θH := lt_trans hwL (mul_lt_mul_of_pos_left hθLH hq_pos)
  have hwH0 : 0 < q * P.θH - w := sub_pos.mpr hwH
  have hwL0 : 0 < q * P.θL - w := sub_pos.mpr hwL
  let I := σ.inv q w
  let S := I + Qbar
  let Qg := σ.order q w I .good
  let Qb := σ.order q w I .bad
  obtain ⟨hQg0, _⟩ := hpost.2.2 q w I .good hq hw hI0
  obtain ⟨hQb0, _⟩ := hpost.2.2 q w I .bad hq hw hI0
  have hmade_bds : ∀ s : State, ∀ Q : ℝ, 0 ≤ Q →
      0 ≤ σ.made q w I s Q ∧ σ.made q w I s Q ≤ Qbar ∧
      0 ≤ σ.recv q w I s Q ∧ σ.recv q w I s Q ≤ S := by
    intro s Q hQ
    unfold Profile.made Profile.recv inSeason received
    rcases le_or_gt Q I with hQI | hIQ
    · rw [if_pos hQI, if_pos hQI]; exact ⟨le_refl 0, hQ0, hQ, by dsimp [S]; linarith⟩
    · rw [if_neg (not_le_of_gt hIQ), if_neg (not_le_of_gt hIQ)]
      obtain ⟨hr0, hrQ, _⟩ := hpost.2.1 q w I s Q hq hw hI0 hIQ
      exact ⟨hr0, hrQ, le_min (add_nonneg hI0 hr0) hQ, le_trans (min_le_left _ _) (by dsimp [S]; linarith)⟩
  obtain ⟨hmg0, hmgQ, hRg0, hRgS⟩ := hmade_bds .good Qg hQg0
  obtain ⟨hmb0, hmbQ, hRb0, hRbS⟩ := hmade_bds .bad Qb hQb0
  let Rg := σ.recv q w I .good Qg
  let Rb := σ.recv q w I .bad Qb
  let pg := σ.priceAfter q w I .good Qg
  let pb := σ.priceAfter q w I .bad Qb
  obtain ⟨hpg0, _⟩ := hpost.1 q w I .good Qg (σ.made q w I .good Qg) hq hw hI0 hQg0 hmg0 hmgQ
  obtain ⟨hpb0, _⟩ := hpost.1 q w I .bad Qb (σ.made q w I .bad Qb) hq hw hI0 hQb0 hmb0 hmbQ
  have hrule := retailer_stage_rule P hStand q w S hq_pos hw hwH hS_pos.le
  have hov_step : ∀ s : State,
      σ.orderValue P q w I s (σ.order q w I s) =
        P.stepOnePayoff q w (P.alpha s) S (σ.recv q w I s (σ.order q w I s))
          (σ.priceAfter q w I s (σ.order q w I s)) := by
    rintro (_ | _)
    · unfold Profile.orderValue Params.retailerState Params.stepOnePayoff; rw [min_eq_left hRgS]
    · unfold Profile.orderValue Params.retailerState Params.stepOnePayoff; rw [min_eq_left hRbS]
  have hov_good_ub : σ.orderValue P q w I .good Qg ≤ (q * P.θH - w) * min P.αg S := by
    rw [hov_step .good]
    have h1 := (hrule.1 P.αg hαg0.le hαg1.le).2 ⟨Rg, pg, hRg0, hpg0, rfl⟩
    have hvH0 : 0 ≤ (q * P.θH - w) * min P.αg S := mul_nonneg hwH0.le (le_min hαg0.le hS_pos.le)
    have hvL_le : (q * P.θL - w) * min S 1 ≤ (q * P.θH - w) * min P.αg S := by
      rcases le_or_gt S P.αg with hSα | hSα
      · rw [min_eq_left (le_trans hSα hαg1.le), min_eq_right hSα]
        exact mul_le_mul_of_nonneg_right (by have := mul_lt_mul_of_pos_left hθLH hq_pos; linarith) hS_pos.le
      · rw [min_eq_left hSα.le]
        have hle1 : (q * P.θL - w) * min S 1 ≤ q * P.θL - w := by
          have := mul_le_mul_of_nonneg_left (min_le_right S 1) hwL0.le; linarith
        have h2 : q * P.θL < q * (P.αg * P.θH) := mul_lt_mul_of_pos_left hαg_gt hq_pos
        have h3 : w * P.αg ≤ w := by have := mul_le_mul_of_nonneg_left hαg1.le hw; linarith
        linarith
    rwa [max_eq_left hvL_le, max_eq_left hvH0] at h1
  have hb_max : σ.orderValue P q w I .bad Qb ≤ (q * P.θL - w) * min S 1 := by
    rw [hov_step .bad]
    have h1 := (hrule.1 P.αb hαb0.le hαb1.le).2 ⟨Rb, pb, hRb0, hpb0, rfl⟩
    have hvH0 : 0 ≤ (q * P.θH - w) * min P.αb S := mul_nonneg hwH0.le (le_min hαb0.le hS_pos.le)
    rw [max_eq_left (le_trans hvH0 (le_max_left _ _)), max_eq_right hBrL.le] at h1
    exact h1
  have hg_s1 : (q * P.θH - w) * min P.αg S ≤ (q * P.θH - w) * P.αg :=
    mul_le_mul_of_nonneg_left (min_le_left _ _) hwH0.le
  have hg_s2 : (q * P.θH - w) * P.αg ≤ (q * P.θH - P.cost q / (1 - P.ρ)) * P.αg :=
    mul_le_mul_of_nonneg_right (by linarith) hαg0.le
  have hb_s1 : (q * P.θL - w) * min S 1 ≤ q * P.θL - w := by
    have := mul_le_mul_of_nonneg_left (min_le_right S 1) hwL0.le; linarith
  have hb_s2 : q * P.θL - w ≤ q * P.θL - P.cost q / (1 - P.ρ) := by linarith
  have hlin := lin_id_oo_tb P q hk h1ρ hD1
  have hA_pos : 0 < (P.ρ * P.αg + 1 - P.ρ) / (1 - P.ρ) * P.k :=
    mul_pos (div_pos hD1 h1ρ) hk
  have hsq_nonneg : 0 ≤ (P.ρ * P.αg + 1 - P.ρ) / (1 - P.ρ) * P.k *
      (q - (1 - P.ρ) * P.X / (2 * P.k)) ^ 2 :=
    mul_nonneg hA_pos.le (sq_nonneg _)
  have hrv_ub_sum : σ.retailerValue P q w ≤
      P.ρ * ((q * P.θH - P.cost q / (1 - P.ρ)) * P.αg) +
        (1 - P.ρ) * (q * P.θL - P.cost q / (1 - P.ρ)) := by
    unfold Profile.retailerValue Params.prob
    change P.ρ * σ.orderValue P q w I .good Qg +
      (1 - P.ρ) * σ.orderValue P q w I .bad Qb ≤ _
    have := mul_le_mul_of_nonneg_left
      (le_trans hov_good_ub (le_trans hg_s1 hg_s2)) hρ0.le
    have := mul_le_mul_of_nonneg_left
      (le_trans hb_max (le_trans hb_s1 hb_s2)) h1ρ.le
    linarith
  have hrv_le_VOO : σ.retailerValue P q w ≤ P.V_OO := by linarith
  refine ⟨le_trans hrv_le_VOO (le_max_right _ _), fun hrv_eq => ?_⟩
  have hVOS_le_VOO : P.V_OS Qbar ≤ P.V_OO :=
    le_trans (le_max_left _ _) (hrv_eq ▸ hrv_le_VOO)
  have hrv_eq_VOO : σ.retailerValue P q w = P.V_OO :=
    le_antisymm hrv_le_VOO (hrv_eq.symm ▸ le_max_right _ _)
  have hsq_zero : (P.ρ * P.αg + 1 - P.ρ) / (1 - P.ρ) * P.k *
      (q - (1 - P.ρ) * P.X / (2 * P.k)) ^ 2 = 0 := by linarith
  have hq_eq : q = (1 - P.ρ) * P.X / (2 * P.k) := by
    have h1 : (q - (1 - P.ρ) * P.X / (2 * P.k)) ^ 2 = 0 := by
      rcases mul_eq_zero.mp hsq_zero with h0 | h0
      · exfalso; linarith
      · exact h0
    linarith [sq_eq_zero_iff.mp h1]
  have hov_g_eq : σ.orderValue P q w I .good Qg =
      (q * P.θH - P.cost q / (1 - P.ρ)) * P.αg := by
    unfold Profile.retailerValue Params.prob at hrv_eq_VOO
    change P.ρ * σ.orderValue P q w I .good Qg +
      (1 - P.ρ) * σ.orderValue P q w I .bad Qb = P.V_OO at hrv_eq_VOO
    by_contra hne
    have hlt : σ.orderValue P q w I .good Qg <
        (q * P.θH - P.cost q / (1 - P.ρ)) * P.αg :=
      lt_of_le_of_ne (le_trans hov_good_ub (le_trans hg_s1 hg_s2)) hne
    have := mul_lt_mul_of_pos_left hlt hρ0
    have := mul_le_mul_of_nonneg_left
      (le_trans hb_max (le_trans hb_s1 hb_s2)) h1ρ.le
    linarith
  have hov_b_eq : σ.orderValue P q w I .bad Qb = q * P.θL - P.cost q / (1 - P.ρ) := by
    unfold Profile.retailerValue Params.prob at hrv_eq_VOO
    change P.ρ * σ.orderValue P q w I .good Qg +
      (1 - P.ρ) * σ.orderValue P q w I .bad Qb = P.V_OO at hrv_eq_VOO
    by_contra hne
    have hlt : σ.orderValue P q w I .bad Qb < q * P.θL - P.cost q / (1 - P.ρ) :=
      lt_of_le_of_ne (le_trans hb_max (le_trans hb_s1 hb_s2)) hne
    have := mul_le_mul_of_nonneg_left
      (le_trans hov_good_ub (le_trans hg_s1 hg_s2)) hρ0.le
    have := mul_lt_mul_of_pos_left hlt h1ρ
    linarith
  have hw_eq_c1ρ : w = P.cost q / (1 - P.ρ) := by linarith
  obtain ⟨_hc_oo, hc1ρ_oo, _hval_oo, _hsv_oo_alg⟩ := val_qoo_tb P Qbar hk h1ρ hD1
  have hw_eq : w = (1 - P.ρ) * P.X ^ 2 / (4 * P.k) := by
    rw [hw_eq_c1ρ, hq_eq, hc1ρ_oo]
  have hminS1 : min S 1 = 1 := by
    have h1 : (q * P.θL - w) * min S 1 = q * P.θL - w := by linarith
    have h2 : (q * P.θL - w) * (1 - min S 1) = 0 := by linarith
    rcases mul_eq_zero.mp h2 with h0 | h0 <;> linarith
  have hS_ge1 : 1 ≤ S := by
    by_contra hc
    rw [min_eq_left (lt_of_not_ge hc).le] at hminS1; linarith
  have hI_ge_1Q : 1 - Qbar ≤ I := by dsimp [S] at hS_ge1; linarith
  have hlow_oo : (q * P.θH - w) * P.αb < (q * P.θL - w) * (P.αg + Qbar) := by
    rw [hq_eq, hw_eq, oo_margin_id_tb P.ρ P.X P.θH P.k hk.ne',
      oo_margin_id_tb P.ρ P.X P.θL P.k hk.ne']
    have hfac : 0 < (1 - P.ρ) * P.X / (4 * P.k) := div_pos (mul_pos h1ρ hX_pos) (by linarith)
    have hlt_in : (2 * P.θH - P.X) * P.αb < (2 * P.θL - P.X) * (P.αg + Qbar) := by
      clear * - hX_focus; linarith
    have hmul := mul_lt_mul_of_pos_left hlt_in hfac
    clear * - hmul; linarith
  have hresp := (supplier_response_medium P hStand Qbar hQ0 hQ1 σ hpost q w hq_pos
    hc_lt_w hlow_oo).2.2 hw_eq_c1ρ
  have hI_mem : I ∈ Set.Icc P.αg (1 - Qbar) := by
    rw [← hresp]
    exact ⟨hI0, hI_opt⟩
  have hI_eq : I = 1 - Qbar := le_antisymm hI_mem.2 hI_ge_1Q
  have hov_g_w : σ.orderValue P q w I .good Qg = (q * P.θH - w) * P.αg := by
    rw [hov_g_eq, hw_eq_c1ρ]
  have hov_b_w : σ.orderValue P q w I .bad Qb = q * P.θL - w := by
    rw [hov_b_eq, hw_eq_c1ρ]
  obtain ⟨hsv_eq, hpg_eq, hpb_eq, hRg_eq, hRb_eq⟩ :=
    ub_char_med_L1b_tb P hStand Qbar hQ0 hQ1 σ hpost q w hq_pos hw_pos hwL hI0
      hq_eq hw_eq hI_eq hBrL hov_g_w hov_b_w
  exact ⟨hVOS_le_VOO, hrv_eq_VOO, hsv_eq, hq_eq, hw_eq, hpg_eq, hpb_eq, hI_eq,
    hRg_eq, hRb_eq⟩

private lemma ub_char_med_tb (P : Params) (hP : P.Dom)
    (Qbar : ℝ) (hQ0 : 0 ≤ Qbar) (hQ1 : Qbar < 1 - P.αg)
    (σ : Profile) (hpost : IsPostInventorySPE P Qbar σ)
    (hinv : ∀ q w : ℝ, 0 ≤ q → 0 ≤ w →
      0 ≤ σ.inv q w ∧ ∀ I' : ℝ, 0 ≤ I' → σ.supplierValue P q w I' ≤ σ.supplierValue P q w (σ.inv q w))
    (q w : ℝ) (hq : 0 ≤ q) (hw : 0 ≤ w) :
    σ.retailerValue P q w ≤ max (P.V_OS Qbar) P.V_OO ∧
    (σ.retailerValue P q w = max (P.V_OS Qbar) P.V_OO →
      (P.V_OO ≤ P.V_OS Qbar ∧ σ.retailerValue P q w = P.V_OS Qbar ∧
        σ.supplierValue P q w (σ.inv q w) = 0 ∧
        q = P.Y (P.αg + Qbar) / (2 * P.k) ∧ w = P.Y (P.αg + Qbar) ^ 2 / (4 * P.k) ∧
        σ.priceAfter q w (σ.inv q w) .good (σ.order q w (σ.inv q w) .good) =
          P.Y (P.αg + Qbar) * P.θH / (2 * P.k) ∧
        σ.priceAfter q w (σ.inv q w) .bad (σ.order q w (σ.inv q w) .bad) =
          P.Y (P.αg + Qbar) * P.θL / (2 * P.k) ∧
        σ.inv q w = P.αg ∧
        σ.recv q w (σ.inv q w) .good (σ.order q w (σ.inv q w) .good) = P.αg ∧
        σ.recv q w (σ.inv q w) .bad (σ.order q w (σ.inv q w) .bad) = P.αg + Qbar) ∨
      (P.V_OS Qbar ≤ P.V_OO ∧ σ.retailerValue P q w = P.V_OO ∧
        σ.supplierValue P q w (σ.inv q w) =
          P.ρ * (1 - P.ρ) * (P.αg + (1 - P.ρ) * Qbar) * P.X ^ 2 / (4 * P.k) ∧
        q = (1 - P.ρ) * P.X / (2 * P.k) ∧ w = (1 - P.ρ) * P.X ^ 2 / (4 * P.k) ∧
        σ.priceAfter q w (σ.inv q w) .good (σ.order q w (σ.inv q w) .good) =
          (1 - P.ρ) * P.X * P.θH / (2 * P.k) ∧
        σ.priceAfter q w (σ.inv q w) .bad (σ.order q w (σ.inv q w) .bad) =
          (1 - P.ρ) * P.X * P.θL / (2 * P.k) ∧
        σ.inv q w = 1 - Qbar ∧
        σ.recv q w (σ.inv q w) .good (σ.order q w (σ.inv q w) .good) = P.αg ∧
        σ.recv q w (σ.inv q w) .bad (σ.order q w (σ.inv q w) .bad) = 1)) := by
  have hHOD_med := hod_med_tb P hP Qbar hQ0 hQ1.le
  rcases hP with ⟨hStand, hFocus, _hHOD⟩
  obtain ⟨hDS, _hYS_pos, hX_pos, _hX_le_YS, _hYS_le, _hYS_lt, _hX_lt, _hYS_f, hX_focus⟩ :=
    focus_Y_props_tb P hStand hFocus (P.αg + Qbar) (by linarith) (by linarith)
  rcases hStand with ⟨hθL, hθLH, hk, hρ0, hρ1, hαb0, hαb_lt, hαg_gt, hαg1⟩
  have hStand : P.Standing := ⟨hθL, hθLH, hk, hρ0, hρ1, hαb0, hαb_lt, hαg_gt, hαg1⟩
  have hθH : 0 < P.θH := lt_trans hθL hθLH
  have hαg0 : 0 < P.αg := pos_of_mul_pos_left (lt_trans hθL hαg_gt) hθH.le
  have hαb_αg : P.αb < P.αg := lt_of_mul_lt_mul_right (lt_trans hαb_lt hαg_gt) hθH.le
  have hαb1 : P.αb < 1 := lt_trans hαb_αg hαg1
  have h1ρ : 0 < 1 - P.ρ := sub_pos.mpr hρ1
  have hD1 : 0 < P.ρ * P.αg + 1 - P.ρ := by
    have : 0 < P.ρ * P.αg := mul_pos hρ0 hαg0
    linarith
  have hVOO_pos : 0 < P.V_OO := by
    unfold Params.V_OO
    exact div_pos (mul_pos (mul_pos h1ρ hD1) (pow_pos hX_pos 2)) (by linarith)
  have hM_pos : 0 < max (P.V_OS Qbar) P.V_OO := lt_of_lt_of_le hVOO_pos (le_max_right _ _)
  let M := max (P.V_OS Qbar) P.V_OO
  let I := σ.inv q w
  obtain ⟨hI0, hI_opt⟩ := hinv q w hq hw
  have hsv0_nonneg : 0 ≤ σ.supplierValue P q w 0 := by
    have hst : ∀ s : State, 0 ≤ σ.supplierStateValue P q w 0 s := by
      intro s
      obtain ⟨hQs0, _⟩ := hpost.2.2 q w 0 s hq hw (le_refl 0)
      unfold Profile.supplierStateValue Params.supplierState Profile.recv Profile.made
        received inSeason
      rcases le_or_gt (σ.order q w 0 s) 0 with hle | hgt
      · simp [le_antisymm hle hQs0]
      · have hropt := (hpost.2.1 q w 0 s (σ.order q w 0 s) hq hw (le_refl 0) hgt).2.2
          0 (le_refl 0) hQ0
        unfold Params.supplierState received at hropt
        simp only [if_neg (not_le_of_gt hgt), zero_add, min_eq_left hQs0, mul_zero, sub_zero] at hropt
        simp only [if_neg (not_le_of_gt hgt), zero_add]
        linarith
    unfold Profile.supplierValue Params.prob
    exact add_nonneg (mul_nonneg hρ0.le (hst .good)) (mul_nonneg h1ρ.le (hst .bad))
  have hsv_I_nonneg : 0 ≤ σ.supplierValue P q w I := le_trans hsv0_nonneg (hI_opt 0 (le_refl 0))
  have hmade_bds : ∀ J : ℝ, ∀ s : State, ∀ Q : ℝ, 0 ≤ J → 0 ≤ Q →
      0 ≤ σ.made q w J s Q ∧ σ.made q w J s Q ≤ Qbar ∧
      0 ≤ σ.recv q w J s Q ∧ σ.recv q w J s Q ≤ J + Qbar := by
    intro J s Q hJ hQ
    unfold Profile.made Profile.recv inSeason received
    rcases le_or_gt Q J with hQJ | hJQ
    · rw [if_pos hQJ, if_pos hQJ]
      exact ⟨le_refl 0, hQ0, hQ, by linarith⟩
    · rw [if_neg (not_le_of_gt hJQ), if_neg (not_le_of_gt hJQ)]
      obtain ⟨hr0, hrQ, _⟩ := hpost.2.1 q w J s Q hq hw hJ hJQ
      exact ⟨hr0, hrQ, le_min (add_nonneg hJ hr0) hQ, le_trans (min_le_left _ _) (by linarith)⟩
  by_cases hact : P.cost q ≤ w ∧ 0 < q ∧ w < q * P.θH
  · rcases hact with ⟨hcw, hq_pos, hwH⟩
    have hwH0 : 0 < q * P.θH - w := sub_pos.mpr hwH
    let S := I + Qbar
    let Qg := σ.order q w I .good
    let Qb := σ.order q w I .bad
    obtain ⟨hQg0, _⟩ := hpost.2.2 q w I .good hq hw hI0
    obtain ⟨hQb0, _⟩ := hpost.2.2 q w I .bad hq hw hI0
    obtain ⟨hmg0, hmgQ, hRg0, hRgS⟩ := hmade_bds I .good Qg hI0 hQg0
    obtain ⟨hmb0, hmbQ, hRb0, hRbS⟩ := hmade_bds I .bad Qb hI0 hQb0
    let Rg := σ.recv q w I .good Qg
    let Rb := σ.recv q w I .bad Qb
    let pg := σ.priceAfter q w I .good Qg
    let pb := σ.priceAfter q w I .bad Qb
    obtain ⟨hpg0, _⟩ := hpost.1 q w I .good Qg (σ.made q w I .good Qg) hq hw hI0 hQg0 hmg0 hmgQ
    obtain ⟨hpb0, _⟩ := hpost.1 q w I .bad Qb (σ.made q w I .bad Qb) hq hw hI0 hQb0 hmb0 hmbQ
    rcases eq_or_lt_of_le (add_nonneg hI0 hQ0) with hS0_eq | hS_pos
    · have hRg_zero : Rg = 0 := le_antisymm (hRgS.trans hS0_eq.symm.le) hRg0
      have hRb_zero : Rb = 0 := le_antisymm (hRbS.trans hS0_eq.symm.le) hRb0
      have hov0 : ∀ s : State, σ.orderValue P q w I s (σ.order q w I s) = 0 := by
        rintro (_ | _)
        · unfold Profile.orderValue Params.retailerState
          change pg * min (P.demand q P.αg pg) Rg - w * Rg = 0
          have hd0 : 0 ≤ P.demand q P.αg pg := by unfold Params.demand; split_ifs <;> linarith
          rw [hRg_zero, min_eq_right hd0, mul_zero, mul_zero, sub_zero]
        · unfold Profile.orderValue Params.retailerState
          change pb * min (P.demand q P.αb pb) Rb - w * Rb = 0
          have hd0 : 0 ≤ P.demand q P.αb pb := by unfold Params.demand; split_ifs <;> linarith
          rw [hRb_zero, min_eq_right hd0, mul_zero, mul_zero, sub_zero]
      have hrv0 : σ.retailerValue P q w = 0 := by
        unfold Profile.retailerValue Params.prob
        change P.ρ * σ.orderValue P q w I .good _ + (1 - P.ρ) * σ.orderValue P q w I .bad _ = 0
        rw [hov0 .good, hov0 .bad]; ring
      have hrv_lt : σ.retailerValue P q w < M := by rw [hrv0]; exact hM_pos
      exact ⟨hrv_lt.le, fun heq => absurd heq hrv_lt.ne⟩
    · have hrule := retailer_stage_rule P hStand q w S hq_pos hw hwH hS_pos.le
      have hov_step : ∀ s : State,
          σ.orderValue P q w I s (σ.order q w I s) =
            P.stepOnePayoff q w (P.alpha s) S (σ.recv q w I s (σ.order q w I s))
              (σ.priceAfter q w I s (σ.order q w I s)) := by
        rintro (_ | _)
        · unfold Profile.orderValue Params.retailerState Params.stepOnePayoff; rw [min_eq_left hRgS]
        · unfold Profile.orderValue Params.retailerState Params.stepOnePayoff; rw [min_eq_left hRbS]
      have hov_good_ub : σ.orderValue P q w I .good Qg ≤ (q * P.θH - w) * min P.αg S := by
        rw [hov_step .good]
        have h1 := (hrule.1 P.αg hαg0.le hαg1.le).2 ⟨Rg, pg, hRg0, hpg0, rfl⟩
        have hvH0 : 0 ≤ (q * P.θH - w) * min P.αg S :=
          mul_nonneg hwH0.le (le_min hαg0.le hS_pos.le)
        have hvL_le : (q * P.θL - w) * min S 1 ≤ (q * P.θH - w) * min P.αg S := by
          rcases le_or_gt (q * P.θL - w) 0 with hL0 | hL_pos
          · exact le_trans (mul_nonpos_of_nonpos_of_nonneg hL0 (le_min hS_pos.le zero_le_one)) hvH0
          · rcases le_or_gt S P.αg with hSα | hSα
            · rw [min_eq_left (le_trans hSα hαg1.le), min_eq_right hSα]
              exact mul_le_mul_of_nonneg_right
                (by have := mul_lt_mul_of_pos_left hθLH hq_pos; linarith) hS_pos.le
            · rw [min_eq_left hSα.le]
              have hle1 : (q * P.θL - w) * min S 1 ≤ q * P.θL - w := by
                have := mul_le_mul_of_nonneg_left (min_le_right S 1) hL_pos.le; linarith
              have h2 : q * P.θL < q * (P.αg * P.θH) := mul_lt_mul_of_pos_left hαg_gt hq_pos
              have h3 : w * P.αg ≤ w := by
                have := mul_le_mul_of_nonneg_left hαg1.le hw; linarith
              linarith
        rwa [max_eq_left hvL_le, max_eq_left hvH0] at h1
      have hov_bad_ub : σ.orderValue P q w I .bad Qb ≤
          max ((q * P.θH - w) * min P.αb S) ((q * P.θL - w) * min S 1) := by
        rw [hov_step .bad]
        have h1 := (hrule.1 P.αb hαb0.le hαb1.le).2 ⟨Rb, pb, hRb0, hpb0, rfl⟩
        have hvH0 : 0 ≤ (q * P.θH - w) * min P.αb S :=
          mul_nonneg hwH0.le (le_min hαb0.le hS_pos.le)
        rwa [max_eq_left (le_trans hvH0 (le_max_left _ _))] at h1
      rcases le_or_gt ((q * P.θL - w) * min S 1) ((q * P.θH - w) * min P.αb S) with hBrH | hBrL
      · have hg_le : σ.orderValue P q w I .good Qg ≤ (q * P.θH - P.cost q) * P.αg := by
          have h1 : (q * P.θH - w) * min P.αg S ≤ (q * P.θH - w) * P.αg :=
            mul_le_mul_of_nonneg_left (min_le_left _ _) hwH0.le
          have h2 : (q * P.θH - w) * P.αg ≤ (q * P.θH - P.cost q) * P.αg :=
            mul_le_mul_of_nonneg_right (by linarith) hαg0.le
          linarith
        have hb_le : σ.orderValue P q w I .bad Qb ≤ (q * P.θH - P.cost q) * P.αb := by
          rw [max_eq_left hBrH] at hov_bad_ub
          have h1 : (q * P.θH - w) * min P.αb S ≤ (q * P.θH - w) * P.αb :=
            mul_le_mul_of_nonneg_left (min_le_left _ _) hwH0.le
          have h2 : (q * P.θH - w) * P.αb ≤ (q * P.θH - P.cost q) * P.αb :=
            mul_le_mul_of_nonneg_right (by linarith) hαb0.le
          linarith
        have hrv_lt : σ.retailerValue P q w < M := by
          have h1 : σ.retailerValue P q w ≤
              (P.ρ * P.αg + (1 - P.ρ) * P.αb) * (q * P.θH - P.cost q) := by
            unfold Profile.retailerValue Params.prob
            change P.ρ * σ.orderValue P q w I .good Qg +
              (1 - P.ρ) * σ.orderValue P q w I .bad Qb ≤ _
            have := mul_le_mul_of_nonneg_left hg_le hρ0.le
            have := mul_le_mul_of_nonneg_left hb_le h1ρ.le
            linarith
          have hsq : q * P.θH - P.cost q ≤ P.θH ^ 2 / (4 * P.k) := by
            unfold Params.cost
            rw [le_div_iff₀ (by linarith : 0 < 4 * P.k)]
            have : 0 ≤ (2 * P.k * q - P.θH) ^ 2 := sq_nonneg _
            linarith
          have hA : 0 < P.ρ * P.αg + (1 - P.ρ) * P.αb :=
            add_pos (mul_pos hρ0 hαg0) (mul_pos h1ρ hαb0)
          have h2 : (P.ρ * P.αg + (1 - P.ρ) * P.αb) * (q * P.θH - P.cost q) ≤
              (P.ρ * P.αg + (1 - P.ρ) * P.αb) * P.θH ^ 2 / (4 * P.k) := by
            rw [mul_div_assoc]
            exact mul_le_mul_of_nonneg_left hsq hA.le
          exact lt_of_le_of_lt (le_trans h1 h2) hHOD_med
        exact ⟨hrv_lt.le, fun heq => absurd heq hrv_lt.ne⟩
      · have hwL : w < q * P.θL := by
          have hvH_pos : 0 < (q * P.θH - w) * min P.αb S :=
            mul_pos hwH0 (lt_min hαb0 hS_pos)
          have hvL_pos : 0 < (q * P.θL - w) * min S 1 := lt_trans hvH_pos hBrL
          by_contra hc
          have := mul_nonpos_of_nonpos_of_nonneg (by linarith : q * P.θL - w ≤ 0)
            (le_min hS_pos.le zero_le_one)
          linarith
        rcases lt_or_ge w (P.cost q / (1 - P.ρ)) with hw_lt_c1ρ | hw_ge_c1ρ
        · obtain ⟨hub_L2, hchar_L2⟩ := ub_char_med_L2_tb P hStand Qbar hQ0 hQ1 hDS σ hpost
            q w hq_pos hcw hw_lt_c1ρ hwL hI0 hI_opt hsv_I_nonneg hS_pos hBrL
          exact ⟨hub_L2, fun heq => Or.inl (hchar_L2 heq)⟩
        · obtain ⟨hub_L1, hchar_L1⟩ := ub_char_med_L1_tb P hStand Qbar hQ0 hQ1 hX_pos hX_focus
            σ hpost q w hq_pos hw_ge_c1ρ hwL hI0 hI_opt hS_pos hBrL
          exact ⟨hub_L1, fun heq => Or.inr (hchar_L1 heq)⟩
  · -- Inactive contract: retailerValue ≤ 0 < M
    have hrv_nonpos : σ.retailerValue P q w ≤ 0 := by
      rcases lt_or_ge w (P.cost q) with hw_lt | hcw
      · have hreact0 : ∀ J : ℝ, ∀ s : State, ∀ Q : ℝ, 0 ≤ J → J < Q →
            σ.react q w J s Q = 0 := by
          intro J s Q hJ hJQ
          obtain ⟨hr0, _hrQ, hropt⟩ := hpost.2.1 q w J s Q hq hw hJ hJQ
          have h0 := hropt 0 (le_refl 0) hQ0
          unfold Params.supplierState received at h0
          simp only [if_neg (not_le_of_gt hJQ), add_zero, min_eq_left hJQ.le] at h0
          by_contra hne
          have hr_pos : 0 < σ.react q w J s Q := lt_of_le_of_ne hr0 (Ne.symm hne)
          have hmin_gt : J < min (J + σ.react q w J s Q) Q := lt_min (by linarith) hJQ
          have hmin_le : min (J + σ.react q w J s Q) Q ≤ J + σ.react q w J s Q := min_le_left _ _
          have hc0 : 0 ≤ P.cost q := mul_nonneg hk.le (sq_nonneg q)
          have h1 : (w - P.cost q) * (min (J + σ.react q w J s Q) Q - J) < 0 :=
            mul_neg_of_neg_of_pos (by linarith) (by linarith)
          have h2 : 0 ≤ P.cost q * (J + σ.react q w J s Q - min (J + σ.react q w J s Q) Q) :=
            mul_nonneg hc0 (by linarith)
          linarith
        have hsv_le : ∀ s : State, σ.supplierStateValue P q w I s ≤ (w - P.cost q) * I := by
          intro s
          unfold Profile.supplierStateValue Params.supplierState Profile.recv Profile.made
            received inSeason
          rcases le_or_gt (σ.order q w I s) I with hQI | hIQ
          · rw [if_pos hQI, if_pos hQI, add_zero]
            have := mul_le_mul_of_nonneg_left hQI hw
            linarith
          · rw [if_neg (not_le_of_gt hIQ), if_neg (not_le_of_gt hIQ),
              hreact0 I s _ hI0 hIQ, add_zero, min_eq_left hIQ.le]
            linarith
        have hI_eq0 : I = 0 := by
          by_contra hne
          have hI_pos : 0 < I := lt_of_le_of_ne hI0 (Ne.symm hne)
          have hneg : (w - P.cost q) * I < 0 := mul_neg_of_neg_of_pos (by linarith) hI_pos
          unfold Profile.supplierValue Params.prob at hsv_I_nonneg
          have := mul_le_mul_of_nonneg_left (hsv_le .good) hρ0.le
          have := mul_le_mul_of_nonneg_left (hsv_le .bad) h1ρ.le
          linarith
        have hov0 : ∀ s : State, σ.orderValue P q w I s (σ.order q w I s) = 0 := by
          intro s
          obtain ⟨hQs0, _⟩ := hpost.2.2 q w I s hq hw hI0
          have hrec0 : σ.recv q w I s (σ.order q w I s) = 0 := by
            unfold Profile.recv received
            rcases le_or_gt (σ.order q w I s) I with hle | hgt
            · rw [if_pos hle]; linarith
            · rw [if_neg (not_le_of_gt hgt), hreact0 I s _ hI0 hgt, add_zero,
                min_eq_left hgt.le, hI_eq0]
          unfold Profile.orderValue Params.retailerState
          rw [hrec0, mul_zero]
          have hd0 : 0 ≤ P.demand q (P.alpha s) (σ.priceAfter q w I s (σ.order q w I s)) := by
            unfold Params.demand
            cases s <;> (simp only [Params.alpha]; split_ifs <;> linarith)
          rw [min_eq_right hd0, mul_zero, sub_zero]
        unfold Profile.retailerValue Params.prob
        change P.ρ * σ.orderValue P q w I .good _ + (1 - P.ρ) * σ.orderValue P q w I .bad _ ≤ 0
        rw [hov0 .good, hov0 .bad]; linarith
      · have hw_ge_H : q * P.θH ≤ w := by
          rcases eq_or_lt_of_le hq with rfl | hq_pos
          · simp [hw]
          · by_contra hc; exact hact ⟨hcw, hq_pos, lt_of_not_ge hc⟩
        have hov_le0 : ∀ s : State, σ.orderValue P q w I s (σ.order q w I s) ≤ 0 := by
          intro s
          obtain ⟨hQs0, _⟩ := hpost.2.2 q w I s hq hw hI0
          obtain ⟨_, _, hRs0, _⟩ := hmade_bds I s (σ.order q w I s) hI0 hQs0
          let Rs := σ.recv q w I s (σ.order q w I s)
          let ps := σ.priceAfter q w I s (σ.order q w I s)
          unfold Profile.orderValue Params.retailerState
          change ps * min (P.demand q (P.alpha s) ps) Rs - w * Rs ≤ 0
          rcases le_or_gt ps (q * P.θH) with hpH | hpH
          · have hd0 : 0 ≤ P.demand q (P.alpha s) ps := by
              unfold Params.demand
              cases s <;> (simp only [Params.alpha]; split_ifs <;> linarith)
            have hm0 : 0 ≤ min (P.demand q (P.alpha s) ps) Rs := le_min hd0 hRs0
            have hm_le : min (P.demand q (P.alpha s) ps) Rs ≤ Rs := min_le_right _ _
            have h1 : ps * min (P.demand q (P.alpha s) ps) Rs ≤
                w * min (P.demand q (P.alpha s) ps) Rs :=
              mul_le_mul_of_nonneg_right (le_trans hpH hw_ge_H) hm0
            have h2 : w * min (P.demand q (P.alpha s) ps) Rs ≤ w * Rs :=
              mul_le_mul_of_nonneg_left hm_le hw
            linarith
          · have hpL : q * P.θL < ps :=
              lt_of_le_of_lt (mul_le_mul_of_nonneg_left hθLH.le hq) hpH
            unfold Params.demand
            rw [if_neg (not_le_of_gt hpL), if_neg (not_le_of_gt hpH), add_zero,
              min_eq_left hRs0, mul_zero]
            have : 0 ≤ w * Rs := mul_nonneg hw hRs0
            linarith
        unfold Profile.retailerValue Params.prob
        change P.ρ * σ.orderValue P q w I .good _ + (1 - P.ρ) * σ.orderValue P q w I .bad _ ≤ 0
        have := mul_le_mul_of_nonneg_left (hov_le0 .good) hρ0.le
        have := mul_le_mul_of_nonneg_left (hov_le0 .bad) h1ρ.le
        linarith
    have hrv_lt : σ.retailerValue P q w < M := lt_of_le_of_lt hrv_nonpos hM_pos
    exact ⟨hrv_lt.le, fun heq => absurd heq hrv_lt.ne⟩

private lemma lb_os_tb (P : Params) (hStand : P.Standing) (hFocus : P.Focus)
    (Qbar : ℝ) (hQ0 : 0 ≤ Qbar) (hQ1 : Qbar < 1 - P.αg)
    (σ : Profile) (hSPE : IsSPE P Qbar σ) :
    P.V_OS Qbar ≤ σ.retailerValue P σ.q σ.w := by
  rcases hSPE with ⟨hpost, hinv, _hq0, _hw0, hropt⟩
  obtain ⟨hDS, hYS_pos, _hX_pos, _hX_le, _hYS_le, hYS_lt, _hX_lt, hYS_focus, _hX_f⟩ :=
    focus_Y_props_tb P hStand hFocus (P.αg + Qbar) (by linarith) (by linarith)
  rcases hStand with ⟨hθL, hθLH, hk, hρ0, hρ1, hαb0, hαb_lt, hαg_gt, _hαg1⟩
  have hStand : P.Standing := ⟨hθL, hθLH, hk, hρ0, hρ1, hαb0, hαb_lt, hαg_gt, _hαg1⟩
  have hθH : 0 < P.θH := lt_trans hθL hθLH
  have hαg0 : 0 < P.αg := pos_of_mul_pos_left (lt_trans hθL hαg_gt) hθH.le
  have hαb_αg : P.αb < P.αg := lt_of_mul_lt_mul_right (lt_trans hαb_lt hαg_gt) hθH.le
  have h1ρ : 0 < 1 - P.ρ := sub_pos.mpr hρ1
  let S_Q := P.αg + Qbar
  let qstar := P.Y S_Q / (2 * P.k)
  let wstar := P.Y S_Q ^ 2 / (4 * P.k)
  have hqs_pos : 0 < qstar := div_pos hYS_pos (by linarith)
  have hws_pos : 0 < wstar := div_pos (pow_pos hYS_pos 2) (by linarith)
  have hc_qs : P.cost qstar = wstar := by
    dsimp [qstar, wstar]; unfold Params.cost; field_simp [hk.ne']; ring
  have hws_lt_c1ρ : wstar < P.cost qstar / (1 - P.ρ) := by
    rw [hc_qs, lt_div_iff₀ h1ρ]
    have : wstar * (1 - P.ρ) < wstar * 1 := mul_lt_mul_of_pos_left (by linarith) hws_pos
    linarith
  have hws_lt_L : wstar < qstar * P.θL := by
    dsimp [qstar, wstar]
    rw [div_mul_eq_mul_div, div_lt_div_iff₀ (by linarith : 0 < 4 * P.k) (by linarith : 0 < 2 * P.k)]
    have := mul_lt_mul_of_pos_left hYS_lt (mul_pos hYS_pos hk)
    dsimp [S_Q] at *; linarith
  have hlow_qs : (qstar * P.θH - wstar) * P.αb < (qstar * P.θL - wstar) * S_Q := by
    dsimp [qstar, wstar]
    have hid1 : P.Y S_Q / (2 * P.k) * P.θH - P.Y S_Q ^ 2 / (4 * P.k) =
        P.Y S_Q / (4 * P.k) * (2 * P.θH - P.Y S_Q) := by field_simp [hk.ne']; ring
    have hid2 : P.Y S_Q / (2 * P.k) * P.θL - P.Y S_Q ^ 2 / (4 * P.k) =
        P.Y S_Q / (4 * P.k) * (2 * P.θL - P.Y S_Q) := by field_simp [hk.ne']; ring
    rw [hid1, hid2]
    have hfac : 0 < P.Y S_Q / (4 * P.k) := div_pos hYS_pos (by linarith)
    have hlt_inner : (2 * P.θH - P.Y S_Q) * P.αb < (2 * P.θL - P.Y S_Q) * S_Q := by
      dsimp [S_Q] at *; linarith
    have := mul_lt_mul_of_pos_left hlt_inner hfac
    linarith
  by_contra hlt_c
  have hgap : 0 < P.V_OS Qbar - σ.retailerValue P σ.q σ.w := sub_pos.mpr (lt_of_not_ge hlt_c)
  let δ1 := (qstar * P.θL - wstar) * S_Q - (qstar * P.θH - wstar) * P.αb
  have hδ1_pos : 0 < δ1 := sub_pos.mpr hlow_qs
  let δ2 := qstar * P.θL - wstar
  have hδ2_pos : 0 < δ2 := sub_pos.mpr hws_lt_L
  let δ4 := P.cost qstar / (1 - P.ρ) - wstar
  have hδ4_pos : 0 < δ4 := sub_pos.mpr hws_lt_c1ρ
  let δ3 := (P.V_OS Qbar - σ.retailerValue P σ.q σ.w) / (2 * (P.ρ * P.αg + (1 - P.ρ) * S_Q))
  have hδ3_pos : 0 < δ3 := div_pos hgap (mul_pos (by norm_num) hDS)
  let ε := min (min (δ1 / 2) (δ2 / 2)) (min (δ4 / 2) δ3)
  have hε_pos : 0 < ε :=
    lt_min (lt_min (half_pos hδ1_pos) (half_pos hδ2_pos)) (lt_min (half_pos hδ4_pos) hδ3_pos)
  have hε_1 : ε ≤ δ1 / 2 := le_trans (min_le_left _ _) (min_le_left _ _)
  have hε_2 : ε ≤ δ2 / 2 := le_trans (min_le_left _ _) (min_le_right _ _)
  have hε_4 : ε ≤ δ4 / 2 := le_trans (min_le_right _ _) (min_le_left _ _)
  have hε_3 : ε ≤ δ3 := le_trans (min_le_right _ _) (min_le_right _ _)
  let wε := wstar + ε
  have hwε_gt_c : P.cost qstar < wε := by rw [hc_qs]; dsimp [wε]; linarith
  have hwε0 : 0 ≤ wε := (lt_trans hws_pos (by dsimp [wε]; linarith)).le
  have hwε_lt_c1ρ : wε < P.cost qstar / (1 - P.ρ) := by dsimp [wε, δ4] at *; linarith
  have hlow_ε : (qstar * P.θH - wε) * P.αb < (qstar * P.θL - wε) * S_Q := by
    have hSab : S_Q - P.αb ≤ 1 := by dsimp [S_Q]; linarith
    have : ε * (S_Q - P.αb) ≤ ε := mul_le_of_le_one_right hε_pos.le hSab
    dsimp [wε, δ1] at *; linarith
  have hresp := (supplier_response_medium P hStand Qbar hQ0 hQ1 σ hpost qstar wε hqs_pos
    hwε_gt_c hlow_ε).1 hwε_lt_c1ρ
  have hmem : σ.inv qstar wε ∈ ({P.αg} : Set ℝ) := by
    rw [← hresp]
    exact hinv qstar wε hqs_pos.le hwε0
  have hIε_eq : σ.inv qstar wε = P.αg := Set.mem_singleton_iff.mp hmem
  let Iε := σ.inv qstar wε
  have hIε0 : 0 ≤ Iε := by dsimp [Iε]; rw [hIε_eq]; exact hαg0.le
  have hSε_eq : Iε + Qbar = S_Q := by dsimp [Iε, S_Q]; rw [hIε_eq]
  have hrecv_ε : ∀ s : State, ∀ Q : ℝ, 0 ≤ Q → σ.recv qstar wε Iε s Q = min Q S_Q := by
    intro s Q _hQ
    rw [← hSε_eq]
    unfold Profile.recv received
    rcases le_or_gt Q Iε with hQI | hIQ
    · rw [if_pos hQI, min_eq_left (by linarith)]
    · rw [if_neg (not_le_of_gt hIQ)]
      obtain ⟨_hr0, _hrQ, hropt_r⟩ := hpost.2.1 qstar wε Iε s Q hqs_pos.le hwε0 hIε0 hIQ
      let Is := min Qbar (Q - Iε)
      have hge_r := hropt_r Is (le_min hQ0 (sub_pos.mpr hIQ).le) (min_le_left _ _)
      have hIIs : Iε + Is ≤ Q := by have := min_le_right Qbar (Q - Iε); dsimp [Is]; linarith
      have hreq : σ.react qstar wε Iε s Q = Is := by
        unfold Params.supplierState received at hge_r
        simp only [if_neg (not_le_of_gt hIQ), min_eq_left hIIs] at hge_r
        rcases lt_trichotomy (σ.react qstar wε Iε s Q) Is with hlt | heq | hgt
        · exfalso
          rw [min_eq_left (by linarith)] at hge_r
          have := mul_lt_mul_of_pos_left (by linarith : Iε + σ.react qstar wε Iε s Q < Iε + Is)
            (sub_pos.mpr hwε_gt_c)
          linarith
        · exact heq
        · exfalso
          have hIs_eq : Is = Q - Iε := by
            dsimp [Is] at hgt ⊢
            rcases le_or_gt Qbar (Q - Iε) with h1 | h1
            · rw [min_eq_left h1] at hgt; linarith
            · exact min_eq_right h1.le
          have hgtQ : Q < Iε + σ.react qstar wε Iε s Q := by linarith
          rw [min_eq_right hgtQ.le, hIs_eq, show Iε + (Q - Iε) = Q by ring] at hge_r
          have hc_pos : 0 < P.cost qstar := by rw [hc_qs]; exact hws_pos
          have := mul_lt_mul_of_pos_left hgtQ hc_pos
          linarith
      rw [hreq]; dsimp [Is]
      rcases le_or_gt Qbar (Q - Iε) with h1 | h1
      · rw [min_eq_left h1, min_eq_left (by linarith), min_eq_right (by linarith)]
      · rw [min_eq_right h1.le, show Iε + (Q - Iε) = Q by ring, min_self, min_eq_left (by linarith)]
  have hov_g_ge : (qstar * P.θH - wε) * P.αg ≤
      σ.orderValue P qstar wε Iε .good (σ.order qstar wε Iε .good) := by
    have h1 := (hpost.2.2 qstar wε Iε .good hqs_pos.le hwε0 hIε0).2 P.αg hαg0.le
    have hm_bds : 0 ≤ σ.made qstar wε Iε .good P.αg ∧ σ.made qstar wε Iε .good P.αg ≤ Qbar := by
      unfold Profile.made inSeason
      rcases le_or_gt P.αg Iε with hle | hgt
      · rw [if_pos hle]; exact ⟨le_refl 0, hQ0⟩
      · rw [if_neg (not_le_of_gt hgt)]
        obtain ⟨hr0, hrQ, _⟩ := hpost.2.1 qstar wε Iε .good P.αg hqs_pos.le hwε0 hIε0 hgt
        exact ⟨hr0, hrQ⟩
    have hp_opt := (hpost.1 qstar wε Iε .good P.αg (σ.made qstar wε Iε .good P.αg)
      hqs_pos.le hwε0 hIε0 hαg0.le hm_bds.1 hm_bds.2).2 (qstar * P.θH) (mul_pos hqs_pos hθH).le
    have hrec_raw : σ.recv qstar wε Iε .good P.αg = P.αg := by
      rw [hrecv_ε .good P.αg hαg0.le, min_eq_left (by dsimp [S_Q]; linarith)]
    have hrm_eq : received Iε P.αg (σ.made qstar wε Iε .good P.αg) = P.αg := by
      have hrec := hrec_raw
      unfold Profile.recv received at hrec
      unfold Profile.made received inSeason
      rcases le_or_gt P.αg Iε with h2 | h2
      · rw [if_pos h2]
      · rw [if_neg (not_le_of_gt h2), if_neg (not_le_of_gt h2)]; rw [if_neg (not_le_of_gt h2)] at hrec; exact hrec
    have hqLH : qstar * P.θL < qstar * P.θH := mul_lt_mul_of_pos_left hθLH hqs_pos
    unfold Profile.orderValue Profile.priceAfter at h1
    rw [hrec_raw] at h1
    rw [hrm_eq] at hp_opt
    have hlhs : P.retailerState qstar wε .good P.αg (qstar * P.θH) = (qstar * P.θH - wε) * P.αg := by
      unfold Params.retailerState Params.demand Params.alpha
      rw [if_neg (not_le_of_gt hqLH), if_pos (le_refl _), zero_add, min_self]; ring
    rw [hlhs] at hp_opt
    exact le_trans hp_opt h1
  have hSQ0 : 0 ≤ S_Q := by dsimp [S_Q]; linarith
  have hov_b_ge : (qstar * P.θL - wε) * S_Q ≤
      σ.orderValue P qstar wε Iε .bad (σ.order qstar wε Iε .bad) := by
    have h1 := (hpost.2.2 qstar wε Iε .bad hqs_pos.le hwε0 hIε0).2 S_Q hSQ0
    have hm_bds : 0 ≤ σ.made qstar wε Iε .bad S_Q ∧ σ.made qstar wε Iε .bad S_Q ≤ Qbar := by
      unfold Profile.made inSeason
      rcases le_or_gt S_Q Iε with hle | hgt
      · rw [if_pos hle]; exact ⟨le_refl 0, hQ0⟩
      · rw [if_neg (not_le_of_gt hgt)]
        obtain ⟨hr0, hrQ, _⟩ := hpost.2.1 qstar wε Iε .bad S_Q hqs_pos.le hwε0 hIε0 hgt
        exact ⟨hr0, hrQ⟩
    have hp_opt := (hpost.1 qstar wε Iε .bad S_Q (σ.made qstar wε Iε .bad S_Q)
      hqs_pos.le hwε0 hIε0 hSQ0 hm_bds.1 hm_bds.2).2 (qstar * P.θL) (mul_pos hqs_pos hθL).le
    have hrec_raw : σ.recv qstar wε Iε .bad S_Q = S_Q := by
      rw [hrecv_ε .bad S_Q hSQ0, min_self]
    have hrm_eq : received Iε S_Q (σ.made qstar wε Iε .bad S_Q) = S_Q := by
      have hrec := hrec_raw
      unfold Profile.recv received at hrec
      unfold Profile.made received inSeason
      rcases le_or_gt S_Q Iε with h2 | h2
      · rw [if_pos h2]
      · rw [if_neg (not_le_of_gt h2), if_neg (not_le_of_gt h2)]; rw [if_neg (not_le_of_gt h2)] at hrec; exact hrec
    have hqLH : qstar * P.θL < qstar * P.θH := mul_lt_mul_of_pos_left hθLH hqs_pos
    unfold Profile.orderValue Profile.priceAfter at h1
    rw [hrec_raw] at h1
    rw [hrm_eq] at hp_opt
    have hlhs : P.retailerState qstar wε .bad S_Q (qstar * P.θL) = (qstar * P.θL - wε) * S_Q := by
      unfold Params.retailerState Params.demand Params.alpha
      rw [if_pos (le_refl _), if_pos hqLH.le, sub_add_cancel,
        min_eq_right (by dsimp [S_Q]; linarith : S_Q ≤ 1)]
      ring
    rw [hlhs] at hp_opt
    exact le_trans hp_opt h1
  have hrv_wε : P.V_OS Qbar - (P.ρ * P.αg + (1 - P.ρ) * S_Q) * ε ≤
      σ.retailerValue P qstar wε := by
    have hid_qs := val_qos_tb P Qbar hk hQ1.le hDS
    unfold Profile.retailerValue Params.prob
    change _ ≤ P.ρ * σ.orderValue P qstar wε Iε .good _ +
      (1 - P.ρ) * σ.orderValue P qstar wε Iε .bad _
    have := mul_le_mul_of_nonneg_left hov_g_ge hρ0.le
    have := mul_le_mul_of_nonneg_left hov_b_ge h1ρ.le
    dsimp [wε, qstar, wstar, S_Q] at *
    linarith
  have hopt_ε := hropt qstar wε hqs_pos.le hwε0
  have hε_bound : (P.ρ * P.αg + (1 - P.ρ) * S_Q) * ε ≤
      (P.V_OS Qbar - σ.retailerValue P σ.q σ.w) / 2 := by
    have := mul_le_mul_of_nonneg_left hε_3 hDS.le
    dsimp [δ3, S_Q] at this ⊢
    have heq : (P.ρ * P.αg + (1 - P.ρ) * (P.αg + Qbar)) *
        ((P.V_OS Qbar - σ.retailerValue P σ.q σ.w) /
          (2 * (P.ρ * P.αg + (1 - P.ρ) * (P.αg + Qbar)))) =
        (P.V_OS Qbar - σ.retailerValue P σ.q σ.w) / 2 := by
      field_simp [hDS.ne']
    linarith
  dsimp [S_Q] at hrv_wε
  linarith

private lemma lb_oo_tb (P : Params) (hStand : P.Standing) (hFocus : P.Focus)
    (Qbar : ℝ) (hQ0 : 0 ≤ Qbar) (hQ1 : Qbar < 1 - P.αg)
    (σ : Profile) (hSPE : IsSPE P Qbar σ) :
    P.V_OO ≤ σ.retailerValue P σ.q σ.w := by
  rcases hSPE with ⟨hpost, hinv, _hq0, _hw0, hropt⟩
  obtain ⟨_hDS, _hYS_pos, hX_pos, _hX_le, _hYS_le, _hYS_lt, hX_lt, _hYS_f, hX_focus⟩ :=
    focus_Y_props_tb P hStand hFocus (P.αg + Qbar) (by linarith) (by linarith)
  rcases hStand with ⟨hθL, hθLH, hk, hρ0, hρ1, hαb0, hαb_lt, hαg_gt, hαg1⟩
  have hStand : P.Standing := ⟨hθL, hθLH, hk, hρ0, hρ1, hαb0, hαb_lt, hαg_gt, hαg1⟩
  have hθH : 0 < P.θH := lt_trans hθL hθLH
  have hαg0 : 0 < P.αg := pos_of_mul_pos_left (lt_trans hθL hαg_gt) hθH.le
  have hαb_αg : P.αb < P.αg := lt_of_mul_lt_mul_right (lt_trans hαb_lt hαg_gt) hθH.le
  have h1ρ : 0 < 1 - P.ρ := sub_pos.mpr hρ1
  have hD1 : 0 < P.ρ * P.αg + 1 - P.ρ := by
    have : 0 < P.ρ * P.αg := mul_pos hρ0 hαg0
    linarith
  obtain ⟨hc_oo, hc1ρ_oo, hval_oo, _⟩ := val_qoo_tb P Qbar hk h1ρ hD1
  let S_Q := P.αg + Qbar
  let qstar := (1 - P.ρ) * P.X / (2 * P.k)
  let wstar := (1 - P.ρ) * P.X ^ 2 / (4 * P.k)
  have hqs_pos : 0 < qstar := div_pos (mul_pos h1ρ hX_pos) (by linarith)
  have hws_pos : 0 < wstar := div_pos (mul_pos h1ρ (pow_pos hX_pos 2)) (by linarith)
  have hc_lt_ws : P.cost qstar < wstar := by
    dsimp [qstar, wstar]
    rw [hc_oo]
    have hsq_lt : (1 - P.ρ) ^ 2 < 1 - P.ρ := by
      have := mul_lt_mul_of_pos_left (by linarith : 1 - P.ρ < 1) h1ρ
      linarith
    exact div_lt_div_of_pos_right (mul_lt_mul_of_pos_right hsq_lt (pow_pos hX_pos 2)) (by linarith)
  have hws_lt_L : wstar < qstar * P.θL := by
    dsimp [qstar, wstar]
    rw [div_mul_eq_mul_div, div_lt_div_iff₀ (by linarith : 0 < 4 * P.k) (by linarith : 0 < 2 * P.k)]
    have := mul_lt_mul_of_pos_left hX_lt (mul_pos (mul_pos h1ρ hX_pos) hk)
    linarith
  have hlow_qs : (qstar * P.θH - wstar) * P.αb < (qstar * P.θL - wstar) * S_Q := by
    dsimp [qstar, wstar]
    have hid1 : (1 - P.ρ) * P.X / (2 * P.k) * P.θH - (1 - P.ρ) * P.X ^ 2 / (4 * P.k) =
        (1 - P.ρ) * P.X / (4 * P.k) * (2 * P.θH - P.X) := by field_simp [hk.ne']; ring
    have hid2 : (1 - P.ρ) * P.X / (2 * P.k) * P.θL - (1 - P.ρ) * P.X ^ 2 / (4 * P.k) =
        (1 - P.ρ) * P.X / (4 * P.k) * (2 * P.θL - P.X) := by field_simp [hk.ne']; ring
    rw [hid1, hid2]
    have hfac : 0 < (1 - P.ρ) * P.X / (4 * P.k) := div_pos (mul_pos h1ρ hX_pos) (by linarith)
    have hlt_inner : (2 * P.θH - P.X) * P.αb < (2 * P.θL - P.X) * S_Q := by dsimp [S_Q] at *; linarith
    have := mul_lt_mul_of_pos_left hlt_inner hfac
    linarith
  by_contra hlt_c
  have hgap : 0 < P.V_OO - σ.retailerValue P σ.q σ.w := sub_pos.mpr (lt_of_not_ge hlt_c)
  let δ1 := (qstar * P.θL - wstar) * S_Q - (qstar * P.θH - wstar) * P.αb
  have hδ1_pos : 0 < δ1 := sub_pos.mpr hlow_qs
  let δ2 := qstar * P.θL - wstar
  have hδ2_pos : 0 < δ2 := sub_pos.mpr hws_lt_L
  let δ3 := (P.V_OO - σ.retailerValue P σ.q σ.w) / (2 * (P.ρ * P.αg + 1 - P.ρ))
  have hδ3_pos : 0 < δ3 := div_pos hgap (mul_pos (by norm_num) hD1)
  let ε := min (min (δ1 / 2) (δ2 / 2)) δ3
  have hε_pos : 0 < ε := lt_min (lt_min (half_pos hδ1_pos) (half_pos hδ2_pos)) hδ3_pos
  have hε_1 : ε ≤ δ1 / 2 := le_trans (min_le_left _ _) (min_le_left _ _)
  have hε_3 : ε ≤ δ3 := min_le_right _ _
  let wε := wstar + ε
  have hwε_gt_c : P.cost qstar < wε := lt_trans hc_lt_ws (by dsimp [wε]; linarith)
  have hwε_gt_c1ρ : P.cost qstar / (1 - P.ρ) < wε := by
    dsimp [qstar, wε]; rw [hc1ρ_oo]; dsimp [wstar]; linarith
  have hwε0 : 0 ≤ wε := (lt_trans hws_pos (by dsimp [wε]; linarith)).le
  have hlow_ε : (qstar * P.θH - wε) * P.αb < (qstar * P.θL - wε) * S_Q := by
    have hSab : S_Q - P.αb ≤ 1 := by dsimp [S_Q]; linarith
    have : ε * (S_Q - P.αb) ≤ ε := mul_le_of_le_one_right hε_pos.le hSab
    dsimp [wε, δ1] at *; linarith
  have hresp := (supplier_response_medium P hStand Qbar hQ0 hQ1 σ hpost qstar wε hqs_pos
    hwε_gt_c hlow_ε).2.1 hwε_gt_c1ρ
  have hmem : σ.inv qstar wε ∈ ({1 - Qbar} : Set ℝ) := by
    rw [← hresp]
    exact hinv qstar wε hqs_pos.le hwε0
  have hIε_eq : σ.inv qstar wε = 1 - Qbar := Set.mem_singleton_iff.mp hmem
  let Iε := σ.inv qstar wε
  have hIε0 : 0 ≤ Iε := by dsimp [Iε]; rw [hIε_eq]; linarith
  have hSε_eq : Iε + Qbar = 1 := by dsimp [Iε]; rw [hIε_eq]; ring
  have hrecv_ε : ∀ s : State, ∀ Q : ℝ, 0 ≤ Q → σ.recv qstar wε Iε s Q = min Q 1 := by
    intro s Q _hQ
    rw [← hSε_eq]
    unfold Profile.recv received
    rcases le_or_gt Q Iε with hQI | hIQ
    · rw [if_pos hQI, min_eq_left (by linarith)]
    · rw [if_neg (not_le_of_gt hIQ)]
      obtain ⟨_hr0, _hrQ, hropt_r⟩ := hpost.2.1 qstar wε Iε s Q hqs_pos.le hwε0 hIε0 hIQ
      let Is := min Qbar (Q - Iε)
      have hge_r := hropt_r Is (le_min hQ0 (sub_pos.mpr hIQ).le) (min_le_left _ _)
      have hIIs : Iε + Is ≤ Q := by have := min_le_right Qbar (Q - Iε); dsimp [Is]; linarith
      have hreq : σ.react qstar wε Iε s Q = Is := by
        unfold Params.supplierState received at hge_r
        simp only [if_neg (not_le_of_gt hIQ), min_eq_left hIIs] at hge_r
        rcases lt_trichotomy (σ.react qstar wε Iε s Q) Is with hlt | heq | hgt
        · exfalso
          rw [min_eq_left (by linarith)] at hge_r
          have := mul_lt_mul_of_pos_left (by linarith : Iε + σ.react qstar wε Iε s Q < Iε + Is)
            (sub_pos.mpr hwε_gt_c)
          linarith
        · exact heq
        · exfalso
          have hIs_eq : Is = Q - Iε := by
            dsimp [Is] at hgt ⊢
            rcases le_or_gt Qbar (Q - Iε) with h1 | h1
            · rw [min_eq_left h1] at hgt; linarith
            · exact min_eq_right h1.le
          have hgtQ : Q < Iε + σ.react qstar wε Iε s Q := by linarith
          rw [min_eq_right hgtQ.le, hIs_eq, show Iε + (Q - Iε) = Q by ring] at hge_r
          have hc_pos : 0 < P.cost qstar := mul_pos hk (pow_pos hqs_pos 2)
          have := mul_lt_mul_of_pos_left hgtQ hc_pos
          linarith
      rw [hreq]; dsimp [Is]
      rcases le_or_gt Qbar (Q - Iε) with h1 | h1
      · rw [min_eq_left h1, min_eq_left (by linarith), min_eq_right (by linarith)]
      · rw [min_eq_right h1.le, show Iε + (Q - Iε) = Q by ring, min_self, min_eq_left (by linarith)]
  have hov_g_ge : (qstar * P.θH - wε) * P.αg ≤
      σ.orderValue P qstar wε Iε .good (σ.order qstar wε Iε .good) := by
    have h1 := (hpost.2.2 qstar wε Iε .good hqs_pos.le hwε0 hIε0).2 P.αg hαg0.le
    have hm_bds : 0 ≤ σ.made qstar wε Iε .good P.αg ∧ σ.made qstar wε Iε .good P.αg ≤ Qbar := by
      unfold Profile.made inSeason
      rcases le_or_gt P.αg Iε with hle | hgt
      · rw [if_pos hle]; exact ⟨le_refl 0, hQ0⟩
      · rw [if_neg (not_le_of_gt hgt)]
        obtain ⟨hr0, hrQ, _⟩ := hpost.2.1 qstar wε Iε .good P.αg hqs_pos.le hwε0 hIε0 hgt
        exact ⟨hr0, hrQ⟩
    have hp_opt := (hpost.1 qstar wε Iε .good P.αg (σ.made qstar wε Iε .good P.αg)
      hqs_pos.le hwε0 hIε0 hαg0.le hm_bds.1 hm_bds.2).2 (qstar * P.θH) (mul_pos hqs_pos hθH).le
    have hrec_raw : σ.recv qstar wε Iε .good P.αg = P.αg := by
      rw [hrecv_ε .good P.αg hαg0.le, min_eq_left hαg1.le]
    have hrm_eq : received Iε P.αg (σ.made qstar wε Iε .good P.αg) = P.αg := by
      have hrec := hrec_raw
      unfold Profile.recv received at hrec
      unfold Profile.made received inSeason
      rcases le_or_gt P.αg Iε with h2 | h2
      · rw [if_pos h2]
      · rw [if_neg (not_le_of_gt h2), if_neg (not_le_of_gt h2)]; rw [if_neg (not_le_of_gt h2)] at hrec; exact hrec
    have hqLH : qstar * P.θL < qstar * P.θH := mul_lt_mul_of_pos_left hθLH hqs_pos
    unfold Profile.orderValue Profile.priceAfter at h1
    rw [hrec_raw] at h1
    rw [hrm_eq] at hp_opt
    have hlhs : P.retailerState qstar wε .good P.αg (qstar * P.θH) = (qstar * P.θH - wε) * P.αg := by
      unfold Params.retailerState Params.demand Params.alpha
      rw [if_neg (not_le_of_gt hqLH), if_pos (le_refl _), zero_add, min_self]; ring
    rw [hlhs] at hp_opt
    exact le_trans hp_opt h1
  have hov_b_ge : qstar * P.θL - wε ≤
      σ.orderValue P qstar wε Iε .bad (σ.order qstar wε Iε .bad) := by
    have h1 := (hpost.2.2 qstar wε Iε .bad hqs_pos.le hwε0 hIε0).2 1 zero_le_one
    have hm_bds : 0 ≤ σ.made qstar wε Iε .bad 1 ∧ σ.made qstar wε Iε .bad 1 ≤ Qbar := by
      unfold Profile.made inSeason
      rcases le_or_gt 1 Iε with hle | hgt
      · rw [if_pos hle]; exact ⟨le_refl 0, hQ0⟩
      · rw [if_neg (not_le_of_gt hgt)]
        obtain ⟨hr0, hrQ, _⟩ := hpost.2.1 qstar wε Iε .bad 1 hqs_pos.le hwε0 hIε0 hgt
        exact ⟨hr0, hrQ⟩
    have hp_opt := (hpost.1 qstar wε Iε .bad 1 (σ.made qstar wε Iε .bad 1)
      hqs_pos.le hwε0 hIε0 zero_le_one hm_bds.1 hm_bds.2).2 (qstar * P.θL) (mul_pos hqs_pos hθL).le
    have hrec_raw : σ.recv qstar wε Iε .bad 1 = 1 := by
      rw [hrecv_ε .bad 1 zero_le_one, min_self]
    have hrm_eq : received Iε 1 (σ.made qstar wε Iε .bad 1) = 1 := by
      have hrec := hrec_raw
      unfold Profile.recv received at hrec
      unfold Profile.made received inSeason
      rcases le_or_gt 1 Iε with h2 | h2
      · rw [if_pos h2]
      · rw [if_neg (not_le_of_gt h2), if_neg (not_le_of_gt h2)]; rw [if_neg (not_le_of_gt h2)] at hrec; exact hrec
    have hqLH : qstar * P.θL < qstar * P.θH := mul_lt_mul_of_pos_left hθLH hqs_pos
    unfold Profile.orderValue Profile.priceAfter at h1
    rw [hrec_raw] at h1
    rw [hrm_eq] at hp_opt
    have hlhs : P.retailerState qstar wε .bad 1 (qstar * P.θL) = qstar * P.θL - wε := by
      unfold Params.retailerState Params.demand Params.alpha
      rw [if_pos (le_refl _), if_pos hqLH.le, sub_add_cancel, min_self]; ring
    rw [hlhs] at hp_opt
    exact le_trans hp_opt h1
  have hrv_wε : P.V_OO - (P.ρ * P.αg + 1 - P.ρ) * ε ≤ σ.retailerValue P qstar wε := by
    unfold Profile.retailerValue Params.prob
    change _ ≤ P.ρ * σ.orderValue P qstar wε Iε .good _ +
      (1 - P.ρ) * σ.orderValue P qstar wε Iε .bad _
    have := mul_le_mul_of_nonneg_left hov_g_ge hρ0.le
    have := mul_le_mul_of_nonneg_left hov_b_ge h1ρ.le
    dsimp [wε, qstar, wstar] at *
    linarith
  have hopt_ε := hropt qstar wε hqs_pos.le hwε0
  have hε_bound : (P.ρ * P.αg + 1 - P.ρ) * ε ≤ (P.V_OO - σ.retailerValue P σ.q σ.w) / 2 := by
    have := mul_le_mul_of_nonneg_left hε_3 hD1.le
    dsimp [δ3] at this
    have heq : (P.ρ * P.αg + 1 - P.ρ) *
        ((P.V_OO - σ.retailerValue P σ.q σ.w) / (2 * (P.ρ * P.αg + 1 - P.ρ))) =
        (P.V_OO - σ.retailerValue P σ.q σ.w) / 2 := by
      field_simp [hD1.ne']
    linarith
  linarith

private lemma exists_med_os_tb (P : Params) (hP : P.Dom)
    (Qbar : ℝ) (hQ0 : 0 ≤ Qbar) (hQ1 : Qbar < 1 - P.αg)
    (hV_os : P.V_OO ≤ P.V_OS Qbar) :
    ∃ e : Outcome, IsEquilibrium P Qbar e := by
  have hDom := hP
  rcases hP with ⟨hStand, hFocus, _hHOD⟩
  obtain ⟨hDS, hYS_pos, _hX_pos, _hX_le, _hYS_le, hYS_lt, _hX_lt, hYS_focus, _hX_focus⟩ :=
    focus_Y_props_tb P hStand hFocus (P.αg + Qbar) (by linarith) (by linarith)
  rcases hStand with ⟨hθL, hθLH, hk, hρ0, hρ1, hαb0, hαb_lt, hαg_gt, hαg1⟩
  have hStand : P.Standing := ⟨hθL, hθLH, hk, hρ0, hρ1, hαb0, hαb_lt, hαg_gt, hαg1⟩
  have hθH : 0 < P.θH := lt_trans hθL hθLH
  have hαg0 : 0 < P.αg := pos_of_mul_pos_left (lt_trans hθL hαg_gt) hθH.le
  have hαb_αg : P.αb < P.αg := lt_of_mul_lt_mul_right (lt_trans hαb_lt hαg_gt) hθH.le
  have h1ρ : 0 < 1 - P.ρ := sub_pos.mpr hρ1
  let S_Q := P.αg + Qbar
  let qstar := P.Y S_Q / (2 * P.k)
  let wstar := P.Y S_Q ^ 2 / (4 * P.k)
  have hqs_pos : 0 < qstar := div_pos hYS_pos (by linarith)
  have hws_pos : 0 < wstar := div_pos (pow_pos hYS_pos 2) (by linarith)
  have hc_qs : P.cost qstar = wstar := by
    dsimp [qstar, wstar]; unfold Params.cost; field_simp [hk.ne']; ring
  have hws_lt_L : wstar < qstar * P.θL := by
    dsimp [qstar, wstar]
    rw [div_mul_eq_mul_div, div_lt_div_iff₀ (by linarith : 0 < 4 * P.k) (by linarith : 0 < 2 * P.k)]
    have := mul_lt_mul_of_pos_left hYS_lt (mul_pos hYS_pos hk)
    dsimp [S_Q] at *; linarith
  have hws_lt_H : wstar < qstar * P.θH :=
    lt_trans hws_lt_L (mul_lt_mul_of_pos_left hθLH hqs_pos)
  have hlow_qs : (qstar * P.θH - wstar) * P.αb < (qstar * P.θL - wstar) * S_Q := by
    dsimp [qstar, wstar]
    rw [os_margin_id_tb (P.Y S_Q) P.θH P.k hk.ne', os_margin_id_tb (P.Y S_Q) P.θL P.k hk.ne']
    have hfac : 0 < P.Y S_Q / (4 * P.k) := div_pos hYS_pos (by linarith)
    have hlt_inner : (2 * P.θH - P.Y S_Q) * P.αb < (2 * P.θL - P.Y S_Q) * S_Q := by
      dsimp [S_Q] at *; linarith
    have := mul_lt_mul_of_pos_left hlt_inner hfac
    linarith
  let σ0 := fullProfile_tb P Qbar qstar wstar P.αg
  have hpost0 := isPostSPE_full_tb P hStand Qbar hQ0 qstar wstar P.αg
  have hinv0 := isInvSPE_full_tb P hStand Qbar hQ0 qstar wstar P.αg hαg0.le
  have hSQ_le1 : S_Q ≤ 1 := by dsimp [S_Q]; linarith
  have hord_g : (basePost_tb P Qbar).order qstar wstar P.αg .good = P.αg := by
    unfold basePost_tb; dsimp only
    rw [if_pos hc_qs.le, Params.alpha, min_eq_left (by linarith : P.αg ≤ P.αg + Qbar),
      min_eq_right hSQ_le1]
    have hvH : 0 < (qstar * P.θH - wstar) * P.αg := mul_pos (sub_pos.mpr hws_lt_H) hαg0
    have hvL : (qstar * P.θL - wstar) * (P.αg + Qbar) < (qstar * P.θH - wstar) * P.αg := by
      have hle1 : (qstar * P.θL - wstar) * (P.αg + Qbar) ≤ qstar * P.θL - wstar := by
        have := mul_le_mul_of_nonneg_left hSQ_le1 (sub_pos.mpr hws_lt_L).le
        dsimp [S_Q] at this; linarith
      have h2 : qstar * P.θL < qstar * (P.αg * P.θH) := mul_lt_mul_of_pos_left hαg_gt hqs_pos
      have h3 : wstar * P.αg ≤ wstar := by
        have := mul_le_mul_of_nonneg_left hαg1.le hws_pos.le; linarith
      linarith
    rw [if_neg (not_le_of_gt (lt_of_lt_of_le hvH (le_max_left _ _))),
      if_neg (not_le_of_gt hvL)]
  have hord_b : (basePost_tb P Qbar).order qstar wstar P.αg .bad = S_Q := by
    unfold basePost_tb; dsimp only
    rw [if_pos hc_qs.le, Params.alpha, min_eq_left (by linarith : P.αb ≤ P.αg + Qbar),
      min_eq_right hSQ_le1]
    have hvL : 0 < (qstar * P.θL - wstar) * (P.αg + Qbar) :=
      mul_pos (sub_pos.mpr hws_lt_L) (by linarith)
    rw [if_neg (not_le_of_gt (lt_of_lt_of_le hvL (le_max_right _ _))),
      if_pos (by dsimp [S_Q] at hlow_qs; exact hlow_qs.le)]
  have hI0_eq : σ0.inv qstar wstar = P.αg := by
    change argmaxList_tb (fun I => (basePost_tb P Qbar).supplierValue P qstar wstar I)
      (P.αg :: candList_tb P Qbar qstar wstar) = P.αg
    apply argmaxList_tb_head
    intro z _hz
    have hc_mul : ∀ x : ℝ, P.cost qstar * x = wstar * x := fun x => by rw [hc_qs]
    have hz_le : (basePost_tb P Qbar).supplierValue P qstar wstar z ≤ 0 := by
      have hst : ∀ s : State, (basePost_tb P Qbar).supplierStateValue P qstar wstar z s ≤ 0 := by
        intro s
        let Qz := (basePost_tb P Qbar).order qstar wstar z s
        have hre : (basePost_tb P Qbar).react qstar wstar z s Qz = min Qbar (max 0 (Qz - z)) := by
          change (if P.cost qstar ≤ wstar then min Qbar (max 0 (Qz - z)) else 0) = _
          rw [if_pos hc_qs.le]
        change wstar * received z Qz ((basePost_tb P Qbar).react qstar wstar z s Qz) -
          P.cost qstar * (z + inSeason z Qz ((basePost_tb P Qbar).react qstar wstar z s Qz)) ≤ 0
        rw [hre, hc_mul]
        unfold received inSeason
        split_ifs with h1
        · have := mul_le_mul_of_nonneg_left h1 hws_pos.le; linarith
        · have := mul_le_mul_of_nonneg_left
            (min_le_left (z + min Qbar (max 0 (Qz - z))) Qz) hws_pos.le
          linarith
      unfold Profile.supplierValue Params.prob
      have := mul_nonpos_of_nonneg_of_nonpos hρ0.le (hst .good)
      have := mul_nonpos_of_nonneg_of_nonpos h1ρ.le (hst .bad)
      linarith
    have hag_eq0 : (basePost_tb P Qbar).supplierValue P qstar wstar P.αg = 0 := by
      have hst_g : (basePost_tb P Qbar).supplierStateValue P qstar wstar P.αg .good = 0 := by
        unfold Profile.supplierStateValue Params.supplierState Profile.recv Profile.made
          received inSeason
        rw [hord_g, if_pos (le_refl P.αg), if_pos (le_refl P.αg), add_zero, hc_mul, sub_self]
      have hst_b : (basePost_tb P Qbar).supplierStateValue P qstar wstar P.αg .bad = 0 := by
        unfold Profile.supplierStateValue Params.supplierState Profile.recv Profile.made
          received inSeason
        rw [hord_b]
        rcases eq_or_lt_of_le hQ0 with hQ_z | hQ_p
        · have hSQ_ag : S_Q = P.αg := by dsimp [S_Q]; linarith
          rw [hSQ_ag, if_pos (le_refl P.αg), if_pos (le_refl P.αg), add_zero, hc_mul, sub_self]
        · have hgt_b : P.αg < S_Q := by dsimp [S_Q]; linarith
          have hre_b : (basePost_tb P Qbar).react qstar wstar P.αg .bad S_Q = Qbar := by
            change (if P.cost qstar ≤ wstar then min Qbar (max 0 (S_Q - P.αg)) else 0) = Qbar
            rw [if_pos hc_qs.le, show S_Q - P.αg = Qbar by dsimp [S_Q]; ring,
              max_eq_right hQ0, min_self]
          rw [if_neg (not_le_of_gt hgt_b), if_neg (not_le_of_gt hgt_b), hre_b,
            show P.αg + Qbar = S_Q from rfl, min_self, hc_mul, sub_self]
      unfold Profile.supplierValue Params.prob
      rw [hst_g, hst_b]; ring
    linarith
  have hrv0_eq : σ0.retailerValue P qstar wstar = P.V_OS Qbar := by
    have hord_g0 : σ0.order qstar wstar P.αg .good = P.αg := hord_g
    have hord_b0 : σ0.order qstar wstar P.αg .bad = S_Q := hord_b
    have hrec_g : σ0.recv qstar wstar P.αg .good P.αg = P.αg := by
      unfold Profile.recv received; rw [if_pos (le_refl _)]
    have hmade_g : σ0.made qstar wstar P.αg .good P.αg = 0 := by
      unfold Profile.made inSeason; rw [if_pos (le_refl _)]
    have hrec_b : σ0.recv qstar wstar P.αg .bad S_Q = S_Q := by
      unfold Profile.recv received
      rcases eq_or_lt_of_le hQ0 with hQ_z | hQ_p
      · rw [if_pos (by dsimp [S_Q]; linarith)]
      · rw [if_neg (not_le_of_gt (by dsimp [S_Q]; linarith : P.αg < S_Q))]
        change min (P.αg + (if P.cost qstar ≤ wstar then min Qbar (max 0 (S_Q - P.αg)) else 0)) S_Q = S_Q
        rw [if_pos hc_qs.le, show S_Q - P.αg = Qbar by dsimp [S_Q]; ring,
          max_eq_right hQ0, min_self, show P.αg + Qbar = S_Q from rfl, min_self]
    have hrm_b : received P.αg S_Q (σ0.made qstar wstar P.αg .bad S_Q) = S_Q := by
      have h1 := hrec_b
      unfold Profile.recv received at h1
      unfold Profile.made received inSeason
      rcases le_or_gt S_Q P.αg with h2 | h2
      · rw [if_pos h2]
      · rw [if_neg (not_le_of_gt h2), if_neg (not_le_of_gt h2)]; rw [if_neg (not_le_of_gt h2)] at h1; exact h1
    have hqLH : qstar * P.θL < qstar * P.θH := mul_lt_mul_of_pos_left hθLH hqs_pos
    have hpg : σ0.priceAfter qstar wstar P.αg .good P.αg = qstar * P.θH := by
      unfold Profile.priceAfter; rw [hmade_g]
      change (let R := received P.αg P.αg 0
        if (qstar * P.θL) * min 1 R ≤ (qstar * P.θH) * min P.αg R then qstar * P.θH else qstar * P.θL) = _
      have hR : received P.αg P.αg 0 = P.αg := by unfold received; rw [if_pos (le_refl _)]
      dsimp only
      rw [hR, min_eq_right hαg1.le, min_self,
        if_pos (mul_le_mul_of_nonneg_right hqLH.le hαg0.le)]
    have hpb : σ0.priceAfter qstar wstar P.αg .bad S_Q = qstar * P.θL := by
      change (let R := received P.αg S_Q (σ0.made qstar wstar P.αg .bad S_Q)
        if (qstar * P.θL) * min 1 R ≤ (qstar * P.θH) * min P.αb R then qstar * P.θH else qstar * P.θL) = _
      dsimp only
      rw [hrm_b, min_eq_right hSQ_le1, min_eq_left (by dsimp [S_Q]; linarith : P.αb ≤ S_Q)]
      have hlt_b : (qstar * P.θH) * P.αb < (qstar * P.θL) * S_Q := by
        have : wstar * P.αb < wstar * S_Q :=
          mul_lt_mul_of_pos_left (by dsimp [S_Q]; linarith) hws_pos
        linarith
      rw [if_neg (not_le_of_gt hlt_b)]
    unfold Profile.retailerValue Params.prob Profile.orderValue Params.retailerState Params.demand
    rw [hI0_eq, hord_g0, hord_b0, hrec_g, hrec_b, hpg, hpb, Params.alpha, Params.alpha,
      if_neg (not_le_of_gt hqLH), if_pos (le_refl _), zero_add, min_self,
      if_pos (le_refl _), if_pos hqLH.le, sub_add_cancel, min_eq_right hSQ_le1]
    have hval := val_qos_tb P Qbar hk hQ1.le hDS
    dsimp [qstar, wstar, S_Q]
    linarith
  have hSPE0 : IsSPE P Qbar σ0 := by
    refine ⟨hpost0, hinv0, hqs_pos.le, hws_pos.le, fun q w hq hw => ?_⟩
    change σ0.retailerValue P q w ≤ σ0.retailerValue P qstar wstar
    rw [hrv0_eq, ← max_eq_left hV_os]
    exact (ub_char_med_tb P hDom Qbar hQ0 hQ1 σ0 hpost0 hinv0 q w hq hw).1
  exact ⟨σ0.outcome P, σ0, hSPE0, rfl⟩

private lemma exists_med_oo_tb (P : Params) (hP : P.Dom)
    (Qbar : ℝ) (hQ0 : 0 ≤ Qbar) (hQ1 : Qbar < 1 - P.αg)
    (hV_oo : P.V_OS Qbar ≤ P.V_OO) :
    ∃ e : Outcome, IsEquilibrium P Qbar e := by
  have hDom := hP
  rcases hP with ⟨hStand, hFocus, _hHOD⟩
  obtain ⟨_hDS, _hYS_pos, hX_pos, _hX_le, _hYS_le, _hYS_lt, hX_lt, _hYS_focus, hX_focus⟩ :=
    focus_Y_props_tb P hStand hFocus (P.αg + Qbar) (by linarith) (by linarith)
  rcases hStand with ⟨hθL, hθLH, hk, hρ0, hρ1, hαb0, hαb_lt, hαg_gt, hαg1⟩
  have hStand : P.Standing := ⟨hθL, hθLH, hk, hρ0, hρ1, hαb0, hαb_lt, hαg_gt, hαg1⟩
  have hθH : 0 < P.θH := lt_trans hθL hθLH
  have hαg0 : 0 < P.αg := pos_of_mul_pos_left (lt_trans hθL hαg_gt) hθH.le
  have hαb_αg : P.αb < P.αg := lt_of_mul_lt_mul_right (lt_trans hαb_lt hαg_gt) hθH.le
  have hαb1 : P.αb < 1 := lt_trans hαb_αg hαg1
  have h1ρ : 0 < 1 - P.ρ := sub_pos.mpr hρ1
  have hD1 : 0 < P.ρ * P.αg + 1 - P.ρ := by
    have : 0 < P.ρ * P.αg := mul_pos hρ0 hαg0
    linarith
  obtain ⟨hc_oo, hc1ρ_oo, hval_oo, _⟩ := val_qoo_tb P Qbar hk h1ρ hD1
  let S_Q := P.αg + Qbar
  let qstar := (1 - P.ρ) * P.X / (2 * P.k)
  let wstar := (1 - P.ρ) * P.X ^ 2 / (4 * P.k)
  have hqs_pos : 0 < qstar := div_pos (mul_pos h1ρ hX_pos) (by linarith)
  have hws_pos : 0 < wstar := div_pos (mul_pos h1ρ (pow_pos hX_pos 2)) (by linarith)
  have hc_lt_ws : P.cost qstar < wstar := by
    dsimp [qstar, wstar]; rw [hc_oo]
    have hsq_lt : (1 - P.ρ) ^ 2 < 1 - P.ρ := by
      have := mul_lt_mul_of_pos_left (by linarith : 1 - P.ρ < 1) h1ρ
      linarith
    exact div_lt_div_of_pos_right (mul_lt_mul_of_pos_right hsq_lt (pow_pos hX_pos 2)) (by linarith)
  have hws_eq_c1ρ : wstar = P.cost qstar / (1 - P.ρ) := by
    dsimp [qstar, wstar]; exact hc1ρ_oo.symm
  have hws_lt_L : wstar < qstar * P.θL := by
    dsimp [qstar, wstar]
    rw [div_mul_eq_mul_div, div_lt_div_iff₀ (by linarith : 0 < 4 * P.k) (by linarith : 0 < 2 * P.k)]
    have := mul_lt_mul_of_pos_left hX_lt (mul_pos (mul_pos h1ρ hX_pos) hk)
    linarith
  have hws_lt_H : wstar < qstar * P.θH :=
    lt_trans hws_lt_L (mul_lt_mul_of_pos_left hθLH hqs_pos)
  have hlow_qs : (qstar * P.θH - wstar) * P.αb < (qstar * P.θL - wstar) * S_Q := by
    dsimp [qstar, wstar]
    rw [oo_margin_id_tb P.ρ P.X P.θH P.k hk.ne', oo_margin_id_tb P.ρ P.X P.θL P.k hk.ne']
    have hfac : 0 < (1 - P.ρ) * P.X / (4 * P.k) := div_pos (mul_pos h1ρ hX_pos) (by linarith)
    have hlt_inner : (2 * P.θH - P.X) * P.αb < (2 * P.θL - P.X) * S_Q := by dsimp [S_Q] at *; linarith
    have := mul_lt_mul_of_pos_left hlt_inner hfac
    linarith
  have hlow_1 : (qstar * P.θH - wstar) * P.αb < qstar * P.θL - wstar := by
    refine lt_of_lt_of_le hlow_qs ?_
    have := mul_le_mul_of_nonneg_left (by dsimp [S_Q]; linarith : S_Q ≤ 1) (sub_pos.mpr hws_lt_L).le
    linarith
  have h1Q_0 : 0 ≤ 1 - Qbar := by linarith
  let σ0 := fullProfile_tb P Qbar qstar wstar (1 - Qbar)
  have hpost0 := isPostSPE_full_tb P hStand Qbar hQ0 qstar wstar (1 - Qbar)
  have hinv0 := isInvSPE_full_tb P hStand Qbar hQ0 qstar wstar (1 - Qbar) h1Q_0
  let σ_base := fullProfile_tb P Qbar 0 0 0
  have hpost_base := isPostSPE_full_tb P hStand Qbar hQ0 0 0 0
  have hresp := (supplier_response_medium P hStand Qbar hQ0 hQ1 σ_base hpost_base
    qstar wstar hqs_pos hc_lt_ws hlow_qs).2.2 hws_eq_c1ρ
  have h1Q_opt : (1 - Qbar) ∈ {I : ℝ | 0 ≤ I ∧ ∀ I' : ℝ, 0 ≤ I' →
      σ_base.supplierValue P qstar wstar I' ≤ σ_base.supplierValue P qstar wstar I} := by
    rw [hresp]
    exact ⟨by linarith, le_refl _⟩
  have hI0_eq : σ0.inv qstar wstar = 1 - Qbar := by
    change argmaxList_tb (fun I => (basePost_tb P Qbar).supplierValue P qstar wstar I)
      ((1 - Qbar) :: candList_tb P Qbar qstar wstar) = 1 - Qbar
    apply argmaxList_tb_head
    intro z hz
    have hz0 : 0 ≤ z := by
      simp only [candList_tb, List.mem_cons, List.not_mem_nil, or_false] at hz
      rcases hz with rfl | rfl | rfl | rfl | rfl | rfl
      · exact hαg0.le
      · exact le_max_left _ _
      · exact le_refl 0
      · exact hαb0.le
      · exact le_trans hαb0.le (le_max_left _ _)
      · exact le_max_left _ _
    exact h1Q_opt.2 z hz0
  have h1Q_sum : (1 - Qbar) + Qbar = 1 := by ring
  have hord_g : (basePost_tb P Qbar).order qstar wstar (1 - Qbar) .good = P.αg := by
    unfold basePost_tb; dsimp only
    rw [if_pos hc_lt_ws.le, Params.alpha, h1Q_sum, min_eq_left hαg1.le, min_self, mul_one]
    have hvH : 0 < (qstar * P.θH - wstar) * P.αg := mul_pos (sub_pos.mpr hws_lt_H) hαg0
    have hvL : qstar * P.θL - wstar < (qstar * P.θH - wstar) * P.αg := by
      have h2 : qstar * P.θL < qstar * (P.αg * P.θH) := mul_lt_mul_of_pos_left hαg_gt hqs_pos
      have h3 : wstar * P.αg ≤ wstar := by
        have := mul_le_mul_of_nonneg_left hαg1.le hws_pos.le; linarith
      linarith
    rw [if_neg (not_le_of_gt (lt_of_lt_of_le hvH (le_max_left _ _))),
      if_neg (not_le_of_gt hvL)]
  have hord_b : (basePost_tb P Qbar).order qstar wstar (1 - Qbar) .bad = 1 := by
    unfold basePost_tb; dsimp only
    rw [if_pos hc_lt_ws.le, Params.alpha, h1Q_sum, min_eq_left hαb1.le, min_self, mul_one]
    have hvL : 0 < qstar * P.θL - wstar := sub_pos.mpr hws_lt_L
    rw [if_neg (not_le_of_gt (lt_of_lt_of_le hvL (le_max_right _ _))),
      if_pos hlow_1.le]
  have hrv0_eq : σ0.retailerValue P qstar wstar = P.V_OO := by
    have hord_g0 : σ0.order qstar wstar (1 - Qbar) .good = P.αg := hord_g
    have hord_b0 : σ0.order qstar wstar (1 - Qbar) .bad = 1 := hord_b
    have hag_le_1Q : P.αg ≤ 1 - Qbar := by linarith
    have hrec_g : σ0.recv qstar wstar (1 - Qbar) .good P.αg = P.αg := by
      unfold Profile.recv received; rw [if_pos hag_le_1Q]
    have hmade_g : σ0.made qstar wstar (1 - Qbar) .good P.αg = 0 := by
      unfold Profile.made inSeason; rw [if_pos hag_le_1Q]
    have hrec_b : σ0.recv qstar wstar (1 - Qbar) .bad 1 = 1 := by
      unfold Profile.recv received
      rcases eq_or_lt_of_le hQ0 with hQ_z | hQ_p
      · rw [if_pos (by linarith)]
      · rw [if_neg (not_le_of_gt (by linarith : 1 - Qbar < 1))]
        change min ((1 - Qbar) + (if P.cost qstar ≤ wstar then min Qbar (max 0 (1 - (1 - Qbar))) else 0)) 1 = 1
        rw [if_pos hc_lt_ws.le, show 1 - (1 - Qbar) = Qbar by ring,
          max_eq_right hQ0, min_self, h1Q_sum, min_self]
    have hrm_b : received (1 - Qbar) 1 (σ0.made qstar wstar (1 - Qbar) .bad 1) = 1 := by
      have h1 := hrec_b
      unfold Profile.recv received at h1
      unfold Profile.made received inSeason
      rcases le_or_gt 1 (1 - Qbar) with h2 | h2
      · rw [if_pos h2]
      · rw [if_neg (not_le_of_gt h2), if_neg (not_le_of_gt h2)]; rw [if_neg (not_le_of_gt h2)] at h1; exact h1
    have hqLH : qstar * P.θL < qstar * P.θH := mul_lt_mul_of_pos_left hθLH hqs_pos
    have hpg : σ0.priceAfter qstar wstar (1 - Qbar) .good P.αg = qstar * P.θH := by
      unfold Profile.priceAfter; rw [hmade_g]
      change (let R := received (1 - Qbar) P.αg 0
        if (qstar * P.θL) * min 1 R ≤ (qstar * P.θH) * min P.αg R then qstar * P.θH else qstar * P.θL) = _
      have hR : received (1 - Qbar) P.αg 0 = P.αg := by unfold received; rw [if_pos hag_le_1Q]
      dsimp only
      rw [hR, min_eq_right hαg1.le, min_self,
        if_pos (mul_le_mul_of_nonneg_right hqLH.le hαg0.le)]
    have hpb : σ0.priceAfter qstar wstar (1 - Qbar) .bad 1 = qstar * P.θL := by
      change (let R := received (1 - Qbar) 1 (σ0.made qstar wstar (1 - Qbar) .bad 1)
        if (qstar * P.θL) * min 1 R ≤ (qstar * P.θH) * min P.αb R then qstar * P.θH else qstar * P.θL) = _
      dsimp only
      rw [hrm_b, min_self, min_eq_left hαb1.le,
        if_neg (not_le_of_gt (by have := mul_lt_mul_of_pos_left hαb_lt hqs_pos; linarith))]
    unfold Profile.retailerValue Params.prob Profile.orderValue Params.retailerState Params.demand
    rw [hI0_eq, hord_g0, hord_b0, hrec_g, hrec_b, hpg, hpb, Params.alpha, Params.alpha,
      if_neg (not_le_of_gt hqLH), if_pos (le_refl _), zero_add, min_self,
      if_pos (le_refl _), if_pos hqLH.le, sub_add_cancel, min_self]
    dsimp [qstar, wstar]
    linarith
  have hSPE0 : IsSPE P Qbar σ0 := by
    refine ⟨hpost0, hinv0, hqs_pos.le, hws_pos.le, fun q w hq hw => ?_⟩
    change σ0.retailerValue P q w ≤ σ0.retailerValue P qstar wstar
    rw [hrv0_eq, ← max_eq_right hV_oo]
    exact (ub_char_med_tb P hDom Qbar hQ0 hQ1 σ0 hpost0 hinv0 q w hq hw).1
  exact ⟨σ0.outcome P, σ0, hSPE0, rfl⟩

private lemma exists_med_tb (P : Params) (hP : P.Dom)
    (Qbar : ℝ) (hQ0 : 0 ≤ Qbar) (hQ1 : Qbar < 1 - P.αg) :
    ∃ e : Outcome, IsEquilibrium P Qbar e := by
  rcases le_or_gt P.V_OO (P.V_OS Qbar) with hV_os | hV_oo
  · exact exists_med_os_tb P hP Qbar hQ0 hQ1 hV_os
  · exact exists_med_oo_tb P hP Qbar hQ0 hQ1 hV_oo.le

theorem solution (P : Params) (hP : P.Dom) (Qbar : ℝ) (h0 : 0 ≤ Qbar) (h1 : Qbar ≤ 1 - P.αg) :
    (∃ e : Outcome, IsEquilibrium P Qbar e) ∧
    ∀ e : Outcome, IsEquilibrium P Qbar e →
      (P.V_OO ≤ P.V_OS Qbar ∧ e.πR = P.V_OS Qbar ∧ e.πS = 0 ∧
        e.q = P.Y (P.αg + Qbar) / (2 * P.k) ∧ e.w = P.Y (P.αg + Qbar) ^ 2 / (4 * P.k) ∧
        e.p .good = P.Y (P.αg + Qbar) * P.θH / (2 * P.k) ∧
        e.p .bad = P.Y (P.αg + Qbar) * P.θL / (2 * P.k) ∧
        e.I = P.αg ∧ e.R .good = P.αg ∧ e.R .bad = P.αg + Qbar) ∨
      (P.V_OS Qbar ≤ P.V_OO ∧ e.πR = P.V_OO ∧
        e.πS = P.ρ * (1 - P.ρ) * (P.αg + (1 - P.ρ) * Qbar) * P.X ^ 2 / (4 * P.k) ∧
        e.q = (1 - P.ρ) * P.X / (2 * P.k) ∧ e.w = (1 - P.ρ) * P.X ^ 2 / (4 * P.k) ∧
        e.p .good = (1 - P.ρ) * P.X * P.θH / (2 * P.k) ∧
        e.p .bad = (1 - P.ρ) * P.X * P.θL / (2 * P.k) ∧
        e.I = 1 - Qbar ∧ e.R .good = P.αg ∧ e.R .bad = 1) := by
  rcases lt_or_eq_of_le h1 with hlt1 | rfl
  · refine ⟨exists_med_tb P hP Qbar h0 hlt1, ?_⟩
    rintro e ⟨σ, hSPE, rfl⟩
    have hDom := hP
    rcases hP with ⟨hStand, hFocus, _hHOD⟩
    have hge_os := lb_os_tb P hStand hFocus Qbar h0 hlt1 σ hSPE
    have hge_oo := lb_oo_tb P hStand hFocus Qbar h0 hlt1 σ hSPE
    have hge_max : max (P.V_OS Qbar) P.V_OO ≤ σ.retailerValue P σ.q σ.w :=
      max_le hge_os hge_oo
    rcases hSPE with ⟨hpost, hinv, hq0, hw0, _hropt⟩
    have hub := ub_char_med_tb P hDom Qbar h0 hlt1 σ hpost hinv σ.q σ.w hq0 hw0
    have hrv_eq : σ.retailerValue P σ.q σ.w = max (P.V_OS Qbar) P.V_OO :=
      le_antisymm hub.1 hge_max
    exact hub.2 hrv_eq
  · have htc := table_C P hP (1 - P.αg) (le_refl _)
    refine ⟨htc.1, fun e he => ?_⟩
    obtain ⟨hπR, hπS, hq_eq, hw_eq, hpg, hpb, hI_lo, hI_hi, hRg, hRb⟩ := htc.2 e he
    rcases hP with ⟨hStand, hFocus, _hHOD⟩
    have hsum1 : P.αg + (1 - P.αg) = 1 := by ring
    obtain ⟨hD1_mul, _hY1_pos, hX_pos, _hX_le, _hY1_le, _hY1_lt, _hX_lt, _hY1_f, _hX_f1⟩ :=
      focus_Y_props_tb P hStand hFocus 1
        (by rcases hStand with ⟨_, _, _, _, _, _, _, _, hαg1⟩; exact hαg1.le) (le_refl 1)
    rcases hStand with ⟨_hθL, _hθLH, hk, hρ0, hρ1, _hαb0, _hαb_lt, _hαg_gt, _hαg1⟩
    have hVOS_1 : P.V_OS (1 - P.αg) = P.X ^ 2 * (P.ρ * P.αg + 1 - P.ρ) / (4 * P.k) := by
      unfold Params.V_OS Params.supplyS Params.X
      rw [hsum1, min_self]
      ring
    have hVOO_le_VOS : P.V_OO ≤ P.V_OS (1 - P.αg) := by
      rw [hVOS_1]
      unfold Params.V_OO
      have hpos : 0 ≤ (P.ρ * P.αg + 1 - P.ρ) * P.X ^ 2 :=
        mul_nonneg (by linarith) (sq_nonneg P.X)
      have hle : (1 - P.ρ) * (P.ρ * P.αg + 1 - P.ρ) * P.X ^ 2 ≤
          P.X ^ 2 * (P.ρ * P.αg + 1 - P.ρ) := by
        have := mul_le_of_le_one_left hpos (by linarith : 1 - P.ρ ≤ 1)
        linarith
      exact div_le_div_of_nonneg_right hle (by linarith)
    left
    have hY_eq : P.Y (P.αg + (1 - P.αg)) = P.X := by rw [hsum1]; rfl
    have hI_eq : e.I = P.αg := by
      have hmax : P.αg ≤ max 0 (1 - (1 - P.αg)) := by
        have := le_max_right 0 (1 - (1 - P.αg)); linarith
      exact le_antisymm hI_hi (le_trans hmax hI_lo)
    refine ⟨hVOO_le_VOS, ?_, hπS, ?_, ?_, ?_, ?_, hI_eq, hRg, ?_⟩
    · rw [hVOS_1]; exact hπR
    · rw [hY_eq]; exact hq_eq
    · rw [hY_eq]; exact hw_eq
    · rw [hY_eq]; exact hpg
    · rw [hY_eq]; exact hpb
    · rw [hsum1]; exact hRb
