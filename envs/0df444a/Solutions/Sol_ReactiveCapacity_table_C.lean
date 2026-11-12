-- Prove2me | solution 1 for ReactiveCapacity.table_C
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-12T03:24:58.678117+00:00
-- url     : https://prove2.me/submissions/5b4f092c-a22a-429e-bdf9-e9bc35dd5c57

import Mathlib
import Definitions.Def_ReactiveCapacity_Model
import Definitions.Def_ReactiveCapacity_Game
import Definitions.Def_ReactiveCapacity_ClosedForms
import Theorems.Thm_ReactiveCapacity_retailer_stage_rule
import Theorems.Thm_ReactiveCapacity_supplier_response_high

open ReactiveCapacity

private noncomputable def argmaxList_tc (f : ℝ → ℝ) : List ℝ → ℝ
  | [] => 0
  | [x] => x
  | x :: y :: xs =>
      let m := argmaxList_tc f (y :: xs)
      if f m ≤ f x then x else m

private lemma argmaxList_tc_mem {f : ℝ → ℝ} :
    ∀ {l : List ℝ}, l ≠ [] → argmaxList_tc f l ∈ l
  | [], h => absurd rfl h
  | [x], _ => by simp [argmaxList_tc]
  | x :: y :: xs, _ => by
      simp only [argmaxList_tc]
      split_ifs
      · simp
      · exact List.mem_cons_of_mem x (argmaxList_tc_mem (List.cons_ne_nil y xs))

private lemma argmaxList_tc_le {f : ℝ → ℝ} :
    ∀ {l : List ℝ} {z : ℝ}, z ∈ l → f z ≤ f (argmaxList_tc f l)
  | [], _, hz => by cases hz
  | [x], z, hz => by
      simp only [List.mem_singleton] at hz
      subst hz
      exact le_refl _
  | x :: y :: xs, z, hz => by
      simp only [argmaxList_tc]
      rcases List.mem_cons.mp hz with rfl | hzy
      · split_ifs with h
        · exact le_refl _
        · exact le_of_lt (lt_of_not_ge h)
      · have ih := argmaxList_tc_le (f := f) hzy
        split_ifs with h
        · exact le_trans ih h
        · exact ih

private lemma argmaxList_tc_head {f : ℝ → ℝ} {x : ℝ} :
    ∀ {xs : List ℝ}, (∀ z ∈ xs, f z ≤ f x) → argmaxList_tc f (x :: xs) = x
  | [], _ => rfl
  | y :: ys, h => by
      simp only [argmaxList_tc]
      have hm := argmaxList_tc_mem (f := f) (List.cons_ne_nil y ys)
      rw [if_pos (h _ hm)]

private lemma affine_le_max_tc {a b x m c fa fb : ℝ} (hab : a ≤ x) (hxb : x ≤ b)
    (ha : m * a + c ≤ fa) (hb : m * b + c ≤ fb) : m * x + c ≤ max fa fb := by
  rcases le_or_gt 0 m with hm | hm
  · exact le_trans (by have := mul_le_mul_of_nonneg_left hxb hm; linarith) (le_max_right fa fb)
  · exact le_trans (by have := mul_le_mul_of_nonpos_left hab hm.le; linarith) (le_max_left fa fb)

private noncomputable def basePost_tc (P : Params) (Qbar : ℝ) : Profile where
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

private noncomputable def candList_tc (P : Params) (Qbar q w : ℝ) : List ℝ :=
  [P.αg, max 0 (1 - Qbar), 0, P.αb, max P.αb (P.αg - Qbar),
    max 0 ((q * P.θH - w) * P.αb / (q * P.θL - w) - Qbar)]

private noncomputable def fullProfile_tc (P : Params) (Qbar q0 w0 I_pref : ℝ) : Profile :=
  { basePost_tc P Qbar with
    q := q0
    w := w0
    inv := fun q w =>
      argmaxList_tc (fun I => (basePost_tc P Qbar).supplierValue P q w I)
        (I_pref :: candList_tc P Qbar q w) }

private lemma isPostSPE_full_tc (P : Params) (hStand : P.Standing) (Qbar : ℝ) (hQ0 : 0 ≤ Qbar)
    (q0 w0 I_pref : ℝ) : IsPostInventorySPE P Qbar (fullProfile_tc P Qbar q0 w0 I_pref) := by
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
      (fullProfile_tc P Qbar q0 w0 I_pref).recv q w I s Q =
        min Q (if P.cost q ≤ w then I + Qbar else I) ∧
      0 ≤ (fullProfile_tc P Qbar q0 w0 I_pref).made q w I s Q ∧
      (fullProfile_tc P Qbar q0 w0 I_pref).made q w I s Q ≤ Qbar := by
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
    have hpr : (fullProfile_tc P Qbar q0 w0 I_pref).price q w I s Q I' =
        if (q * P.θL) * min 1 (received I Q I') ≤ (q * P.θH) * min (P.alpha s) (received I Q I')
        then q * P.θH else q * P.θL := rfl
    unfold Params.retailerState
    rw [hpr, hval0]
    have := hmax p hp
    linarith
  · intro q w I s Q _hq _hw _hI hIQ
    have hre : (fullProfile_tc P Qbar q0 w0 I_pref).react q w I s Q =
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
    have hQo_bds : 0 ≤ (fullProfile_tc P Qbar q0 w0 I_pref).order q w I s ∧
        (fullProfile_tc P Qbar q0 w0 I_pref).order q w I s ≤ S := by
      change 0 ≤ (if max vH vL ≤ 0 then 0 else if vH ≤ vL then min 1 S else min (P.alpha s) S) ∧
        (if max vH vL ≤ 0 then 0 else if vH ≤ vL then min 1 S else min (P.alpha s) S) ≤ S
      split_ifs
      · exact ⟨le_refl 0, hS0⟩
      · exact ⟨le_min zero_le_one hS0, min_le_right 1 S⟩
      · exact ⟨le_min hα0.le hS0, min_le_right (P.alpha s) S⟩
    refine ⟨hQo_bds.1, fun Q hQ => ?_⟩
    have hov_eq : ∀ Q1 : ℝ, 0 ≤ Q1 →
        (fullProfile_tc P Qbar q0 w0 I_pref).orderValue P q w I s Q1 =
          let R := min Q1 S
          max ((q * P.θH) * min (P.alpha s) R) ((q * P.θL) * min 1 R) - w * R := by
      intro Q1 hQ1
      obtain ⟨hrec, _hm0, _hmQ⟩ := hrecv_full q w I s Q1 hI hQ1
      have hrecS : (fullProfile_tc P Qbar q0 w0 I_pref).recv q w I s Q1 = min Q1 S := hrec
      have hR0 : 0 ≤ min Q1 S := le_min hQ1 hS0
      obtain ⟨_, hval0, _⟩ := hrev_price q s (min Q1 S) hq hR0
      dsimp only at hval0 ⊢
      have hrec2 : received I Q1 ((fullProfile_tc P Qbar q0 w0 I_pref).made q w I s Q1) = min Q1 S := by
        have h1 := hrecS
        unfold Profile.recv received at h1
        unfold Profile.made inSeason received
        rcases le_or_gt Q1 I with hQI | hIQ
        · rw [if_pos hQI] at h1 ⊢; exact h1
        · rw [if_neg (not_le_of_gt hIQ), if_neg (not_le_of_gt hIQ)]; rw [if_neg (not_le_of_gt hIQ)] at h1; exact h1
      have hp_eq : (fullProfile_tc P Qbar q0 w0 I_pref).priceAfter q w I s Q1 =
          if (q * P.θL) * min 1 (min Q1 S) ≤ (q * P.θH) * min (P.alpha s) (min Q1 S)
          then q * P.θH else q * P.θL := by
        change (let R := received I Q1 ((fullProfile_tc P Qbar q0 w0 I_pref).made q w I s Q1)
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
        max ((q * P.θH) * min (P.alpha s) ((fullProfile_tc P Qbar q0 w0 I_pref).order q w I s))
          ((q * P.θL) * min 1 ((fullProfile_tc P Qbar q0 w0 I_pref).order q w I s)) -
        w * (fullProfile_tc P Qbar q0 w0 I_pref).order q w I s := by
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

private lemma isInvSPE_full_tc (P : Params) (hStand : P.Standing) (Qbar : ℝ) (hQ0 : 0 ≤ Qbar)
    (q0 w0 I_pref : ℝ) (hIp : 0 ≤ I_pref) :
    ∀ q w : ℝ, 0 ≤ q → 0 ≤ w →
      0 ≤ (fullProfile_tc P Qbar q0 w0 I_pref).inv q w ∧
      ∀ I : ℝ, 0 ≤ I →
        (fullProfile_tc P Qbar q0 w0 I_pref).supplierValue P q w I ≤
          (fullProfile_tc P Qbar q0 w0 I_pref).supplierValue P q w
            ((fullProfile_tc P Qbar q0 w0 I_pref).inv q w) := by
  rcases hStand with ⟨hθL, hθLH, hk, hρ0, hρ1, hαb0, hαb_lt, hαg_gt, hαg1⟩
  have hθH : 0 < P.θH := lt_trans hθL hθLH
  have hαg0 : 0 < P.αg := pos_of_mul_pos_left (lt_trans hθL hαg_gt) hθH.le
  have hαb_αg : P.αb < P.αg := lt_of_mul_lt_mul_right (lt_trans hαb_lt hαg_gt) hθH.le
  have hpost0 := isPostSPE_full_tc P ⟨hθL, hθLH, hk, hρ0, hρ1, hαb0, hαb_lt, hαg_gt, hαg1⟩
    Qbar hQ0 0 0 0
  intro q w hq hw
  let sv := fun I => (basePost_tc P Qbar).supplierValue P q w I
  let l := I_pref :: candList_tc P Qbar q w
  have hl_ne : l ≠ [] := List.cons_ne_nil _ _
  have hl_nonneg : ∀ z ∈ l, 0 ≤ z := by
    intro z hz
    simp only [l, candList_tc, List.mem_cons, List.not_mem_nil, or_false] at hz
    rcases hz with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact hIp
    · exact hαg0.le
    · exact le_max_left _ _
    · exact le_refl 0
    · exact hαb0.le
    · exact le_trans hαb0.le (le_max_left _ _)
    · exact le_max_left _ _
  have hinv_0 : 0 ≤ (fullProfile_tc P Qbar q0 w0 I_pref).inv q w :=
    hl_nonneg _ (argmaxList_tc_mem hl_ne)
  refine ⟨hinv_0, fun I hI => ?_⟩
  suffices hdom : ∃ z ∈ candList_tc P Qbar q w, sv I ≤ sv z by
    rcases hdom with ⟨z, hz, hle⟩
    exact le_trans hle (argmaxList_tc_le (List.mem_cons_of_mem I_pref hz))
  have hQo_0 : ∀ J : ℝ, ∀ s : State, 0 ≤ J → 0 ≤ (basePost_tc P Qbar).order q w J s :=
    fun J s hJ => (hpost0.2.2 q w J s hq hw hJ).1
  have hrm_cw : P.cost q ≤ w → ∀ J : ℝ, ∀ s : State, 0 ≤ J →
      (basePost_tc P Qbar).recv q w J s ((basePost_tc P Qbar).order q w J s) =
        min ((basePost_tc P Qbar).order q w J s) (J + Qbar) ∧
      J + (basePost_tc P Qbar).made q w J s ((basePost_tc P Qbar).order q w J s) =
        max J (min ((basePost_tc P Qbar).order q w J s) (J + Qbar)) := by
    intro hcw J s _hJ
    let Q := (basePost_tc P Qbar).order q w J s
    have hre : (basePost_tc P Qbar).react q w J s Q = min Qbar (max 0 (Q - J)) := by
      change (if P.cost q ≤ w then min Qbar (max 0 (Q - J)) else 0) = _
      rw [if_pos hcw]
    change received J Q ((basePost_tc P Qbar).react q w J s Q) = min Q (J + Qbar) ∧
      J + inSeason J Q ((basePost_tc P Qbar).react q w J s Q) = max J (min Q (J + Qbar))
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
        (basePost_tc P Qbar).recv q w J .good ((basePost_tc P Qbar).order q w J .good) =
          min P.αg (J + Qbar) := by
      intro J hJ
      have hrm := hrm_cw hcw J .good hJ
      rw [hrm.1]
      unfold basePost_tc
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
        (basePost_tc P Qbar).supplierStateValue P q w J .good =
          w * min P.αg (J + Qbar) - P.cost q * max J (min P.αg (J + Qbar)) := by
      intro J hJ
      have hrm := hrm_cw hcw J .good hJ
      have hRg := hgood_R J hJ
      unfold Profile.supplierStateValue Params.supplierState
      rw [hRg, hrm.2, ← hrm.1, hRg]
    have hbad_R : ∀ J : ℝ, 0 ≤ J →
        ((basePost_tc P Qbar).recv q w J .bad ((basePost_tc P Qbar).order q w J .bad) =
          min P.αb (J + Qbar)) ∨
        (0 < J + Qbar ∧
          (q * P.θH - w) * min P.αb (J + Qbar) ≤ (q * P.θL - w) * min 1 (J + Qbar) ∧
          (basePost_tc P Qbar).recv q w J .bad ((basePost_tc P Qbar).order q w J .bad) =
            min 1 (J + Qbar)) := by
      intro J hJ
      have hrm := hrm_cw hcw J .bad hJ
      rw [hrm.1]
      have hord : (basePost_tc P Qbar).order q w J .bad =
          if max ((q * P.θH - w) * min P.αb (J + Qbar)) ((q * P.θL - w) * min 1 (J + Qbar)) ≤ 0 then 0
          else if (q * P.θH - w) * min P.αb (J + Qbar) ≤ (q * P.θL - w) * min 1 (J + Qbar)
          then min 1 (J + Qbar) else min P.αb (J + Qbar) := by
        unfold basePost_tc
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
      · refine ⟨P.αb, by simp [candList_tc], le_trans ?_ (hFH_le_sv P.αb hαb0.le (by linarith))⟩
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
              refine affine_le_max_tc hI_ab.le hI_km ?_ ?_
              · rw [← h_aff P.αb (le_refl _) (le_max_left _ _)]
                exact hFH_le_sv P.αb hαb0.le (by linarith)
              · rw [← h_aff km (le_max_left _ _) (le_refl _)]
                exact hFH_le_sv km hkm0 hkm1
            rcases max_choice (sv P.αb) (sv km) with h1 | h1
            · rw [h1] at hle_max
              exact ⟨P.αb, by simp [candList_tc], hle_max⟩
            · rw [h1] at hle_max
              exact ⟨km, by simp [km, candList_tc], hle_max⟩
          · refine ⟨km, by simp [km, candList_tc], le_trans ?_ (hFH_le_sv km hkm0 hkm1)⟩
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
        · refine ⟨P.αg, by simp [candList_tc], le_trans ?_ (hFH_le_sv P.αg hαg0.le hαg1.le)⟩
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
        have hRb_J : (basePost_tc P Qbar).recv q w J .bad
            ((basePost_tc P Qbar).order q w J .bad) = min 1 (J + Qbar) := by
          have hrm := hrm_cw hcw J .bad hJ0
          rw [hrm.1]
          have hord : (basePost_tc P Qbar).order q w J .bad = min 1 (J + Qbar) := by
            unfold basePost_tc
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
      · refine ⟨P.αg, by simp [candList_tc], ?_⟩
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
        have hM_mem : M ∈ candList_tc P Qbar q w := by
          rcases max_choice P.αg (max 0 (1 - Qbar)) with h1 | h1 <;>
          · dsimp [M]; rw [h1]; simp [candList_tc]
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
            refine affine_le_max_tc hL_le_I hI_le_U ?_ ?_
            · rw [← h_aff L (le_refl _) hL_le_U, hsv_FL L (le_max_right _ _)]
            · rw [← h_aff U hL_le_U (le_refl _),
                hsv_FL U (le_trans hJ0_le_I hI_le_U)]
          rcases max_choice (sv L) (sv U) with h1 | h1
          · rw [h1] at hle_max
            have hL_mem : L ∈ candList_tc P Qbar q w := by
              rcases max_choice P.αg J0 with h2 | h2 <;>
              · dsimp [L, J0, S0] at h2 ⊢; rw [h2]; simp [candList_tc]
            exact ⟨L, hL_mem, hle_max⟩
          · rw [h1] at hle_max
            exact ⟨U, by simp [U, candList_tc], hle_max⟩
  · refine ⟨0, by simp [candList_tc], ?_⟩
    rcases lt_or_ge w (P.cost q) with hw_lt | hcw
    · have hstate_le : ∀ s : State,
          (basePost_tc P Qbar).supplierStateValue P q w I s ≤ 0 ∧
          (basePost_tc P Qbar).supplierStateValue P q w 0 s = 0 := by
        intro s
        have hQoI := hQo_0 I s hI
        have hQo0 := hQo_0 0 s (le_refl 0)
        let QI := (basePost_tc P Qbar).order q w I s
        let Q0 := (basePost_tc P Qbar).order q w 0 s
        have hreJ : ∀ J : ℝ, (basePost_tc P Qbar).react q w J s ((basePost_tc P Qbar).order q w J s) = 0 := by
          intro J
          change (if P.cost q ≤ w then _ else 0) = 0
          rw [if_neg (not_le_of_gt hw_lt)]
        change (w * received I QI ((basePost_tc P Qbar).react q w I s QI) -
            P.cost q * (I + inSeason I QI ((basePost_tc P Qbar).react q w I s QI)) ≤ 0) ∧
          (w * received 0 Q0 ((basePost_tc P Qbar).react q w 0 s Q0) -
            P.cost q * (0 + inSeason 0 Q0 ((basePost_tc P Qbar).react q w 0 s Q0)) = 0)
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
          (basePost_tc P Qbar).supplierStateValue P q w J s = -P.cost q * J := by
        intro J s hJ
        have hS0 : 0 ≤ J + Qbar := add_nonneg hJ hQ0
        obtain ⟨hα0, _⟩ : 0 ≤ P.alpha s ∧ True := by
          cases s <;> exact ⟨by simp [Params.alpha]; linarith, trivial⟩
        have hvH_le : (q * P.θH - w) * min (P.alpha s) (J + Qbar) ≤ 0 :=
          mul_nonpos_of_nonpos_of_nonneg (by linarith) (le_min hα0 hS0)
        have hvL_le : (q * P.θL - w) * min 1 (J + Qbar) ≤ 0 :=
          mul_nonpos_of_nonpos_of_nonneg (by linarith) (le_min zero_le_one hS0)
        have hord0 : (basePost_tc P Qbar).order q w J s = 0 := by
          unfold basePost_tc
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

private lemma ub_char_tc (P : Params) (hStand : P.Standing)
    (hHOD_TC : (P.ρ * P.αg + (1 - P.ρ) * P.αb) * P.θH ^ 2 / (4 * P.k) <
      P.X ^ 2 * (P.ρ * P.αg + 1 - P.ρ) / (4 * P.k))
    (Qbar : ℝ) (hQ_pos : 0 < Qbar)
    (σ : Profile) (hpost : IsPostInventorySPE P Qbar σ)
    (hinv : ∀ q w : ℝ, 0 ≤ q → 0 ≤ w →
      0 ≤ σ.inv q w ∧ ∀ I' : ℝ, 0 ≤ I' → σ.supplierValue P q w I' ≤ σ.supplierValue P q w (σ.inv q w))
    (q w : ℝ) (hq : 0 ≤ q) (hw : 0 ≤ w) :
    let V_TC := P.X ^ 2 * (P.ρ * P.αg + 1 - P.ρ) / (4 * P.k)
    σ.retailerValue P q w ≤ V_TC ∧
    (σ.retailerValue P q w = V_TC →
      σ.supplierValue P q w (σ.inv q w) = 0 ∧
      q = P.X / (2 * P.k) ∧ w = P.X ^ 2 / (4 * P.k) ∧
      σ.priceAfter q w (σ.inv q w) .good (σ.order q w (σ.inv q w) .good) = P.X * P.θH / (2 * P.k) ∧
      σ.priceAfter q w (σ.inv q w) .bad (σ.order q w (σ.inv q w) .bad) = P.X * P.θL / (2 * P.k) ∧
      max 0 (1 - Qbar) ≤ σ.inv q w ∧ σ.inv q w ≤ P.αg ∧
      σ.recv q w (σ.inv q w) .good (σ.order q w (σ.inv q w) .good) = P.αg ∧
      σ.recv q w (σ.inv q w) .bad (σ.order q w (σ.inv q w) .bad) = 1) := by
  rcases hStand with ⟨hθL, hθLH, hk, hρ0, hρ1, hαb0, hαb_lt, hαg_gt, hαg1⟩
  have hStand : P.Standing := ⟨hθL, hθLH, hk, hρ0, hρ1, hαb0, hαb_lt, hαg_gt, hαg1⟩
  have hθH : 0 < P.θH := lt_trans hθL hθLH
  have hαg0 : 0 < P.αg := pos_of_mul_pos_left (lt_trans hθL hαg_gt) hθH.le
  have hαb_αg : P.αb < P.αg := lt_of_mul_lt_mul_right (lt_trans hαb_lt hαg_gt) hθH.le
  have hαb1 : P.αb < 1 := lt_trans hαb_αg hαg1
  have h1ρ : 0 < 1 - P.ρ := sub_pos.mpr hρ1
  have hD1_pos : 0 < P.ρ * P.αg + 1 - P.ρ := by
    have : 0 < P.ρ * P.αg := mul_pos hρ0 hαg0
    linarith
  have hX_pos : 0 < P.X := by
    unfold Params.X Params.Y
    refine div_pos ?_ (by linarith)
    have h1 : 0 < P.ρ * P.αg * P.θH := mul_pos (mul_pos hρ0 hαg0) hθH
    have h2 : 0 < (1 - P.ρ) * 1 * P.θL := mul_pos (mul_pos h1ρ zero_lt_one) hθL
    linarith
  let V_TC := P.X ^ 2 * (P.ρ * P.αg + 1 - P.ρ) / (4 * P.k)
  have hV_TC_pos : 0 < V_TC := div_pos (mul_pos (pow_pos hX_pos 2) hD1_pos) (by linarith)
  dsimp only
  change σ.retailerValue P q w ≤ V_TC ∧ (σ.retailerValue P q w = V_TC → _)
  let I := σ.inv q w
  obtain ⟨hI0, hI_opt⟩ := hinv q w hq hw
  have hsv0_nonneg : 0 ≤ σ.supplierValue P q w 0 := by
    have hst : ∀ s : State, 0 ≤ σ.supplierStateValue P q w 0 s := by
      intro s
      obtain ⟨hQ0, _⟩ := hpost.2.2 q w 0 s hq hw (le_refl 0)
      unfold Profile.supplierStateValue Params.supplierState Profile.recv Profile.made
        received inSeason
      rcases le_or_gt (σ.order q w 0 s) 0 with hle | hgt
      · have heq : σ.order q w 0 s = 0 := le_antisymm hle hQ0
        simp [heq]
      · have hropt := (hpost.2.1 q w 0 s (σ.order q w 0 s) hq hw (le_refl 0) hgt).2.2
          0 (le_refl 0) hQ_pos.le
        unfold Params.supplierState received at hropt
        simp only [if_neg (not_le_of_gt hgt), zero_add, min_eq_left hQ0, mul_zero, sub_zero] at hropt
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
      exact ⟨le_refl 0, hQ_pos.le, hQ, by linarith⟩
    · rw [if_neg (not_le_of_gt hJQ), if_neg (not_le_of_gt hJQ)]
      obtain ⟨hr0, hrQ, _⟩ := hpost.2.1 q w J s Q hq hw hJ hJQ
      exact ⟨hr0, hrQ, le_min (add_nonneg hJ hr0) hQ,
        le_trans (min_le_left _ _) (by linarith)⟩
  by_cases hact : P.cost q ≤ w ∧ 0 < q ∧ w < q * P.θH
  · rcases hact with ⟨hcw, hq_pos, hwH⟩
    have hc_pos : 0 < P.cost q := mul_pos hk (pow_pos hq_pos 2)
    have hwH0 : 0 < q * P.θH - w := sub_pos.mpr hwH
    let S := I + Qbar
    have hS_pos : 0 < S := by dsimp [S]; linarith
    have hrule := retailer_stage_rule P hStand q w S hq_pos hw hwH hS_pos.le
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
    have hov_step : ∀ s : State,
        σ.orderValue P q w I s (σ.order q w I s) =
          P.stepOnePayoff q w (P.alpha s) S (σ.recv q w I s (σ.order q w I s))
            (σ.priceAfter q w I s (σ.order q w I s)) := by
      rintro (_ | _)
      · unfold Profile.orderValue Params.retailerState Params.stepOnePayoff
        rw [min_eq_left hRgS]
      · unfold Profile.orderValue Params.retailerState Params.stepOnePayoff
        rw [min_eq_left hRbS]
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
    · -- Branch H: strictly dominated by V_TC via HighOnlyDominated
      have hg_le : σ.orderValue P q w I .good Qg ≤ (q * P.θH - P.cost q) * P.αg := by
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
      have hrv_lt : σ.retailerValue P q w < V_TC := by
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
        exact lt_of_le_of_lt (le_trans h1 h2) hHOD_TC
      exact ⟨hrv_lt.le, fun heq => absurd heq hrv_lt.ne⟩
    · -- Branch L: (q * θH - w) * min αb S < (q * θL - w) * min S 1
      have hwL : w < q * P.θL := by
        have hvH_pos : 0 < (q * P.θH - w) * min P.αb S :=
          mul_pos hwH0 (lt_min hαb0 hS_pos)
        have hvL_pos : 0 < (q * P.θL - w) * min S 1 := lt_trans hvH_pos hBrL
        by_contra hc
        have := mul_nonpos_of_nonpos_of_nonneg (by linarith : q * P.θL - w ≤ 0)
          (le_min hS_pos.le zero_le_one)
        linarith
      have hwL0 : 0 < q * P.θL - w := sub_pos.mpr hwL
      have hcL0 : 0 < q * P.θL - P.cost q := by linarith
      have hcH0 : 0 < q * P.θH - P.cost q := by linarith
      have hg_step1 : (q * P.θH - w) * min P.αg S ≤ (q * P.θH - w) * P.αg :=
        mul_le_mul_of_nonneg_left (min_le_left _ _) hwH0.le
      have hg_step2 : (q * P.θH - w) * P.αg ≤ (q * P.θH - P.cost q) * P.αg :=
        mul_le_mul_of_nonneg_right (by linarith) hαg0.le
      have hb_max : σ.orderValue P q w I .bad Qb ≤ (q * P.θL - w) * min S 1 := by
        rwa [max_eq_right hBrL.le] at hov_bad_ub
      have hb_step1 : (q * P.θL - w) * min S 1 ≤ q * P.θL - w := by
        have := mul_le_mul_of_nonneg_left (min_le_right S 1) hwL0.le; linarith
      have hb_step2 : q * P.θL - w ≤ q * P.θL - P.cost q := by linarith
      have hlin_id : P.ρ * ((q * P.θH - P.cost q) * P.αg) +
          (1 - P.ρ) * (q * P.θL - P.cost q) =
          V_TC - (P.ρ * P.αg + 1 - P.ρ) * P.k * (q - P.X / (2 * P.k)) ^ 2 := by
        dsimp [V_TC]
        unfold Params.X Params.Y Params.cost
        have hd : P.ρ * P.αg + (1 - P.ρ) * 1 = P.ρ * P.αg + 1 - P.ρ := by ring
        rw [hd]
        field_simp [hD1_pos.ne', hk.ne']
        ring
      have hsq_nonneg : 0 ≤ (P.ρ * P.αg + 1 - P.ρ) * P.k * (q - P.X / (2 * P.k)) ^ 2 :=
        mul_nonneg (mul_nonneg hD1_pos.le hk.le) (sq_nonneg _)
      have hrv_ub_sum : σ.retailerValue P q w ≤
          P.ρ * ((q * P.θH - P.cost q) * P.αg) + (1 - P.ρ) * (q * P.θL - P.cost q) := by
        unfold Profile.retailerValue Params.prob
        change P.ρ * σ.orderValue P q w I .good Qg +
          (1 - P.ρ) * σ.orderValue P q w I .bad Qb ≤ _
        have := mul_le_mul_of_nonneg_left
          (le_trans hov_good_ub (le_trans hg_step1 hg_step2)) hρ0.le
        have := mul_le_mul_of_nonneg_left
          (le_trans hb_max (le_trans hb_step1 hb_step2)) h1ρ.le
        linarith
      refine ⟨by linarith, fun hrv_eq => ?_⟩
      -- All inequalities in the chain are tight!
      have hsq_zero : (P.ρ * P.αg + 1 - P.ρ) * P.k * (q - P.X / (2 * P.k)) ^ 2 = 0 := by
        linarith
      have hq_eq : q = P.X / (2 * P.k) := by
        have h1 : (q - P.X / (2 * P.k)) ^ 2 = 0 := by
          rcases mul_eq_zero.mp hsq_zero with h0 | h0
          · exfalso; have := mul_pos hD1_pos hk; linarith
          · exact h0
        linarith [sq_eq_zero_iff.mp h1]
      have hov_g_eq : σ.orderValue P q w I .good Qg = (q * P.θH - P.cost q) * P.αg := by
        unfold Profile.retailerValue Params.prob at hrv_eq
        change P.ρ * σ.orderValue P q w I .good Qg +
          (1 - P.ρ) * σ.orderValue P q w I .bad Qb = V_TC at hrv_eq
        by_contra hne
        have hlt : σ.orderValue P q w I .good Qg < (q * P.θH - P.cost q) * P.αg :=
          lt_of_le_of_ne (le_trans hov_good_ub (le_trans hg_step1 hg_step2)) hne
        have := mul_lt_mul_of_pos_left hlt hρ0
        have := mul_le_mul_of_nonneg_left
          (le_trans hb_max (le_trans hb_step1 hb_step2)) h1ρ.le
        linarith
      have hov_b_eq : σ.orderValue P q w I .bad Qb = q * P.θL - P.cost q := by
        unfold Profile.retailerValue Params.prob at hrv_eq
        change P.ρ * σ.orderValue P q w I .good Qg +
          (1 - P.ρ) * σ.orderValue P q w I .bad Qb = V_TC at hrv_eq
        by_contra hne
        have hlt : σ.orderValue P q w I .bad Qb < q * P.θL - P.cost q :=
          lt_of_le_of_ne (le_trans hb_max (le_trans hb_step1 hb_step2)) hne
        have := mul_le_mul_of_nonneg_left
          (le_trans hov_good_ub (le_trans hg_step1 hg_step2)) hρ0.le
        have := mul_lt_mul_of_pos_left hlt h1ρ
        linarith
      have hw_eq_c : w = P.cost q := by
        linarith
      have hcost_val : P.cost q = P.X ^ 2 / (4 * P.k) := by
        rw [hq_eq]
        unfold Params.cost
        field_simp [hk.ne']
        ring
      have hw_eq : w = P.X ^ 2 / (4 * P.k) := hw_eq_c.trans hcost_val
      have hminS1 : min S 1 = 1 := by
        have : (q * P.θL - w) * min S 1 = q * P.θL - w := by linarith
        have h1 : (q * P.θL - w) * (1 - min S 1) = 0 := by linarith
        rcases mul_eq_zero.mp h1 with h0 | h0
        · linarith
        · linarith
      have hS_ge1 : 1 ≤ S := by
        by_contra hc
        have hlt : S < 1 := lt_of_not_ge hc
        rw [min_eq_left hlt.le] at hminS1
        linarith
      have hI_lo : max 0 (1 - Qbar) ≤ I := max_le hI0 (by dsimp [S] at hS_ge1; linarith)
      -- At w = P.cost q, supplierStateValue ≤ 0 in both states, and I ≤ Rg
      have hsv_state_c : ∀ s : State,
          σ.supplierStateValue P q w I s ≤ 0 ∧
          (σ.recv q w I s (σ.order q w I s) < I → σ.supplierStateValue P q w I s < 0) := by
        intro s
        obtain ⟨hQs0, _⟩ := hpost.2.2 q w I s hq hw hI0
        unfold Profile.supplierStateValue Params.supplierState Profile.recv Profile.made
          received inSeason
        have hw_mul : ∀ x : ℝ, w * x = P.cost q * x := fun x => by rw [hw_eq_c]
        rcases le_or_gt (σ.order q w I s) I with hQI | hIQ
        · rw [if_pos hQI, if_pos hQI, add_zero, hw_mul]
          refine ⟨?_, fun hlt => ?_⟩
          · have := mul_le_mul_of_nonneg_left hQI hc_pos.le; linarith
          · have := mul_lt_mul_of_pos_left hlt hc_pos; linarith
        · have hropt := (hpost.2.1 q w I s (σ.order q w I s) hq hw hI0 hIQ).2.2
            0 (le_refl 0) hQ_pos.le
          obtain ⟨hr0, _, _⟩ := hpost.2.1 q w I s (σ.order q w I s) hq hw hI0 hIQ
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
      have hsv_eq0 : σ.supplierValue P q w I = 0 := by
        unfold Profile.supplierValue Params.prob at hsv_I_nonneg ⊢
        have hg0 := (hsv_state_c .good).1
        have hb0 := (hsv_state_c .bad).1
        have := mul_nonpos_of_nonneg_of_nonpos hρ0.le hg0
        have := mul_nonpos_of_nonneg_of_nonpos h1ρ.le hb0
        linarith
      have hI_le_Rg : I ≤ Rg := by
        by_contra hc
        have hlt := (hsv_state_c .good).2 (lt_of_not_ge hc)
        have hb0 := (hsv_state_c .bad).1
        unfold Profile.supplierValue Params.prob at hsv_I_nonneg
        have := mul_lt_mul_of_pos_left hlt hρ0
        have := mul_nonpos_of_nonneg_of_nonpos h1ρ.le hb0
        linarith
      have hmin_agS : min P.αg S = P.αg := min_eq_left (le_trans hαg1.le hS_ge1)
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
          have h2 : q * P.θL < q * (P.αg * P.θH) := mul_lt_mul_of_pos_left hαg_gt hq_pos
          have h3 : w * P.αg ≤ w := by
            have := mul_le_mul_of_nonneg_left hαg1.le hw; linarith
          linarith
        have hvH0 : 0 ≤ (q * P.θH - w) * min P.αg S :=
          mul_nonneg hwH0.le (le_min hαg0.le hS_pos.le)
        rw [max_eq_left hvL_le, max_eq_left hvH0, hmin_agS, ← hpay_g] at h1
        exact h1
      have hpg_eq : pg = P.X * P.θH / (2 * P.k) := by
        have := hrule.2.1 hS_pos Rg pg hRg0 hpg0 hopt_g
        rw [this, hq_eq, div_mul_eq_mul_div]
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
          have := mul_lt_mul_of_pos_left hlt hwH0
          linarith
        · exact heq
        · exfalso
          rw [min_eq_left hgt.le] at hpay
          have hw_pos : 0 < w := by rw [hw_eq_c]; exact hc_pos
          have := mul_lt_mul_of_pos_left hgt hw_pos
          linarith
      have hI_hi : I ≤ P.αg := hRg_eq ▸ hI_le_Rg
      have hpay_b : P.stepOnePayoff q w P.αb S Rb pb = q * P.θL - w := by
        have hstep := hov_step .bad
        rw [Params.alpha] at hstep
        change P.stepOnePayoff q w P.αb S Rb pb = q * P.θL - w
        rw [← hstep, hov_b_eq, hw_eq_c]
      have hopt_b : ∀ Q' p' : ℝ, 0 ≤ Q' → 0 ≤ p' →
          P.stepOnePayoff q w P.αb S Q' p' ≤ P.stepOnePayoff q w P.αb S Rb pb := by
        intro Q' p' hQ' hp'
        have h1 := (hrule.1 P.αb hαb0.le hαb1.le).2 ⟨Q', p', hQ', hp', rfl⟩
        have hvL0 : 0 ≤ (q * P.θL - w) * min S 1 :=
          mul_nonneg hwL0.le (le_min hS_pos.le zero_le_one)
        rw [max_eq_right hBrL.le, max_eq_left hvL0, hminS1, mul_one, ← hpay_b] at h1
        exact h1
      have hpb_eq : pb = P.X * P.θL / (2 * P.k) := by
        have := hrule.2.2.1 hBrL Rb pb hRb0 hpb0 hopt_b
        rw [this, hq_eq, div_mul_eq_mul_div]
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
          have := mul_lt_mul_of_pos_left hlt hwL0
          linarith
        · exact heq
        · exfalso
          rw [min_eq_left hgt.le] at hpay
          have hw_pos : 0 < w := by rw [hw_eq_c]; exact hc_pos
          have := mul_lt_mul_of_pos_left hgt hw_pos
          linarith
      exact ⟨hsv_eq0, hq_eq, hw_eq, hpg_eq, hpb_eq, hI_lo, hI_hi, hRg_eq, hRb_eq⟩
  · -- Inactive contract: retailerValue ≤ 0 < V_TC
    have hrv_nonpos : σ.retailerValue P q w ≤ 0 := by
      rcases lt_or_ge w (P.cost q) with hw_lt | hcw
      · -- w < cost q forces react = 0, I = 0, recv = 0, retailerValue = 0
        have hreact0 : ∀ J : ℝ, ∀ s : State, ∀ Q : ℝ, 0 ≤ J → J < Q →
            σ.react q w J s Q = 0 := by
          intro J s Q hJ hJQ
          obtain ⟨hr0, hrQ, hropt⟩ := hpost.2.1 q w J s Q hq hw hJ hJQ
          have h0 := hropt 0 (le_refl 0) hQ_pos.le
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
            · rw [if_pos hle]
              linarith
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
        rw [hov0 .good, hov0 .bad]
        linarith
      · have hw_ge_H : q * P.θH ≤ w := by
          rcases eq_or_lt_of_le hq with rfl | hq_pos
          · simp [hw]
          · by_contra hc
            exact hact ⟨hcw, hq_pos, lt_of_not_ge hc⟩
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
    have hrv_lt : σ.retailerValue P q w < V_TC := lt_of_le_of_lt hrv_nonpos hV_TC_pos
    exact ⟨hrv_lt.le, fun heq => absurd heq hrv_lt.ne⟩

private lemma val_qstar_tc (P : Params) (hk : 0 < P.k) (hD1 : 0 < P.ρ * P.αg + 1 - P.ρ) :
    P.ρ * ((P.X / (2 * P.k) * P.θH - P.X ^ 2 / (4 * P.k)) * P.αg) +
      (1 - P.ρ) * (P.X / (2 * P.k) * P.θL - P.X ^ 2 / (4 * P.k)) =
      P.X ^ 2 * (P.ρ * P.αg + 1 - P.ρ) / (4 * P.k) := by
  unfold Params.X Params.Y
  have hd : P.ρ * P.αg + (1 - P.ρ) * 1 = P.ρ * P.αg + 1 - P.ρ := by ring
  rw [hd]
  field_simp [hD1.ne', hk.ne']
  ring

private lemma exists_tc (P : Params) (hStand : P.Standing)
    (hX_pos : 0 < P.X) (hX_lt_2θL : P.X < 2 * P.θL)
    (hX_focus : P.X * (1 - P.αb) < 2 * (P.θL - P.θH * P.αb))
    (hHOD_TC : (P.ρ * P.αg + (1 - P.ρ) * P.αb) * P.θH ^ 2 / (4 * P.k) <
      P.X ^ 2 * (P.ρ * P.αg + 1 - P.ρ) / (4 * P.k))
    (Qbar : ℝ) (h : 1 - P.αg ≤ Qbar) :
    ∃ e : Outcome, IsEquilibrium P Qbar e := by
  rcases hStand with ⟨hθL, hθLH, hk, hρ0, hρ1, hαb0, hαb_lt, hαg_gt, hαg1⟩
  have hStand : P.Standing := ⟨hθL, hθLH, hk, hρ0, hρ1, hαb0, hαb_lt, hαg_gt, hαg1⟩
  have hθH : 0 < P.θH := lt_trans hθL hθLH
  have hαg0 : 0 < P.αg := pos_of_mul_pos_left (lt_trans hθL hαg_gt) hθH.le
  have hαb_αg : P.αb < P.αg := lt_of_mul_lt_mul_right (lt_trans hαb_lt hαg_gt) hθH.le
  have hαb1 : P.αb < 1 := lt_trans hαb_αg hαg1
  have h1ρ : 0 < 1 - P.ρ := sub_pos.mpr hρ1
  have hQ_pos : 0 < Qbar := by linarith
  have hD1_pos : 0 < P.ρ * P.αg + 1 - P.ρ := by
    have : 0 < P.ρ * P.αg := mul_pos hρ0 hαg0
    linarith
  let qstar := P.X / (2 * P.k)
  let wstar := P.X ^ 2 / (4 * P.k)
  have hqs_pos : 0 < qstar := div_pos hX_pos (by linarith)
  have hws_pos : 0 < wstar := div_pos (pow_pos hX_pos 2) (by linarith)
  have hc_qs : P.cost qstar = wstar := by
    dsimp [qstar, wstar]
    unfold Params.cost
    field_simp [hk.ne']
    ring
  have hws_lt_L : wstar < qstar * P.θL := by
    dsimp [qstar, wstar]
    rw [div_mul_eq_mul_div, div_lt_div_iff₀ (by linarith : 0 < 4 * P.k) (by linarith : 0 < 2 * P.k)]
    have := mul_lt_mul_of_pos_left hX_lt_2θL (mul_pos hX_pos hk)
    linarith
  have hws_lt_H : wstar < qstar * P.θH :=
    lt_trans hws_lt_L (mul_lt_mul_of_pos_left hθLH hqs_pos)
  have hlow_qs : (qstar * P.θH - wstar) * P.αb < qstar * P.θL - wstar := by
    dsimp [qstar, wstar]
    have hid1 : P.X / (2 * P.k) * P.θH - P.X ^ 2 / (4 * P.k) =
        P.X / (4 * P.k) * (2 * P.θH - P.X) := by field_simp [hk.ne']; ring
    have hid2 : P.X / (2 * P.k) * P.θL - P.X ^ 2 / (4 * P.k) =
        P.X / (4 * P.k) * (2 * P.θL - P.X) := by field_simp [hk.ne']; ring
    rw [hid1, hid2]
    have hfac : 0 < P.X / (4 * P.k) := div_pos hX_pos (by linarith)
    have : (2 * P.θH - P.X) * P.αb < 2 * P.θL - P.X := by linarith
    nlinarith
  let σ0 := fullProfile_tc P Qbar qstar wstar P.αg
  have hpost0 := isPostSPE_full_tc P hStand Qbar hQ_pos.le qstar wstar P.αg
  have hinv0 := isInvSPE_full_tc P hStand Qbar hQ_pos.le qstar wstar P.αg hαg0.le
  have h1le : 1 ≤ P.αg + Qbar := by linarith
  have hord_g : (basePost_tc P Qbar).order qstar wstar P.αg .good = P.αg := by
    unfold basePost_tc; dsimp only
    rw [if_pos hc_qs.le, Params.alpha, min_eq_left (by linarith : P.αg ≤ P.αg + Qbar),
      min_eq_left h1le, mul_one]
    have hvH : 0 < (qstar * P.θH - wstar) * P.αg := mul_pos (sub_pos.mpr hws_lt_H) hαg0
    have hvL : qstar * P.θL - wstar < (qstar * P.θH - wstar) * P.αg := by
      have h2 : qstar * P.θL < qstar * (P.αg * P.θH) := mul_lt_mul_of_pos_left hαg_gt hqs_pos
      have h3 : wstar * P.αg ≤ wstar := by
        have := mul_le_mul_of_nonneg_left hαg1.le hws_pos.le; linarith
      linarith
    rw [if_neg (not_le_of_gt (lt_of_lt_of_le hvH (le_max_left _ _))),
      if_neg (not_le_of_gt hvL)]
  have hord_b : (basePost_tc P Qbar).order qstar wstar P.αg .bad = 1 := by
    unfold basePost_tc; dsimp only
    rw [if_pos hc_qs.le, Params.alpha, min_eq_left (by linarith : P.αb ≤ P.αg + Qbar),
      min_eq_left h1le, mul_one]
    have hvL : 0 < qstar * P.θL - wstar := sub_pos.mpr hws_lt_L
    rw [if_neg (not_le_of_gt (lt_of_lt_of_le hvL (le_max_right _ _))),
      if_pos hlow_qs.le]
  have hI0_eq : σ0.inv qstar wstar = P.αg := by
    dsimp [σ0, fullProfile_tc]
    apply argmaxList_tc_head
    intro z _hz
    have hc_mul : ∀ x : ℝ, P.cost qstar * x = wstar * x := fun x => by rw [hc_qs]
    have hz_le : (basePost_tc P Qbar).supplierValue P qstar wstar z ≤ 0 := by
      have hst : ∀ s : State, (basePost_tc P Qbar).supplierStateValue P qstar wstar z s ≤ 0 := by
        intro s
        let Qz := (basePost_tc P Qbar).order qstar wstar z s
        have hre : (basePost_tc P Qbar).react qstar wstar z s Qz = min Qbar (max 0 (Qz - z)) := by
          change (if P.cost qstar ≤ wstar then min Qbar (max 0 (Qz - z)) else 0) = _
          rw [if_pos hc_qs.le]
        change wstar * received z Qz ((basePost_tc P Qbar).react qstar wstar z s Qz) -
          P.cost qstar * (z + inSeason z Qz ((basePost_tc P Qbar).react qstar wstar z s Qz)) ≤ 0
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
    have hag_eq0 : (basePost_tc P Qbar).supplierValue P qstar wstar P.αg = 0 := by
      have hre_b : (basePost_tc P Qbar).react qstar wstar P.αg .bad 1 = 1 - P.αg := by
        change (if P.cost qstar ≤ wstar then min Qbar (max 0 (1 - P.αg)) else 0) = 1 - P.αg
        rw [if_pos hc_qs.le, max_eq_right (by linarith), min_eq_right h]
      unfold Profile.supplierValue Params.prob Profile.supplierStateValue Params.supplierState
        Profile.recv Profile.made received inSeason
      rw [hord_g, hord_b]
      simp only [if_pos (le_refl P.αg), if_neg (not_le_of_gt hαg1), add_zero, hc_mul, hre_b]
      rw [show P.αg + (1 - P.αg) = 1 by ring, min_self]
      ring
    linarith
  have hrv0_eq : σ0.retailerValue P qstar wstar =
      P.X ^ 2 * (P.ρ * P.αg + 1 - P.ρ) / (4 * P.k) := by
    have hord_g0 : σ0.order qstar wstar P.αg .good = P.αg := hord_g
    have hord_b0 : σ0.order qstar wstar P.αg .bad = 1 := hord_b
    have hrec_g : σ0.recv qstar wstar P.αg .good P.αg = P.αg := by
      unfold Profile.recv received; rw [if_pos (le_refl _)]
    have hmade_g : σ0.made qstar wstar P.αg .good P.αg = 0 := by
      unfold Profile.made inSeason; rw [if_pos (le_refl _)]
    have hmade_b : σ0.made qstar wstar P.αg .bad 1 = 1 - P.αg := by
      unfold Profile.made inSeason
      rw [if_neg (not_le_of_gt hαg1)]
      change (if P.cost qstar ≤ wstar then min Qbar (max 0 (1 - P.αg)) else 0) = 1 - P.αg
      rw [if_pos hc_qs.le, max_eq_right (by linarith), min_eq_right h]
    have hrec_b : σ0.recv qstar wstar P.αg .bad 1 = 1 := by
      unfold Profile.recv received
      rw [if_neg (not_le_of_gt hαg1)]
      change min (P.αg + (if P.cost qstar ≤ wstar then min Qbar (max 0 (1 - P.αg)) else 0)) 1 = 1
      rw [if_pos hc_qs.le, max_eq_right (by linarith), min_eq_right h,
        show P.αg + (1 - P.αg) = 1 by ring, min_self]
    have hqLH : qstar * P.θL < qstar * P.θH := mul_lt_mul_of_pos_left hθLH hqs_pos
    have hpg : σ0.priceAfter qstar wstar P.αg .good P.αg = qstar * P.θH := by
      unfold Profile.priceAfter
      rw [hmade_g]
      change (let R := received P.αg P.αg 0
        if (qstar * P.θL) * min 1 R ≤ (qstar * P.θH) * min P.αg R then qstar * P.θH else qstar * P.θL) = _
      have hR : received P.αg P.αg 0 = P.αg := by unfold received; rw [if_pos (le_refl _)]
      dsimp only
      rw [hR, min_eq_right hαg1.le, min_self,
        if_pos (mul_le_mul_of_nonneg_right hqLH.le hαg0.le)]
    have hpb : σ0.priceAfter qstar wstar P.αg .bad 1 = qstar * P.θL := by
      unfold Profile.priceAfter
      rw [hmade_b]
      change (let R := received P.αg 1 (1 - P.αg)
        if (qstar * P.θL) * min 1 R ≤ (qstar * P.θH) * min P.αb R then qstar * P.θH else qstar * P.θL) = _
      have hR : received P.αg 1 (1 - P.αg) = 1 := by
        unfold received; rw [if_neg (not_le_of_gt hαg1), show P.αg + (1 - P.αg) = 1 by ring, min_self]
      dsimp only
      rw [hR, min_self, min_eq_left hαb1.le,
        if_neg (not_le_of_gt (by have := mul_lt_mul_of_pos_left hαb_lt hqs_pos; linarith))]
    unfold Profile.retailerValue Params.prob Profile.orderValue Params.retailerState Params.demand
    rw [hI0_eq, hord_g0, hord_b0, hrec_g, hrec_b, hpg, hpb, Params.alpha, Params.alpha,
      if_neg (not_le_of_gt hqLH), if_pos (le_refl _), zero_add, min_self,
      if_pos (le_refl _), if_pos hqLH.le, sub_add_cancel, min_self]
    have hval := val_qstar_tc P hk hD1_pos
    dsimp [qstar, wstar]
    linarith
  have hSPE0 : IsSPE P Qbar σ0 := by
    refine ⟨hpost0, hinv0, hqs_pos.le, hws_pos.le, fun q w hq hw => ?_⟩
    change σ0.retailerValue P q w ≤ σ0.retailerValue P qstar wstar
    rw [hrv0_eq]
    exact (ub_char_tc P hStand hHOD_TC Qbar hQ_pos σ0 hpost0 hinv0 q w hq hw).1
  exact ⟨σ0.outcome P, σ0, hSPE0, rfl⟩

private lemma lb_tc (P : Params) (hStand : P.Standing)
    (hX_pos : 0 < P.X) (hX_lt_2θL : P.X < 2 * P.θL)
    (hX_focus : P.X * (1 - P.αb) < 2 * (P.θL - P.θH * P.αb))
    (Qbar : ℝ) (h : 1 - P.αg ≤ Qbar)
    (σ : Profile) (hSPE : IsSPE P Qbar σ) :
    P.X ^ 2 * (P.ρ * P.αg + 1 - P.ρ) / (4 * P.k) ≤ σ.retailerValue P σ.q σ.w := by
  rcases hSPE with ⟨hpost, hinv, _hq0, _hw0, hropt⟩
  rcases hStand with ⟨hθL, hθLH, hk, hρ0, hρ1, hαb0, hαb_lt, hαg_gt, hαg1⟩
  have hStand : P.Standing := ⟨hθL, hθLH, hk, hρ0, hρ1, hαb0, hαb_lt, hαg_gt, hαg1⟩
  have hθH : 0 < P.θH := lt_trans hθL hθLH
  have hαg0 : 0 < P.αg := pos_of_mul_pos_left (lt_trans hθL hαg_gt) hθH.le
  have hαb_αg : P.αb < P.αg := lt_of_mul_lt_mul_right (lt_trans hαb_lt hαg_gt) hθH.le
  have hαb1 : P.αb < 1 := lt_trans hαb_αg hαg1
  have h1ρ : 0 < 1 - P.ρ := sub_pos.mpr hρ1
  have hQ_pos : 0 < Qbar := by linarith
  have hD1_pos : 0 < P.ρ * P.αg + 1 - P.ρ := by
    have : 0 < P.ρ * P.αg := mul_pos hρ0 hαg0
    linarith
  let V_TC := P.X ^ 2 * (P.ρ * P.αg + 1 - P.ρ) / (4 * P.k)
  let qstar := P.X / (2 * P.k)
  let wstar := P.X ^ 2 / (4 * P.k)
  have hqs_pos : 0 < qstar := div_pos hX_pos (by linarith)
  have hws_pos : 0 < wstar := div_pos (pow_pos hX_pos 2) (by linarith)
  have hc_qs : P.cost qstar = wstar := by
    dsimp [qstar, wstar]
    unfold Params.cost
    field_simp [hk.ne']
    ring
  have hws_lt_L : wstar < qstar * P.θL := by
    dsimp [qstar, wstar]
    rw [div_mul_eq_mul_div, div_lt_div_iff₀ (by linarith : 0 < 4 * P.k) (by linarith : 0 < 2 * P.k)]
    have := mul_lt_mul_of_pos_left hX_lt_2θL (mul_pos hX_pos hk)
    linarith
  have hlow_qs : (qstar * P.θH - wstar) * P.αb < qstar * P.θL - wstar := by
    dsimp [qstar, wstar]
    have hid1 : P.X / (2 * P.k) * P.θH - P.X ^ 2 / (4 * P.k) =
        P.X / (4 * P.k) * (2 * P.θH - P.X) := by field_simp [hk.ne']; ring
    have hid2 : P.X / (2 * P.k) * P.θL - P.X ^ 2 / (4 * P.k) =
        P.X / (4 * P.k) * (2 * P.θL - P.X) := by field_simp [hk.ne']; ring
    rw [hid1, hid2]
    have hfac : 0 < P.X / (4 * P.k) := div_pos hX_pos (by linarith)
    have : (2 * P.θH - P.X) * P.αb < 2 * P.θL - P.X := by linarith
    nlinarith
  change V_TC ≤ σ.retailerValue P σ.q σ.w
  by_contra hlt_c
  have hgap : 0 < V_TC - σ.retailerValue P σ.q σ.w := sub_pos.mpr (lt_of_not_ge hlt_c)
  let δ1 := (qstar * P.θL - wstar) - (qstar * P.θH - wstar) * P.αb
  have hδ1_pos : 0 < δ1 := sub_pos.mpr hlow_qs
  let δ2 := qstar * P.θL - wstar
  have hδ2_pos : 0 < δ2 := sub_pos.mpr hws_lt_L
  let δ3 := (V_TC - σ.retailerValue P σ.q σ.w) / (2 * (P.ρ * P.αg + 1 - P.ρ))
  have hδ3_pos : 0 < δ3 := div_pos hgap (mul_pos (by norm_num) hD1_pos)
  let ε := min (min (δ1 / 2) (δ2 / 2)) δ3
  have hε_pos : 0 < ε := lt_min (lt_min (half_pos hδ1_pos) (half_pos hδ2_pos)) hδ3_pos
  have hε_1 : ε ≤ δ1 / 2 := le_trans (min_le_left _ _) (min_le_left _ _)
  have hε_2 : ε ≤ δ2 / 2 := le_trans (min_le_left _ _) (min_le_right _ _)
  have hε_3 : ε ≤ δ3 := min_le_right _ _
  let wε := wstar + ε
  have hwε_gt_c : P.cost qstar < wε := by rw [hc_qs]; dsimp [wε]; linarith
  have hwε0 : 0 ≤ wε := (lt_trans hws_pos (by dsimp [wε]; linarith)).le
  have hwε_lt_L : wε < qstar * P.θL := by dsimp [wε, δ2] at *; linarith
  have hlow_ε : (qstar * P.θH - wε) * P.αb < qstar * P.θL - wε := by
    have : ε * (1 - P.αb) ≤ ε := mul_le_of_le_one_right hε_pos.le (by linarith)
    dsimp [wε, δ1] at *
    linarith
  have hresp := supplier_response_high P hStand Qbar h σ hpost qstar wε hqs_pos hwε_gt_c hlow_ε
  have hmem : σ.inv qstar wε ∈ Set.Icc (max 0 (1 - Qbar)) P.αg := by
    rw [← hresp]
    exact hinv qstar wε hqs_pos.le hwε0
  rcases hmem with ⟨hIε_lo, _hIε_hi⟩
  let Iε := σ.inv qstar wε
  have hIε0 : 0 ≤ Iε := le_trans (le_max_left _ _) hIε_lo
  have hSε_ge1 : 1 ≤ Iε + Qbar := by
    have := le_trans (le_max_right 0 (1 - Qbar)) hIε_lo
    linarith
  have hrecv_ε : ∀ s : State, ∀ Q : ℝ, 0 ≤ Q → σ.recv qstar wε Iε s Q = min Q (Iε + Qbar) := by
    intro s Q _hQ
    unfold Profile.recv received
    rcases le_or_gt Q Iε with hQI | hIQ
    · rw [if_pos hQI, min_eq_left (by linarith)]
    · rw [if_neg (not_le_of_gt hIQ)]
      obtain ⟨_hr0, _hrQ, hropt_r⟩ := hpost.2.1 qstar wε Iε s Q hqs_pos.le hwε0 hIε0 hIQ
      let Is := min Qbar (Q - Iε)
      have hge_r := hropt_r Is (le_min hQ_pos.le (sub_pos.mpr hIQ).le) (min_le_left _ _)
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
      rw [hreq]
      dsimp [Is]
      rcases le_or_gt Qbar (Q - Iε) with h1 | h1
      · rw [min_eq_left h1, min_eq_left (by linarith), min_eq_right (by linarith)]
      · rw [min_eq_right h1.le, show Iε + (Q - Iε) = Q by ring, min_self,
          min_eq_left (by linarith)]
  have hov_g_ge : (qstar * P.θH - wε) * P.αg ≤
      σ.orderValue P qstar wε Iε .good (σ.order qstar wε Iε .good) := by
    have h1 := (hpost.2.2 qstar wε Iε .good hqs_pos.le hwε0 hIε0).2 P.αg hαg0.le
    have hm_bds : 0 ≤ σ.made qstar wε Iε .good P.αg ∧ σ.made qstar wε Iε .good P.αg ≤ Qbar := by
      unfold Profile.made inSeason
      rcases le_or_gt P.αg Iε with hle | hgt
      · rw [if_pos hle]; exact ⟨le_refl 0, hQ_pos.le⟩
      · rw [if_neg (not_le_of_gt hgt)]
        obtain ⟨hr0, hrQ, _⟩ := hpost.2.1 qstar wε Iε .good P.αg hqs_pos.le hwε0 hIε0 hgt
        exact ⟨hr0, hrQ⟩
    have hp_opt := (hpost.1 qstar wε Iε .good P.αg (σ.made qstar wε Iε .good P.αg)
      hqs_pos.le hwε0 hIε0 hαg0.le hm_bds.1 hm_bds.2).2 (qstar * P.θH)
      (mul_pos hqs_pos hθH).le
    have hrm_eq : received Iε P.αg (σ.made qstar wε Iε .good P.αg) = P.αg := by
      have hrec := hrecv_ε .good P.αg hαg0.le
      rw [min_eq_left (by linarith)] at hrec
      unfold Profile.recv received at hrec
      unfold Profile.made received inSeason
      rcases le_or_gt P.αg Iε with h2 | h2
      · rw [if_pos h2]
      · rw [if_neg (not_le_of_gt h2), if_neg (not_le_of_gt h2)]; rw [if_neg (not_le_of_gt h2)] at hrec; exact hrec
    have hqLH : qstar * P.θL < qstar * P.θH := mul_lt_mul_of_pos_left hθLH hqs_pos
    have hrec_raw : σ.recv qstar wε Iε .good P.αg = P.αg := by
      rw [hrecv_ε .good P.αg hαg0.le, min_eq_left (by linarith)]
    unfold Profile.orderValue Profile.priceAfter at h1
    rw [hrec_raw] at h1
    rw [hrm_eq] at hp_opt
    have hlhs : P.retailerState qstar wε .good P.αg (qstar * P.θH) = (qstar * P.θH - wε) * P.αg := by
      unfold Params.retailerState Params.demand Params.alpha
      rw [if_neg (not_le_of_gt hqLH), if_pos (le_refl _), zero_add, min_self]
      ring
    rw [hlhs] at hp_opt
    exact le_trans hp_opt h1
  have hov_b_ge : qstar * P.θL - wε ≤
      σ.orderValue P qstar wε Iε .bad (σ.order qstar wε Iε .bad) := by
    have h1 := (hpost.2.2 qstar wε Iε .bad hqs_pos.le hwε0 hIε0).2 1 zero_le_one
    have hm_bds : 0 ≤ σ.made qstar wε Iε .bad 1 ∧ σ.made qstar wε Iε .bad 1 ≤ Qbar := by
      unfold Profile.made inSeason
      rcases le_or_gt 1 Iε with hle | hgt
      · rw [if_pos hle]; exact ⟨le_refl 0, hQ_pos.le⟩
      · rw [if_neg (not_le_of_gt hgt)]
        obtain ⟨hr0, hrQ, _⟩ := hpost.2.1 qstar wε Iε .bad 1 hqs_pos.le hwε0 hIε0 hgt
        exact ⟨hr0, hrQ⟩
    have hp_opt := (hpost.1 qstar wε Iε .bad 1 (σ.made qstar wε Iε .bad 1)
      hqs_pos.le hwε0 hIε0 zero_le_one hm_bds.1 hm_bds.2).2 (qstar * P.θL)
      (mul_pos hqs_pos hθL).le
    have hrm_eq : received Iε 1 (σ.made qstar wε Iε .bad 1) = 1 := by
      have hrec := hrecv_ε .bad 1 zero_le_one
      rw [min_eq_left hSε_ge1] at hrec
      unfold Profile.recv received at hrec
      unfold Profile.made received inSeason
      rcases le_or_gt 1 Iε with h2 | h2
      · rw [if_pos h2]
      · rw [if_neg (not_le_of_gt h2), if_neg (not_le_of_gt h2)]; rw [if_neg (not_le_of_gt h2)] at hrec; exact hrec
    have hqLH : qstar * P.θL < qstar * P.θH := mul_lt_mul_of_pos_left hθLH hqs_pos
    have hrec_raw : σ.recv qstar wε Iε .bad 1 = 1 := by
      rw [hrecv_ε .bad 1 zero_le_one, min_eq_left hSε_ge1]
    unfold Profile.orderValue Profile.priceAfter at h1
    rw [hrec_raw] at h1
    rw [hrm_eq] at hp_opt
    have hlhs : P.retailerState qstar wε .bad 1 (qstar * P.θL) = qstar * P.θL - wε := by
      unfold Params.retailerState Params.demand Params.alpha
      rw [if_pos (le_refl _), if_pos hqLH.le, sub_add_cancel, min_self]
      ring
    rw [hlhs] at hp_opt
    exact le_trans hp_opt h1
  have hrv_wε : V_TC - (P.ρ * P.αg + 1 - P.ρ) * ε ≤ σ.retailerValue P qstar wε := by
    have hid_qs : P.ρ * ((qstar * P.θH - wstar) * P.αg) +
        (1 - P.ρ) * (qstar * P.θL - wstar) = V_TC := val_qstar_tc P hk hD1_pos
    unfold Profile.retailerValue Params.prob
    change _ ≤ P.ρ * σ.orderValue P qstar wε Iε .good _ +
      (1 - P.ρ) * σ.orderValue P qstar wε Iε .bad _
    have := mul_le_mul_of_nonneg_left hov_g_ge hρ0.le
    have := mul_le_mul_of_nonneg_left hov_b_ge h1ρ.le
    dsimp [wε] at *
    linarith
  have hopt_ε := hropt qstar wε hqs_pos.le hwε0
  have hε_bound : (P.ρ * P.αg + 1 - P.ρ) * ε ≤ (V_TC - σ.retailerValue P σ.q σ.w) / 2 := by
    have := mul_le_mul_of_nonneg_left hε_3 hD1_pos.le
    dsimp [δ3] at this
    have heq : (P.ρ * P.αg + 1 - P.ρ) *
        ((V_TC - σ.retailerValue P σ.q σ.w) / (2 * (P.ρ * P.αg + 1 - P.ρ))) =
        (V_TC - σ.retailerValue P σ.q σ.w) / 2 := by
      field_simp [hD1_pos.ne']
    linarith
  linarith

theorem solution (P : Params) (hP : P.Dom) (Qbar : ℝ) (h : 1 - P.αg ≤ Qbar) :
    (∃ e : Outcome, IsEquilibrium P Qbar e) ∧
    ∀ e : Outcome, IsEquilibrium P Qbar e →
      e.πR = P.X ^ 2 * (P.ρ * P.αg + 1 - P.ρ) / (4 * P.k) ∧ e.πS = 0 ∧
      e.q = P.X / (2 * P.k) ∧ e.w = P.X ^ 2 / (4 * P.k) ∧
      e.p .good = P.X * P.θH / (2 * P.k) ∧ e.p .bad = P.X * P.θL / (2 * P.k) ∧
      max 0 (1 - Qbar) ≤ e.I ∧ e.I ≤ P.αg ∧ e.R .good = P.αg ∧ e.R .bad = 1 := by
  rcases hP with ⟨hStand, hFocus, hHOD⟩
  rcases hStand with ⟨hθL, hθLH, hk, hρ0, hρ1, hαb0, hαb_lt, hαg_gt, hαg1⟩
  have hStand : P.Standing := ⟨hθL, hθLH, hk, hρ0, hρ1, hαb0, hαb_lt, hαg_gt, hαg1⟩
  have hθH : 0 < P.θH := lt_trans hθL hθLH
  have hαg0 : 0 < P.αg := pos_of_mul_pos_left (lt_trans hθL hαg_gt) hθH.le
  have hαb_αg : P.αb < P.αg := lt_of_mul_lt_mul_right (lt_trans hαb_lt hαg_gt) hθH.le
  have hαb1 : P.αb < 1 := lt_trans hαb_αg hαg1
  have h1ρ : 0 < 1 - P.ρ := sub_pos.mpr hρ1
  have hQ_pos : 0 < Qbar := by linarith
  have hD1_pos : 0 < P.ρ * P.αg + 1 - P.ρ := by
    have : 0 < P.ρ * P.αg := mul_pos hρ0 hαg0
    linarith
  have hX_pos : 0 < P.X := by
    unfold Params.X Params.Y
    refine div_pos ?_ (by linarith)
    have h1 : 0 < P.ρ * P.αg * P.θH := mul_pos (mul_pos hρ0 hαg0) hθH
    have h2 : 0 < (1 - P.ρ) * 1 * P.θL := mul_pos (mul_pos h1ρ zero_lt_one) hθL
    linarith
  have hX_le_Y0 : P.X ≤ P.ρ * P.θH + (1 - P.ρ) * P.θL := by
    unfold Params.X Params.Y
    rw [div_le_iff₀ (by linarith : 0 < P.ρ * P.αg + (1 - P.ρ) * 1)]
    have : 0 ≤ P.ρ * (1 - P.ρ) * (1 - P.αg) * (P.θH - P.θL) :=
      mul_nonneg (mul_nonneg (mul_nonneg hρ0.le h1ρ.le) (by linarith)) (by linarith)
    linarith
  have hX_focus : P.X * (1 - P.αb) < 2 * (P.θL - P.θH * P.αb) := by
    have h1 : P.X * (1 - P.αb) * (P.αg - P.αb) ≤
        (P.ρ * P.θH + (1 - P.ρ) * P.θL) * (P.αg - P.αb) * (1 - P.αb) := by
      have := mul_le_mul_of_nonneg_right hX_le_Y0
        (mul_nonneg (by linarith : 0 ≤ 1 - P.αb) (by linarith : 0 ≤ P.αg - P.αb))
      linarith
    have h2 : (P.ρ * P.θH + (1 - P.ρ) * P.θL) * (P.αg - P.αb) * (1 - P.αb) <
        2 * (P.θL * P.αg - P.θH * P.αb) * (1 - P.αb) :=
      mul_lt_mul_of_pos_right hFocus (by linarith)
    have h3 : 2 * (P.θL * P.αg - P.θH * P.αb) * (1 - P.αb) ≤
        2 * (P.θL - P.θH * P.αb) * (P.αg - P.αb) := by
      have : 0 ≤ 2 * (P.θH - P.θL) * P.αb * (1 - P.αg) :=
        mul_nonneg (mul_nonneg (by linarith) hαb0.le) (by linarith)
      linarith
    exact lt_of_mul_lt_mul_right (lt_of_le_of_lt h1 (lt_of_lt_of_le h2 h3)) (by linarith)
  have hY0_lt_2θL : P.ρ * P.θH + (1 - P.ρ) * P.θL < 2 * P.θL := by
    have h1 : 2 * (P.θL * P.αg - P.θH * P.αb) < 2 * P.θL * (P.αg - P.αb) := by
      have : 0 < (P.θH - P.θL) * P.αb := mul_pos (by linarith) hαb0
      linarith
    exact lt_of_mul_lt_mul_right (lt_trans hFocus h1) (by linarith : 0 ≤ P.αg - P.αb)
  have hX_lt_2θL : P.X < 2 * P.θL := lt_of_le_of_lt hX_le_Y0 hY0_lt_2θL
  have hHOD_TC : (P.ρ * P.αg + (1 - P.ρ) * P.αb) * P.θH ^ 2 / (4 * P.k) <
      P.X ^ 2 * (P.ρ * P.αg + 1 - P.ρ) / (4 * P.k) := by
    unfold Params.HighOnlyDominated at hHOD
    have h4k : 0 < 4 * P.k := by linarith
    rw [div_lt_div_iff_of_pos_right h4k]
    have hX_eq : P.X ^ 2 * (P.ρ * P.αg + 1 - P.ρ) =
        (P.ρ * P.αg * P.θH + (1 - P.ρ) * P.θL) ^ 2 / (P.ρ * P.αg + 1 - P.ρ) := by
      unfold Params.X Params.Y
      have hd : P.ρ * P.αg + (1 - P.ρ) * 1 = P.ρ * P.αg + 1 - P.ρ := by ring
      rw [hd, div_pow, div_mul_eq_mul_div, sq (P.ρ * P.αg + 1 - P.ρ),
        mul_div_mul_right _ _ hD1_pos.ne']
      ring_nf
    rw [hX_eq]
    refine lt_of_lt_of_le hHOD (max_le ?_ ?_)
    · exact div_le_div_of_nonneg_right
        (mul_le_of_le_one_left (sq_nonneg _) (by linarith : 1 - P.ρ ≤ 1)) hD1_pos.le
    · rw [le_div_iff₀ hD1_pos]
      let C := P.ρ * P.αg * (P.θH - P.θL)
      let u1 := P.αg
      let u2 := P.ρ * P.αg + 1 - P.ρ
      have hu1_lt_u2 : u1 < u2 := by dsimp [u1, u2]; nlinarith
      have hC_lt : C < u1 * P.θL := by
        dsimp [C, u1]
        have : P.ρ * (P.θH - P.θL) < P.θL := by linarith
        nlinarith
      have hC0 : 0 < C := mul_pos (mul_pos hρ0 hαg0) (by linarith)
      have hC2 : C ^ 2 ≤ u1 * u2 * P.θL ^ 2 := by
        have h1 : C ^ 2 ≤ (u1 * P.θL) ^ 2 := sq_le_sq' (by linarith) hC_lt.le
        have h2 : (u1 * P.θL) ^ 2 ≤ u1 * u2 * P.θL ^ 2 := by
          have : u1 ^ 2 ≤ u1 * u2 := by nlinarith
          nlinarith
        linarith
      have hid : (P.ρ * P.αg * P.θH + (1 - P.ρ) * P.θL) ^ 2 -
          P.αg * (P.ρ * P.θH + (1 - P.ρ) * P.θL) ^ 2 * (P.ρ * P.αg + 1 - P.ρ) =
          (u2 - u1) * (u1 * u2 * P.θL ^ 2 - C ^ 2) / u1 := by
        dsimp [u1, u2, C]
        field_simp [hαg0.ne']
        ring
      have hpos : 0 ≤ (u2 - u1) * (u1 * u2 * P.θL ^ 2 - C ^ 2) / u1 :=
        div_nonneg (mul_nonneg (by linarith) (by linarith)) hαg0.le
      linarith
  refine ⟨exists_tc P hStand hX_pos hX_lt_2θL hX_focus hHOD_TC Qbar h, ?_⟩
  rintro e ⟨σ, hSPE, rfl⟩
  have hrv_ge := lb_tc P hStand hX_pos hX_lt_2θL hX_focus Qbar h σ hSPE
  rcases hSPE with ⟨hpost, hinv, hq0, hw0, _hropt⟩
  have h_ub := ub_char_tc P hStand hHOD_TC Qbar hQ_pos σ hpost hinv σ.q σ.w hq0 hw0
  have hrv_eq : σ.retailerValue P σ.q σ.w = P.X ^ 2 * (P.ρ * P.αg + 1 - P.ρ) / (4 * P.k) :=
    le_antisymm h_ub.1 hrv_ge
  obtain ⟨hπS, hq_eq, hw_eq, hpg, hpb, hI_lo, hI_hi, hRg, hRb⟩ := h_ub.2 hrv_eq
  exact ⟨hrv_eq, hπS, hq_eq, hw_eq, hpg, hpb, hI_lo, hI_hi, hRg, hRb⟩
