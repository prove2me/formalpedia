-- Prove2me | solution 1 for ReviewBlackmail.SemiDec.step1_mechanism
-- status  : ACCEPTED   (prove)
-- author  : @arexychen
-- created : 2026-10-17T16:54:49.504473+00:00
-- url     : https://prove2.me/submissions/7322364b-8fcf-4f1e-a3a9-241d3110f206

import Definitions.Def_ReviewBlackmail_SemiDec_Setting

open ReviewBlackmail.SemiDec

namespace BlackmailProof

lemma buy_bounds (M : Model) (hM : M.Standing) : 0 < M.buyProb ∧ M.buyProb < 1 := by
  rcases hM with ⟨ha, ha1, ht, ht1, hb, hb1, _, _, _, hg, hg1, hd, hd1, hB, hp, hp1⟩
  have hat : 0 < M.a * M.θ := mul_pos ha ht
  unfold Model.buyProb
  constructor
  · exact sub_pos.mpr ((div_lt_one hat).mpr hp1)
  · have := div_pos hp hat
    linarith

lemma postZ (M : Model) (hM : M.Standing) (m : ℝ) (hm : m ∈ Set.Icc (0 : ℝ) 1) :
    M.post m 1 .Z = M.a := by
  have hr := buy_bounds M hM
  have hb : 0 < 1 - M.β := sub_pos.mpr hM.2.2.2.2.2.1
  have hβ : 0 < M.β := hM.2.2.2.2.1
  have hp : 0 < M.β * (1-m) + (1-M.β)*(1-M.buyProb) :=
    add_pos_of_nonneg_of_pos (mul_nonneg hβ.le (sub_nonneg.mpr hm.2)) (mul_pos hb (sub_pos.mpr hr.2))
  simp only [Model.post, Model.lik, sub_self, mul_zero, add_zero]
  rw [show M.a * (M.β * (1-m)+(1-M.β)*(1-M.buyProb)) + (1-M.a)*(M.β*(1-m)+(1-M.β)*(1-M.buyProb)) =
      M.β*(1-m)+(1-M.β)*(1-M.buyProb) by ring]
  exact mul_div_cancel_right₀ M.a (ne_of_gt hp)

lemma postN_den (M : Model) (hM : M.Standing) (m : ℝ) (hm : 0 ≤ m) :
    0 < M.a * (M.β*m+(1-M.β)*M.buyProb*(1-M.θ)) +
      (1-M.a)*(M.β*m+(1-M.β)*M.buyProb) := by
  have hr := buy_bounds M hM
  have hq : 0 < (1-M.β)*M.buyProb := mul_pos (sub_pos.mpr hM.2.2.2.2.2.1) hr.1
  have hbm : 0 ≤ M.β*m := mul_nonneg hM.2.2.2.2.1.le hm
  exact add_pos (mul_pos hM.1 (add_pos_of_nonneg_of_pos hbm (mul_pos hq (sub_pos.mpr hM.2.2.2.1))))
    (mul_pos (sub_pos.mpr hM.2.1) (add_pos_of_nonneg_of_pos hbm hq))

lemma postN_bounds (M : Model) (hM : M.Standing) (m : ℝ) (hm : 0 ≤ m) :
    0 < M.post m 1 .N ∧ M.post m 1 .N < M.a := by
  have hr := buy_bounds M hM
  have hq : 0 < (1-M.β)*M.buyProb := mul_pos (sub_pos.mpr hM.2.2.2.2.2.1) hr.1
  have hh : 0 < M.β*m+(1-M.β)*M.buyProb*(1-M.θ) :=
    add_pos_of_nonneg_of_pos (mul_nonneg hM.2.2.2.2.1.le hm) (mul_pos hq (sub_pos.mpr hM.2.2.2.1))
  have hd := postN_den M hM m hm
  simp only [Model.post, Model.lik, mul_one]
  constructor
  · exact div_pos (mul_pos hM.1 hh) hd
  · apply (div_lt_iff₀ hd).mpr
    have hp := mul_pos (mul_pos hM.1 (sub_pos.mpr hM.2.1)) (mul_pos hq hM.2.2.1)
    nlinarith only [hp]

lemma postN_strict (M : Model) (hM : M.Standing) {x y : ℝ} (hx : 0 ≤ x) (hxy : x < y) :
    M.post x 1 .N < M.post y 1 .N := by
  have hr := buy_bounds M hM
  have hd1 := postN_den M hM x hx
  have hd2 := postN_den M hM y (hx.trans hxy.le)
  simp only [Model.post, Model.lik, mul_one]
  apply (div_lt_div_iff₀ hd1 hd2).mpr
  have hp := mul_pos (mul_pos (mul_pos (mul_pos (mul_pos hM.1
    (sub_pos.mpr hM.2.1)) hM.2.2.2.2.1) (sub_pos.mpr hM.2.2.2.2.2.1))
    hr.1) (mul_pos hM.2.2.1 (sub_pos.mpr hxy))
  nlinarith only [hp]

lemma postN_mono (M : Model) (hM : M.Standing) {x y : ℝ} (hx : 0 ≤ x) (hxy : x ≤ y) :
    M.post x 1 .N ≤ M.post y 1 .N := by
  rcases hxy.eq_or_lt with rfl | h
  · exact le_rfl
  · exact (postN_strict M hM hx h).le

lemma postN_form (M : Model) (hM : M.Standing) (m : ℝ) (hm : 0 ≤ m) :
    M.post m 1 .N = M.a / (M.a + (1-M.a)*
      ((M.β*m+(1-M.β)*M.buyProb)/(M.β*m+(1-M.β)*M.buyProb*(1-M.θ)))) := by
  have hr := buy_bounds M hM
  have hh : 0 < M.β*m+(1-M.β)*M.buyProb*(1-M.θ) :=
    add_pos_of_nonneg_of_pos (mul_nonneg hM.2.2.2.2.1.le hm)
      (mul_pos (mul_pos (sub_pos.mpr hM.2.2.2.2.2.1) hr.1) (sub_pos.mpr hM.2.2.2.1))
  simp only [Model.post, Model.lik, mul_one]
  rw [show M.a + (1-M.a) * ((M.β*m+(1-M.β)*M.buyProb) /
      (M.β*m+(1-M.β)*M.buyProb*(1-M.θ))) =
      (M.a * (M.β*m+(1-M.β)*M.buyProb*(1-M.θ)) +
      (1-M.a)*(M.β*m+(1-M.β)*M.buyProb)) /
      (M.β*m+(1-M.β)*M.buyProb*(1-M.θ)) by field_simp]
  rw [div_div_eq_mul_div]

lemma zeroN (M : Model) (hM : M.Standing) :
    M.post 0 1 .N = M.a / (M.a + (1-M.a)*(1/(1-M.θ))) := by
  rw [postN_form M hM 0 (le_refl 0)]
  have hr := buy_bounds M hM
  have hq : (1-M.β)*M.buyProb ≠ 0 := ne_of_gt (mul_pos (sub_pos.mpr hM.2.2.2.2.2.1) hr.1)
  simp only [mul_zero, zero_add]
  rw [show (1-M.β)*M.buyProb / ((1-M.β)*M.buyProb*(1-M.θ)) = 1/(1-M.θ) by
    simpa only [mul_one] using mul_div_mul_left (1:ℝ) (1-M.θ) hq]

lemma vis_bounds (M : Model) (hM : M.Standing) (i : Resp) : M.vis i ∈ Set.Icc (0:ℝ) 1 := by
  have hg : 0 ≤ M.γ := hM.2.2.2.2.2.2.2.2.2.1
  have hg1 : M.γ ≤ 1 := hM.2.2.2.2.2.2.2.2.2.2.1
  have hd : 0 ≤ M.δ := hM.2.2.2.2.2.2.2.2.2.2.2.1
  have hd1 : M.δ ≤ 1 := hM.2.2.2.2.2.2.2.2.2.2.2.2.1
  cases i <;> simp only [Model.vis, Set.mem_Icc]
  · norm_num
  · norm_num
  · exact ⟨mul_nonneg hg (sub_nonneg.mpr hd1), by nlinarith [mul_nonneg hg hd]⟩

lemma postZ_vis (M : Model) (hM : M.Standing) (i : Resp) : M.post (M.vis i) 1 .Z = M.a :=
  postZ M hM (M.vis i) (vis_bounds M hM i)

lemma semi_eq5 (M : Model) (hM : M.Standing) :
    (∀ m ∈ Set.Icc (0 : ℝ) 1, M.post m 1 .Z = M.a) ∧
    M.post (M.γ * (1 - M.δ)) 1 .N =
      M.a / (M.a + (1 - M.a) *
        ((M.β * M.γ * (1 - M.δ) + (1 - M.β) * (1 - M.p / (M.a * M.θ))) /
          (M.β * M.γ * (1 - M.δ) + (1 - M.β) * (1 - M.p / (M.a * M.θ)) * (1 - M.θ)))) ∧
    M.post 1 1 .N =
      M.a / (M.a + (1 - M.a) *
        ((M.β + (1 - M.β) * (1 - M.p / (M.a * M.θ))) /
          (M.β + (1 - M.β) * (1 - M.p / (M.a * M.θ)) * (1 - M.θ)))) ∧
    M.post 0 1 .N = M.a / (M.a + (1 - M.a) * (1 / (1 - M.θ))) := by
  refine ⟨postZ M hM, ?_, ?_, zeroN M hM⟩
  · simpa only [Model.buyProb, mul_assoc] using postN_form M hM (M.γ*(1-M.δ)) (vis_bounds M hM .d).1
  · simpa only [Model.buyProb, mul_one] using postN_form M hM 1 (by norm_num)

lemma semi_order (M : Model) (hM : M.Standing)
    (h0 : 0 < M.γ * (1 - M.δ)) (h1 : M.γ * (1 - M.δ) < 1) :
    M.post 0 1 .N < M.post (M.γ * (1 - M.δ)) 1 .N ∧
      M.post (M.γ * (1 - M.δ)) 1 .N < M.post 1 1 .N :=
  ⟨postN_strict M hM (le_refl 0) h0, postN_strict M hM h0.le h1⟩

lemma eq_s (M : Model) (hM : M.Standing) (r : ℝ) :
    M.IsEq .s r ↔ r ≤ M.fut M.a - M.fut (M.post 0 1 .N) ∧
      r ≤ (1-M.δ)*(M.γ*(M.fut M.a-M.fut (M.post 0 1 .N))+M.b) := by
  have hz := postZ_vis M hM .s
  constructor
  · intro h
    have hn := h .n
    have hd := h .d
    simp only [Model.pay, Model.vis] at hn hd hz
    rw [hz] at hn hd
    constructor <;> nlinarith
  · rintro ⟨hn, hd⟩ j
    cases j <;> simp only [Model.pay, Model.vis] <;> simp only [Model.vis] at hz
    all_goals rw [hz]
    all_goals nlinarith

lemma eq_n_mul (M : Model) (hM : M.Standing) (r : ℝ) :
    M.IsEq .n r ↔ M.fut M.a - M.fut (M.post 1 1 .N) ≤ r ∧
      (1-M.γ*(1-M.δ))*(M.fut M.a-M.fut (M.post 1 1 .N)) ≤ (1-M.δ)*M.b := by
  have hz := postZ_vis M hM .n
  constructor
  · intro h
    have hs := h .s
    have hd := h .d
    simp only [Model.pay, Model.vis] at hs hd hz
    rw [hz] at hs hd
    constructor <;> nlinarith
  · rintro ⟨hs, hd⟩ j
    cases j <;> simp only [Model.pay, Model.vis] <;> simp only [Model.vis] at hz
    all_goals try rw [hz]
    all_goals nlinarith

lemma eq_d_mul (M : Model) (hM : M.Standing) (r : ℝ) :
    M.IsEq .d r ↔
      (1-M.δ)*M.b ≤ (1-M.γ*(1-M.δ))*(M.fut M.a-M.fut (M.post (M.γ*(1-M.δ)) 1 .N)) ∧
      (1-M.δ)*(M.γ*(M.fut M.a-M.fut (M.post (M.γ*(1-M.δ)) 1 .N))+M.b) ≤ r := by
  have hz := postZ_vis M hM .d
  constructor
  · intro h
    have hs := h .s
    have hn := h .n
    simp only [Model.pay, Model.vis] at hs hn hz
    rw [hz] at hs hn
    constructor <;> nlinarith
  · rintro ⟨hn, hs⟩ j
    cases j <;> simp only [Model.pay, Model.vis] <;> simp only [Model.vis] at hz
    all_goals rw [hz]
    all_goals nlinarith

end BlackmailProof


namespace BlackmailGame

def prevails (S N D t c r : ℝ) : Prop :=
  (r ≤ S ∧ r ≤ t*S+c) ∧
  ((N ≤ r ∧ (1-t)*N ≤ c) → r ≤ N) ∧
  ((c ≤ (1-t)*D ∧ t*D+c ≤ r) → r ≤ t*D+c)

lemma greatest_high (S N D t c : ℝ) (hND : N ≤ D) (hDS : D ≤ S)
    (ht : 0 ≤ t) (ht1 : t ≤ 1) (hc : (1-t)*N ≤ c) :
    IsGreatest {r | prevails S N D t c r} N := by
  have hNS := hND.trans hDS
  have htNS := mul_nonneg ht (sub_nonneg.mpr hNS)
  have htND := mul_nonneg ht (sub_nonneg.mpr hND)
  refine ⟨⟨⟨le_trans hND hDS, ?_⟩, ?_, ?_⟩, ?_⟩
  · nlinarith
  · intro _; exact le_rfl
  · intro _; nlinarith
  · intro r hr
    rcases le_total r N with h | h
    · exact h
    · exact hr.2.1 ⟨h, hc⟩

lemma greatest_low (S N D t c : ℝ) (hND : N ≤ D) (hDS : D ≤ S)
    (ht : 0 ≤ t) (ht1 : t ≤ 1) (hc : c < (1-t)*N) :
    IsGreatest {r | prevails S N D t c r} (t*D+c) := by
  have hcmp := mul_nonneg (sub_nonneg.mpr ht1) (sub_nonneg.mpr hND)
  have hcD : c ≤ (1-t)*D := by nlinarith
  have hDS' := mul_nonneg ht (sub_nonneg.mpr hDS)
  refine ⟨⟨⟨?_, ?_⟩, ?_, ?_⟩, ?_⟩
  · nlinarith
  · nlinarith
  · intro h; exact False.elim (not_le.mpr hc h.2)
  · intro _; exact le_rfl
  · intro r hr
    rcases le_total r (t*D+c) with h | h
    · exact h
    · exact hr.2.2 ⟨hcD, h⟩

lemma purchase_iff {P : ℝ → Prop} {r p : ℝ} (h : IsGreatest {r | P r} r) :
    (∃ v, P v ∧ p < v) ↔ p < r := by
  constructor
  · rintro ⟨v, hv, hp⟩
    exact hp.trans_le (h.2 hv)
  · intro hp
    exact ⟨r, h.1, hp⟩

end BlackmailGame


open ReviewBlackmail.SemiDec

namespace BlackmailProof

lemma bayes_bounds (a H L : ℝ) (ha : 0<a) (ha1 : a<1) (hH : 0<H) (hHL : H<L) :
    0 < a*H/(a*H+(1-a)*L) ∧ a*H/(a*H+(1-a)*L) < a := by
  have hd : 0 < a*H+(1-a)*L := add_pos (mul_pos ha hH) (mul_pos (sub_pos.mpr ha1) (hH.trans hHL))
  refine ⟨div_pos (mul_pos ha hH) hd, (div_lt_iff₀ hd).mpr ?_⟩
  have := mul_pos (mul_pos ha (sub_pos.mpr ha1)) (sub_pos.mpr hHL)
  nlinarith

lemma removedN (M : Model) (hM : M.Standing) (hg : 0<M.γ) :
    M.post 0 M.γ .N = M.post 0 1 .N := by
  simp only [Model.post, Model.lik, mul_zero, zero_add, mul_one]
  rw [show M.a * ((1-M.β)*M.buyProb*(1-M.θ)*M.γ) + (1-M.a)*((1-M.β)*M.buyProb*M.γ) =
    (M.a*((1-M.β)*M.buyProb*(1-M.θ))+(1-M.a)*((1-M.β)*M.buyProb))*M.γ by ring]
  rw [← mul_assoc M.a _ M.γ, mul_div_mul_right _ _ hg.ne']

lemma removedZ (M : Model) (hM : M.Standing) (hg : 0<M.γ) (hg1 : M.γ<1) :
    0 < M.post 0 M.γ .Z ∧ M.post 0 M.γ .Z < M.a := by
  have hr := buy_bounds M hM
  let H := M.β+(1-M.β)*((1-M.buyProb)+M.buyProb*(1-M.θ)*(1-M.γ))
  let L := M.β+(1-M.β)*((1-M.buyProb)+M.buyProb*(1-M.γ))
  have hH : 0<H := by
    dsimp [H]
    exact add_pos hM.2.2.2.2.1 (mul_pos (sub_pos.mpr hM.2.2.2.2.2.1)
      (add_pos (sub_pos.mpr hr.2) (mul_pos (mul_pos hr.1 (sub_pos.mpr hM.2.2.2.1)) (sub_pos.mpr hg1))))
  have hHL : H<L := by
    have := mul_pos (mul_pos (mul_pos (sub_pos.mpr hM.2.2.2.2.2.1) hr.1) hM.2.2.1) (sub_pos.mpr hg1)
    dsimp [H,L]
    nlinarith only [this]
  simpa only [Model.post, Model.lik, sub_zero, mul_one] using bayes_bounds M.a H L hM.1 hM.2.1 hH hHL

lemma semi_prop4 (M : Model) (hM : M.Standing) :
    (M.KeepGenuineBR ↔ M.bLow ≤ M.b) ∧
    (0 < M.γ → M.γ < 1 → M.bLow ≤ M.b → ¬ M.RemoveGenuineBR) := by
  have hz := postZ M hM 0 (by constructor <;> norm_num)
  constructor
  · unfold Model.KeepGenuineBR Model.bLow
    rw [hz]
    constructor <;> intro h <;> nlinarith
  · intro hg hg1 hb hrem
    have hZ := removedZ M hM hg hg1
    have hstrict := hM.2.2.2.2.2.2.2.2.1
      ⟨hZ.1.le, hZ.2.le.trans hM.2.1.le⟩ ⟨hM.1.le,hM.2.1.le⟩ hZ.2
    have hpos := mul_pos (sub_pos.mpr hg1) (sub_pos.mpr hstrict)
    unfold Model.RemoveGenuineBR at hrem
    rw [removedN M hM hg] at hrem
    unfold Model.bLow at hb
    nlinarith

lemma semi_settle (M : Model) (hM : M.Standing) (r : ℝ) :
    M.IsEq .s r ↔ r ≤ min (M.fut M.a - M.fut (M.post 0 1 .N))
      ((1-M.δ)*(M.γ*(M.fut M.a-M.fut (M.post 0 1 .N))+M.b)) := by
  rw [le_min_iff]
  exact eq_s M hM r

lemma semi_nothing (M : Model) (hM : M.Standing) (hδ : M.δ<1) (r : ℝ) :
    M.IsEq .n r ↔ M.fut M.a - M.fut (M.post 1 1 .N) ≤ r ∧
      (1-M.γ*(1-M.δ))/(1-M.δ)*(M.fut M.a-M.fut (M.post 1 1 .N)) ≤ M.b := by
  rw [eq_n_mul M hM r]
  rw [div_mul_eq_mul_div, div_le_iff₀ (sub_pos.mpr hδ)]
  simp only [mul_comm (1-M.δ) M.b]

lemma semi_mechanism (M : Model) (hM : M.Standing) (hδ : M.δ<1) (r : ℝ) :
    M.IsEq .d r ↔
      M.b ≤ (1-M.γ*(1-M.δ))/(1-M.δ)*(M.fut M.a-M.fut (M.post (M.γ*(1-M.δ)) 1 .N)) ∧
      (1-M.δ)*(M.γ*(M.fut M.a-M.fut (M.post (M.γ*(1-M.δ)) 1 .N))+M.b) ≤ r := by
  rw [eq_d_mul M hM r]
  rw [div_mul_eq_mul_div, le_div_iff₀ (sub_pos.mpr hδ)]
  simp only [mul_comm (1-M.δ) M.b]

lemma prevail_iff (M : Model) (hM : M.Standing) (r : ℝ) :
    M.SettlePrevails r ↔ BlackmailGame.prevails
      (M.fut M.a-M.fut (M.post 0 1 .N))
      (M.fut M.a-M.fut (M.post 1 1 .N))
      (M.fut M.a-M.fut (M.post (M.γ*(1-M.δ)) 1 .N))
      (M.γ*(1-M.δ)) ((1-M.δ)*M.b) r := by
  have hs := postZ_vis M hM .s
  have hn := postZ_vis M hM .n
  have hd := postZ_vis M hM .d
  simp only [Model.vis] at hs hn hd
  constructor
  · rintro ⟨h, hp⟩
    have h' := (eq_s M hM r).mp h
    refine ⟨⟨h'.1, by nlinarith [h'.2]⟩, ?_, ?_⟩
    · intro hN
      have hx := hp .n ((eq_n_mul M hM r).mpr hN)
      simp only [Model.pay, Model.vis, hs] at hx
      linarith
    · intro hD
      have hx := hp .d ((eq_d_mul M hM r).mpr ⟨hD.1, by nlinarith [hD.2]⟩)
      simp only [Model.pay, Model.vis, hs, hd] at hx
      nlinarith
  · rintro ⟨h, hN, hD⟩
    refine ⟨(eq_s M hM r).mpr ⟨h.1, by nlinarith [h.2]⟩, ?_⟩
    intro i hi
    cases i with
    | s => exact le_rfl
    | n =>
      have hx := hN ((eq_n_mul M hM r).mp hi)
      simp only [Model.pay, Model.vis, hs]
      linarith
    | d =>
      have hi' := (eq_d_mul M hM r).mp hi
      have hx := hD ⟨hi'.1, by nlinarith [hi'.2]⟩
      simp only [Model.pay, Model.vis, hs, hd]
      nlinarith

lemma gap_order (M : Model) (hM : M.Standing) :
    M.fut M.a-M.fut (M.post 1 1 .N) ≤ M.fut M.a-M.fut (M.post (M.γ*(1-M.δ)) 1 .N) ∧
    M.fut M.a-M.fut (M.post (M.γ*(1-M.δ)) 1 .N) ≤ M.fut M.a-M.fut (M.post 0 1 .N) := by
  have hm := vis_bounds M hM .d
  have h0 := postN_bounds M hM 0 (le_refl 0)
  have h1 := postN_bounds M hM 1 (by norm_num)
  have hd := postN_bounds M hM (M.γ*(1-M.δ)) hm.1
  have hf := hM.2.2.2.2.2.2.2.2.1.monotoneOn
  have h01 := hf ⟨h0.1.le,h0.2.le.trans hM.2.1.le⟩ ⟨hd.1.le,hd.2.le.trans hM.2.1.le⟩
    (postN_mono M hM (le_refl 0) hm.1)
  have hd1 := hf ⟨hd.1.le,hd.2.le.trans hM.2.1.le⟩ ⟨h1.1.le,h1.2.le.trans hM.2.1.le⟩
    (postN_mono M hM hm.1 hm.2)
  constructor <;> linarith

lemma semi_prop5 (M : Model) (hM : M.Standing) (hδ : M.δ < 1) :
    ((1 - M.γ * (1 - M.δ)) / (1 - M.δ) * (M.fut M.a - M.fut (M.post 1 1 .N)) ≤ M.b →
      M.bLow < (1 - M.γ * (1 - M.δ)) / (1 - M.δ) * (M.fut M.a - M.fut (M.post 1 1 .N)) →
      IsGreatest {r | M.SettlePrevails r} (M.fut M.a - M.fut (M.post 1 1 .N)) ∧
        (M.Purchases ↔ M.p < M.fut M.a - M.fut (M.post 1 1 .N))) ∧
    (M.bLow ≤ M.b →
      M.b < (1 - M.γ * (1 - M.δ)) / (1 - M.δ) * (M.fut M.a - M.fut (M.post 1 1 .N)) →
      IsGreatest {r | M.SettlePrevails r}
          ((1 - M.δ) * (M.γ * (M.fut M.a - M.fut (M.post (M.γ * (1 - M.δ)) 1 .N)) + M.b)) ∧
        (M.Purchases ↔
          M.p < (1 - M.δ) * (M.γ * (M.fut M.a - M.fut (M.post (M.γ * (1 - M.δ)) 1 .N)) + M.b))) := by
  have ho := gap_order M hM
  have ht := vis_bounds M hM .d
  simp only [Model.vis] at ht
  have hset : {r | M.SettlePrevails r} = {r | BlackmailGame.prevails
      (M.fut M.a-M.fut (M.post 0 1 .N))
      (M.fut M.a-M.fut (M.post 1 1 .N))
      (M.fut M.a-M.fut (M.post (M.γ*(1-M.δ)) 1 .N))
      (M.γ*(1-M.δ)) ((1-M.δ)*M.b) r} := by
    ext r
    exact prevail_iff M hM r
  constructor
  · intro hb _
    rw [div_mul_eq_mul_div, div_le_iff₀ (sub_pos.mpr hδ)] at hb
    have hg := BlackmailGame.greatest_high _ _ _ _ _ ho.1 ho.2 ht.1 ht.2
      (by simpa only [mul_comm M.b] using hb)
    rw [← hset] at hg
    exact ⟨hg, BlackmailGame.purchase_iff hg⟩
  · intro _ hb
    rw [div_mul_eq_mul_div, lt_div_iff₀ (sub_pos.mpr hδ)] at hb
    have hg := BlackmailGame.greatest_low _ _ _ _ _ ho.1 ho.2 ht.1 ht.2
      (by simpa only [mul_comm M.b] using hb)
    rw [← hset] at hg
    have hr : M.γ*(1-M.δ)*(M.fut M.a-M.fut (M.post (M.γ*(1-M.δ)) 1 .N))+(1-M.δ)*M.b =
        (1-M.δ)*(M.γ*(M.fut M.a-M.fut (M.post (M.γ*(1-M.δ)) 1 .N))+M.b) := by ring
    rw [hr] at hg
    exact ⟨hg, BlackmailGame.purchase_iff hg⟩

end BlackmailProof


open ReviewBlackmail.SemiDec

theorem solution (M : Model) (hM : M.Standing) (hδ : M.δ < 1) (r : ℝ) :
    M.IsEq .d r ↔
      M.b ≤ (1 - M.γ * (1 - M.δ)) / (1 - M.δ) *
          (M.fut M.a - M.fut (M.post (M.γ * (1 - M.δ)) 1 .N)) ∧
        (1 - M.δ) * (M.γ * (M.fut M.a - M.fut (M.post (M.γ * (1 - M.δ)) 1 .N)) + M.b) ≤ r := by
  exact BlackmailProof.semi_mechanism M hM hδ r
