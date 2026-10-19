-- Prove2me | solution 1 for ReviewBlackmail.Central.proposition_1_3
-- status  : ACCEPTED   (prove)
-- author  : @arexychen
-- created : 2026-10-17T17:05:06.956985+00:00
-- url     : https://prove2.me/submissions/a3d459a7-e897-4a0e-9e5f-011107eca93e

import Definitions.Def_ReviewBlackmail_SemiDec_Setting
import Definitions.Def_ReviewBlackmail_Central_Setting

section

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

end

section

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

end

section

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

end

section

open ReviewBlackmail.Central

namespace CentralProof

def embed (M : Model) (e : ℝ) : ReviewBlackmail.SemiDec.Model :=
  ⟨M.a, M.θ, M.β, M.p, 1-e, 0, M.c, M.π⟩

@[simp] lemma embed_a (M : Model) (e : ℝ) : (embed M e).a=M.a := rfl
@[simp] lemma embed_theta (M : Model) (e : ℝ) : (embed M e).θ=M.θ := rfl
@[simp] lemma embed_beta (M : Model) (e : ℝ) : (embed M e).β=M.β := rfl
@[simp] lemma embed_p (M : Model) (e : ℝ) : (embed M e).p=M.p := rfl
@[simp] lemma embed_gamma (M : Model) (e : ℝ) : (embed M e).γ=1-e := rfl
@[simp] lemma embed_delta (M : Model) (e : ℝ) : (embed M e).δ=0 := rfl
@[simp] lemma embed_b (M : Model) (e : ℝ) : (embed M e).b=M.c := rfl
@[simp] lemma embed_fut (M : Model) (e : ℝ) : (embed M e).fut=M.π := rfl

lemma embed_standing (M : Model) (hM : M.Standing) {e : ℝ} (he : e ∈ Set.Icc (0:ℝ) 1) :
    (embed M e).Standing := by
  rcases hM with ⟨ha,ha1,hθ,hθ1,hβ,hβ1,hπ,hconv,hmono,hc,hp,hp1⟩
  exact ⟨ha,ha1,hθ,hθ1,hβ,hβ1,hπ,hconv,hmono,sub_nonneg.mpr he.2,
    by dsimp [embed]; linarith [he.1],le_refl 0,by norm_num [embed],hc,hp,hp1⟩

def rv : Review → ReviewBlackmail.SemiDec.Review
  | .N => .N | .Z => .Z | .P => .P

def rs : Resp → ReviewBlackmail.SemiDec.Resp
  | .s => .s | .n => .n | .c => .d

lemma post_embed (M : Model) (e m : ℝ) (R : Review) :
    (embed M e).post m 1 (rv R) = M.post m R := by
  cases R <;> simp [ReviewBlackmail.SemiDec.Model.post, ReviewBlackmail.SemiDec.Model.lik,
    ReviewBlackmail.SemiDec.Model.buyProb, Model.post, Model.lik, Model.buyProb, embed, rv]

@[simp] lemma postN_embed (M : Model) (e m : ℝ) : (embed M e).post m 1 .N = M.post m .N :=
  post_embed M e m .N
@[simp] lemma postZ_embed (M : Model) (e m : ℝ) : (embed M e).post m 1 .Z = M.post m .Z :=
  post_embed M e m .Z

lemma vis_embed (M : Model) (e : ℝ) (i : Resp) : (embed M e).vis (rs i) = keep e i := by
  cases i <;> simp [ReviewBlackmail.SemiDec.Model.vis, embed, rs, keep]

lemma pay_embed (M : Model) (e r : ℝ) (i j : Resp) :
    (embed M e).pay (rs i) (rs j) r = M.pay e i j r := by
  cases i <;> cases j <;> simp [rs, ReviewBlackmail.SemiDec.Model.pay,
    ReviewBlackmail.SemiDec.Model.vis, Model.pay, keep] <;> ring

lemma eq_embed (M : Model) (e r : ℝ) (i : Resp) :
    M.IsEq e i r ↔ (embed M e).IsEq (rs i) r := by
  constructor
  · intro h j
    cases j with
    | s => simpa only [← pay_embed, rs] using h .s
    | n => simpa only [← pay_embed, rs] using h .n
    | d => simpa only [← pay_embed, rs] using h .c
  · intro h j
    simpa only [pay_embed] using h (rs j)

lemma prevails_embed (M : Model) (e r : ℝ) :
    M.SettlePrevails e r ↔ (embed M e).SettlePrevails r := by
  constructor
  · rintro ⟨hs,hmax⟩
    refine ⟨(eq_embed M e r .s).mp hs, ?_⟩
    intro i hi
    cases i with
    | s => exact le_rfl
    | n => simpa only [← pay_embed, rs] using hmax .n ((eq_embed M e r .n).mpr hi)
    | d => simpa only [← pay_embed, rs] using hmax .c ((eq_embed M e r .c).mpr hi)
  · rintro ⟨hs,hmax⟩
    refine ⟨(eq_embed M e r .s).mpr hs, ?_⟩
    intro i hi
    have h := hmax (rs i) ((eq_embed M e r i).mp hi)
    change (embed M e).pay (rs i) (rs i) r ≤ (embed M e).pay (rs .s) (rs .s) r at h
    simpa only [pay_embed] using h

lemma keep_bounds {e : ℝ} (he : e ∈ Set.Icc (0:ℝ) 1) (i : Resp) : keep e i ∈ Set.Icc (0:ℝ) 1 := by
  cases i <;> simp only [keep, Set.mem_Icc]
  · norm_num
  · norm_num
  · constructor <;> linarith [he.1,he.2]

lemma post_bounds (M : Model) (hM : M.Standing) (m : ℝ) (hm : 0 ≤ m) :
    0 < M.post m .N ∧ M.post m .N < M.a := by
  simpa using BlackmailProof.postN_bounds (embed M 0) (embed_standing M hM (by norm_num)) m hm

lemma post_strict (M : Model) (hM : M.Standing) {x y : ℝ} (hx : 0≤x) (hxy : x<y) :
    M.post x .N < M.post y .N := by
  simpa using BlackmailProof.postN_strict (embed M 0) (embed_standing M hM (by norm_num)) hx hxy

lemma post_mono (M : Model) (hM : M.Standing) {x y : ℝ} (hx : 0≤x) (hxy : x≤y) :
    M.post x .N ≤ M.post y .N := by
  simpa using BlackmailProof.postN_mono (embed M 0) (embed_standing M hM (by norm_num)) hx hxy

lemma central_order (M : Model) (hM : M.Standing) (γ δ : ℝ) (hγ : γ ∈ Set.Icc (0 : ℝ) 1)
    (hδ : δ ∈ Set.Icc (0 : ℝ) 1) (hpos : 0 < γ * δ) (hlt : γ * δ < 1) :
    M.post (keep (γ * δ) .s) .N < M.post (keep (γ * δ) .c) .N ∧
      M.post (keep (γ * δ) .c) .N < M.post (keep (γ * δ) .n) .N := by
  simp only [keep]
  exact ⟨post_strict M hM (le_refl 0) (sub_pos.mpr hlt),
    post_strict M hM (sub_nonneg.mpr hlt.le) (by linarith)⟩

lemma mul_bounds (γ δ : ℝ) (hγ : γ ∈ Set.Icc (0:ℝ) 1) (hδ : δ ∈ Set.Icc (0:ℝ) 1) :
    γ*δ ∈ Set.Icc (0:ℝ) 1 :=
  ⟨mul_nonneg hγ.1 hδ.1, mul_le_one₀ hγ.2 hδ.1 hδ.2⟩

lemma central_lemma2 (M : Model) (hM : M.Standing) (γ δ : ℝ) (hγ : γ ∈ Set.Icc (0 : ℝ) 1)
    (hδ : δ ∈ Set.Icc (0 : ℝ) 1) :
    (∀ i : Resp, M.post (keep (γ * δ) i) .P = 1 ∧ M.post (keep (γ * δ) i) .Z = M.a ∧
      M.post (keep (γ * δ) i) .N ∈ Set.Icc 0 M.a) ∧
    M.post (keep (γ * δ) .n) .N =
      M.a / (M.a + (1 - M.a) * ((M.β + (1 - M.β) * (1 - M.p / (M.a * M.θ))) /
        (M.β + (1 - M.β) * (1 - M.p / (M.a * M.θ)) * (1 - M.θ)))) ∧
    M.post (keep (γ * δ) .c) .N =
      M.a / (M.a + (1 - M.a) * ((M.β * (1 - γ * δ) + (1 - M.β) * (1 - M.p / (M.a * M.θ))) /
        (M.β * (1 - γ * δ) + (1 - M.β) * (1 - M.p / (M.a * M.θ)) * (1 - M.θ)))) ∧
    M.post (keep (γ * δ) .s) .N = M.a / (M.a + (1 - M.a) * (1 / (1 - M.θ))) := by
  have hE := embed_standing M hM (mul_bounds γ δ hγ hδ)
  have hr := BlackmailProof.buy_bounds (embed M (γ*δ)) hE
  have hp : 0 < M.a*((1-M.β)*M.buyProb*M.θ) :=
    mul_pos hM.1 (mul_pos (mul_pos (sub_pos.mpr hM.2.2.2.2.2.1) hr.1) hM.2.2.1)
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro i
    have hm := keep_bounds (mul_bounds γ δ hγ hδ) i
    have hb := post_bounds M hM _ hm.1
    refine ⟨?_, ?_, hb.1.le,hb.2.le⟩
    · simp only [Model.post, Model.lik, mul_zero, add_zero]
      exact div_self hp.ne'
    · simpa using BlackmailProof.postZ (embed M (γ*δ)) hE _ hm
  · simpa [keep,ReviewBlackmail.SemiDec.Model.buyProb] using
      BlackmailProof.postN_form (embed M (γ*δ)) hE 1 (by norm_num)
  · simpa [keep,ReviewBlackmail.SemiDec.Model.buyProb] using
      BlackmailProof.postN_form (embed M (γ*δ)) hE (1-γ*δ) (sub_nonneg.mpr (mul_bounds γ δ hγ hδ).2)
  · simpa [keep] using BlackmailProof.zeroN (embed M (γ*δ)) hE

lemma eq_s (M : Model) (hM : M.Standing) {e : ℝ} (he : e ∈ Set.Icc (0:ℝ) 1) (r : ℝ) :
    M.IsEq e .s r ↔ r ≤ M.π M.a-M.π (M.post 0 .N) ∧
      r ≤ (1-e)*(M.π M.a-M.π (M.post 0 .N))+M.c := by
  rw [eq_embed]
  simpa [rs] using BlackmailProof.eq_s (embed M e) (embed_standing M hM he) r

lemma eq_n (M : Model) (hM : M.Standing) {e : ℝ} (he : e ∈ Set.Icc (0:ℝ) 1) (r : ℝ) :
    M.IsEq e .n r ↔ M.π M.a-M.π (M.post 1 .N) ≤ r ∧
      e*(M.π M.a-M.π (M.post 1 .N)) ≤ M.c := by
  rw [eq_embed]
  simpa [rs] using BlackmailProof.eq_n_mul (embed M e) (embed_standing M hM he) r

lemma eq_c (M : Model) (hM : M.Standing) {e : ℝ} (he : e ∈ Set.Icc (0:ℝ) 1) (r : ℝ) :
    M.IsEq e .c r ↔ M.c ≤ e*(M.π M.a-M.π (M.post (1-e) .N)) ∧
      (1-e)*(M.π M.a-M.π (M.post (1-e) .N))+M.c ≤ r := by
  rw [eq_embed]
  simpa [rs] using BlackmailProof.eq_d_mul (embed M e) (embed_standing M hM he) r

lemma central_prop11 (M : Model) (hM : M.Standing) (γ δ : ℝ) (hγ : γ ∈ Set.Icc (0 : ℝ) 1)
    (hδ : δ ∈ Set.Icc (0 : ℝ) 1) (hpos : 0 < γ * δ) (hlt : γ * δ < 1) (r : ℝ) :
    M.IsEq (γ * δ) .n r ↔
      max (M.π M.a - r) (M.π M.a - M.c / (γ * δ)) ≤ M.π (M.post (keep (γ * δ) .n) .N) := by
  rw [eq_n M hM (mul_bounds γ δ hγ hδ), max_le_iff]
  simp only [keep]
  constructor
  · rintro ⟨h1,h2⟩
    have hd : M.π M.a-M.π (M.post 1 .N) ≤ M.c/(γ*δ) :=
      (le_div_iff₀ hpos).mpr (by nlinarith only [h2])
    constructor <;> linarith
  · rintro ⟨h1,h2⟩
    have hd : M.π M.a-M.π (M.post 1 .N) ≤ M.c/(γ*δ) := by linarith
    have hm := (le_div_iff₀ hpos).mp hd
    constructor <;> nlinarith

lemma central_prop12 (M : Model) (hM : M.Standing) (γ δ : ℝ) (hγ : γ ∈ Set.Icc (0 : ℝ) 1)
    (hδ : δ ∈ Set.Icc (0 : ℝ) 1) (hpos : 0 < γ * δ) (hlt : γ * δ < 1) (r : ℝ) :
    M.IsEq (γ * δ) .s r ↔
      M.π (M.post (keep (γ * δ) .s) .N) ≤
        min (M.π M.a - r) (M.π M.a + (M.c - r) / (1 - γ * δ)) := by
  rw [eq_s M hM (mul_bounds γ δ hγ hδ), le_min_iff]
  simp only [keep]
  constructor
  · rintro ⟨h1,h2⟩
    have hd : M.π (M.post 0 .N)-M.π M.a ≤ (M.c-r)/(1-γ*δ) :=
      (le_div_iff₀ (sub_pos.mpr hlt)).mpr (by nlinarith only [h2])
    constructor <;> linarith
  · rintro ⟨h1,h2⟩
    have hd : M.π (M.post 0 .N)-M.π M.a ≤ (M.c-r)/(1-γ*δ) := by linarith
    have hm := (le_div_iff₀ (sub_pos.mpr hlt)).mp hd
    constructor <;> nlinarith

lemma central_prop13 (M : Model) (hM : M.Standing) (γ δ : ℝ) (hγ : γ ∈ Set.Icc (0 : ℝ) 1)
    (hδ : δ ∈ Set.Icc (0 : ℝ) 1) (hpos : 0 < γ * δ) (hlt : γ * δ < 1) (r : ℝ) :
    M.IsEq (γ * δ) .c r ↔
      M.π M.a + (M.c - r) / (1 - γ * δ) ≤ M.π (M.post (keep (γ * δ) .c) .N) ∧
        M.π (M.post (keep (γ * δ) .c) .N) ≤ M.π M.a - M.c / (γ * δ) := by
  rw [eq_c M hM (mul_bounds γ δ hγ hδ)]
  simp only [keep]
  constructor
  · rintro ⟨h1,h2⟩
    have hd : (M.c-r)/(1-γ*δ) ≤ M.π (M.post (1-γ*δ) .N)-M.π M.a :=
      (div_le_iff₀ (sub_pos.mpr hlt)).mpr (by nlinarith only [h2])
    have hc' : M.c/(γ*δ) ≤ M.π M.a-M.π (M.post (1-γ*δ) .N) :=
      (div_le_iff₀ hpos).mpr (by nlinarith only [h1])
    constructor <;> linarith
  · rintro ⟨h1,h2⟩
    have hd : (M.c-r)/(1-γ*δ) ≤ M.π (M.post (1-γ*δ) .N)-M.π M.a := by linarith
    have hc' : M.c/(γ*δ) ≤ M.π M.a-M.π (M.post (1-γ*δ) .N) := by linarith
    have hm := (div_le_iff₀ (sub_pos.mpr hlt)).mp hd
    have hn := (div_le_iff₀ hpos).mp hc'
    constructor <;> nlinarith

lemma prevail_iff (M : Model) (hM : M.Standing) {e : ℝ} (he : e ∈ Set.Icc (0:ℝ) 1) (r : ℝ) :
    M.SettlePrevails e r ↔ BlackmailGame.prevails
      (M.π M.a-M.π (M.post 0 .N)) (M.π M.a-M.π (M.post 1 .N))
      (M.π M.a-M.π (M.post (1-e) .N)) (1-e) M.c r := by
  rw [prevails_embed]
  simpa using BlackmailProof.prevail_iff (embed M e) (embed_standing M hM he) r

lemma gap_order (M : Model) (hM : M.Standing) {e : ℝ} (he : e ∈ Set.Icc (0:ℝ) 1) :
    M.π M.a-M.π (M.post 1 .N) ≤ M.π M.a-M.π (M.post (1-e) .N) ∧
    M.π M.a-M.π (M.post (1-e) .N) ≤ M.π M.a-M.π (M.post 0 .N) := by
  simpa using BlackmailProof.gap_order (embed M e) (embed_standing M hM he)

lemma greatest_high (M : Model) (hM : M.Standing) {e : ℝ} (he : e ∈ Set.Icc (0:ℝ) 1)
    (hc : e*(M.π M.a-M.π (M.post 1 .N)) ≤ M.c) :
    IsGreatest {r | M.SettlePrevails e r} (M.π M.a-M.π (M.post 1 .N)) := by
  have ho := gap_order M hM he
  have h := BlackmailGame.greatest_high _ _ _ (1-e) M.c ho.1 ho.2
    (sub_nonneg.mpr he.2) (by linarith [he.1]) (by simpa using hc)
  simpa only [← prevail_iff M hM he] using h

lemma greatest_low (M : Model) (hM : M.Standing) {e : ℝ} (he : e ∈ Set.Icc (0:ℝ) 1)
    (hc : M.c < e*(M.π M.a-M.π (M.post 1 .N))) :
    IsGreatest {r | M.SettlePrevails e r} ((1-e)*(M.π M.a-M.π (M.post (1-e) .N))+M.c) := by
  have ho := gap_order M hM he
  have h := BlackmailGame.greatest_low _ _ _ (1-e) M.c ho.1 ho.2
    (sub_nonneg.mpr he.2) (by linarith [he.1]) (by simpa using hc)
  simpa only [← prevail_iff M hM he] using h

lemma central_prop21 (M : Model) (hM : M.Standing) (γ δ : ℝ) (hγ : γ ∈ Set.Icc (0 : ℝ) 1)
    (hδ : δ ∈ Set.Icc (0 : ℝ) 1)
    (hcase : γ * δ * (M.π M.a - M.π (M.post (keep (γ * δ) .n) .N)) ≤ M.c) :
    IsGreatest {r : ℝ | M.SettlePrevails (γ * δ) r}
        (M.π M.a - M.π (M.post (keep (γ * δ) .n) .N)) ∧
      (M.Purchases (γ * δ) ↔ M.p < M.π M.a - M.π (M.post (keep (γ * δ) .n) .N)) := by
  have h := greatest_high M hM (mul_bounds γ δ hγ hδ) hcase
  exact ⟨h, BlackmailGame.purchase_iff h⟩

lemma central_prop22 (M : Model) (hM : M.Standing) (γ δ : ℝ) (hγ : γ ∈ Set.Icc (0 : ℝ) 1)
    (hδ : δ ∈ Set.Icc (0 : ℝ) 1)
    (hcase : M.c < γ * δ * (M.π M.a - M.π (M.post (keep (γ * δ) .n) .N))) :
    IsGreatest {r : ℝ | M.SettlePrevails (γ * δ) r}
        ((1 - γ * δ) * (M.π M.a - M.π (M.post (keep (γ * δ) .c) .N)) + M.c) ∧
      (M.Purchases (γ * δ) ↔
        M.p < (1 - γ * δ) * (M.π M.a - M.π (M.post (keep (γ * δ) .c) .N)) + M.c) := by
  have h := greatest_low M hM (mul_bounds γ δ hγ hδ) hcase
  exact ⟨h, BlackmailGame.purchase_iff h⟩

lemma gap_strict (M : Model) (hM : M.Standing) {e : ℝ} (he : 0<e) (he1 : e≤1) :
    M.π M.a-M.π (M.post 1 .N) < M.π M.a-M.π (M.post (1-e) .N) := by
  have h0 := post_bounds M hM (1-e) (sub_nonneg.mpr he1)
  have h1 := post_bounds M hM 1 (by norm_num)
  have hx := post_strict M hM (sub_nonneg.mpr he1) (show 1-e<1 by linarith)
  have hf := hM.2.2.2.2.2.2.2.2.1
    ⟨h0.1.le,h0.2.le.trans hM.2.1.le⟩ ⟨h1.1.le,h1.2.le.trans hM.2.1.le⟩ hx
  linarith

lemma gap_mono (M : Model) (hM : M.Standing) {e f : ℝ} (hef : e≤f) (hf : f≤1) :
    M.π M.a-M.π (M.post (1-e) .N) ≤ M.π M.a-M.π (M.post (1-f) .N) := by
  have h0 := post_bounds M hM (1-f) (sub_nonneg.mpr hf)
  have h1 := post_bounds M hM (1-e) (by linarith)
  have hx := post_mono M hM (sub_nonneg.mpr hf) (show 1-f≤1-e by linarith)
  have hπ := hM.2.2.2.2.2.2.2.2.1.monotoneOn
    ⟨h0.1.le,h0.2.le.trans hM.2.1.le⟩ ⟨h1.1.le,h1.2.le.trans hM.2.1.le⟩ hx
  linarith

lemma central_corollary (M : Model) (hM : M.Standing) (hc : 0 < M.c)
    (hp : M.p < M.π M.a - M.π (M.post 1 .N) - M.c) :
    ∃ e₁ e₂ r₁ r₂ : ℝ, 0 ≤ e₁ ∧ e₁ < e₂ ∧ e₂ ≤ 1 ∧
      M.p < (1 - e₁) * (M.π M.a - M.π (M.post 1 .N)) ∧
      M.p < (1 - e₂) * (M.π M.a - M.π (M.post 1 .N)) ∧
      IsGreatest {r : ℝ | M.SettlePrevails e₁ r} r₁ ∧
      IsGreatest {r : ℝ | M.SettlePrevails e₂ r} r₂ ∧
      r₁ < r₂ := by
  let N := M.π M.a-M.π (M.post 1 .N)
  let e₀ := M.c/N
  have hp0 : 0<M.p := hM.2.2.2.2.2.2.2.2.2.2.1
  have hNc : M.c<N := by dsimp [N]; linarith
  have hN : 0<N := hc.trans hNc
  have he0 : 0<e₀ := div_pos hc hN
  have he1 : e₀<1 := (div_lt_one hN).mpr hNc
  have heN : e₀*N=M.c := div_mul_cancel₀ M.c hN.ne'
  let D := M.π M.a-M.π (M.post (1-e₀) .N)
  have hND : N<D := gap_strict M hM he0 he1.le
  have hD : 0<D := hN.trans hND
  have hpdiv : M.p/N<1-e₀ := (div_lt_iff₀ hN).mpr (by dsimp [N] at *; nlinarith only [hp,heN])
  have hDdiv : (N-M.c)/D<1-e₀ := (div_lt_iff₀ hD).mpr (by
    have hx := mul_pos (sub_pos.mpr he1) (sub_pos.mpr hND)
    nlinarith only [hx,heN])
  have hub : e₀ < min 1 (min (1-M.p/N) (1-(N-M.c)/D)) := by
    exact lt_min he1 (lt_min (by linarith only [hpdiv]) (by linarith only [hDdiv]))
  obtain ⟨e₂,he₂0,he₂ub⟩ := exists_between hub
  have he₂1 : e₂<1 := he₂ub.trans_le (min_le_left _ _)
  have he₂p : e₂<1-M.p/N := he₂ub.trans_le ((min_le_right _ _).trans (min_le_left _ _))
  have he₂D : e₂<1-(N-M.c)/D := he₂ub.trans_le ((min_le_right _ _).trans (min_le_right _ _))
  have he₂ : 0≤e₂ := he0.le.trans he₂0.le
  have hprice1 : M.p<(1-e₀)*N := by dsimp [N] at *; nlinarith only [hp,heN]
  have hprice2 : M.p<(1-e₂)*N := (div_lt_iff₀ hN).mp (by linarith only [he₂p])
  have hcase2 : M.c<e₂*N := by nlinarith only [mul_pos (sub_pos.mpr he₂0) hN,heN]
  have hgreat1 := greatest_high M hM ⟨he0.le,he1.le⟩ heN.le
  have hgreat2 := greatest_low M hM ⟨he₂,he₂1.le⟩ hcase2
  have hDD := gap_mono M hM he₂0.le he₂1.le
  have hbound : N-M.c<(1-e₂)*D := (div_lt_iff₀ hD).mp (by linarith only [he₂D])
  have hmul := mul_le_mul_of_nonneg_left hDD (sub_nonneg.mpr he₂1.le)
  refine ⟨e₀,e₂,N,(1-e₂)*(M.π M.a-M.π (M.post (1-e₂) .N))+M.c,
    he0.le,he₂0,he₂1.le,hprice1,hprice2,hgreat1,hgreat2,?_⟩
  dsimp [D] at hbound
  linarith only [hbound,hmul]

end CentralProof

end

open ReviewBlackmail.Central


theorem solution (M : Model) (hM : M.Standing) (γ δ : ℝ) (hγ : γ ∈ Set.Icc (0 : ℝ) 1)
    (hδ : δ ∈ Set.Icc (0 : ℝ) 1) (hpos : 0 < γ * δ) (hlt : γ * δ < 1) (r : ℝ) :
    M.IsEq (γ * δ) .c r ↔
      M.π M.a + (M.c - r) / (1 - γ * δ) ≤ M.π (M.post (keep (γ * δ) .c) .N) ∧
        M.π (M.post (keep (γ * δ) .c) .N) ≤ M.π M.a - M.c / (γ * δ) := by
  exact CentralProof.central_prop13 M hM γ δ hγ hδ hpos hlt r

