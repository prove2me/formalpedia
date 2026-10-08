-- Prove2me | solution 1 for StrategicQR.Game.qr_value_ge_myopic
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-08T00:44:22.716194+00:00
-- url     : https://prove2.me/submissions/7a704bfb-a285-46cb-a331-9e48a27c6966

import Mathlib
import Definitions.Def_StrategicQR_Game_Equilibrium

set_option autoImplicit false

namespace StrategicQR.Game.QV3e18

open MeasureTheory StrategicQR.Game

lemma vB_lt_vlo (M : Model) : M.vB < M.vlo := by
  have := M.vlo_ge; have := M.p_lt_vM; have := M.vB_pos; linarith

lemma w_pos (M : Model) : 0 < M.vhi - M.vlo := by have := M.vlo_lt_vhi; linarith

lemma vhi_pos (M : Model) : 0 < M.vhi := by
  have := vB_lt_vlo M; have := M.vB_pos; have := M.vlo_lt_vhi; linarith

lemma vB_lt_p (M : Model) : M.vB < M.p := by
  have := vB_lt_vlo M; have := M.vlo_lt_vhi; have := M.vhi_le_p; linarith

lemma Gbar_nonneg (M : Model) (s : ℝ) : 0 ≤ Gbar M s := by
  unfold Gbar; exact le_min zero_le_one (le_max_left _ _)

lemma Gbar_le_one (M : Model) (s : ℝ) : Gbar M s ≤ 1 := by
  unfold Gbar; exact min_le_left _ _

lemma Gbar_eq_zero (M : Model) {s : ℝ} (hs : M.vhi ≤ s) : Gbar M s = 0 := by
  unfold Gbar
  have : (M.vhi - s) / (M.vhi - M.vlo) ≤ 0 :=
    div_nonpos_of_nonpos_of_nonneg (by linarith) (w_pos M).le
  rw [max_eq_left this, min_eq_right zero_le_one]

lemma Gbar_anti (M : Model) {s t : ℝ} (h : s ≤ t) : Gbar M t ≤ Gbar M s := by
  unfold Gbar
  apply min_le_min_left
  apply max_le_max_left
  exact div_le_div_of_nonneg_right (by linarith) (w_pos M).le

lemma Gbar_mid (M : Model) {s : ℝ} (h1 : M.vlo ≤ s) (h2 : s ≤ M.vhi) :
    Gbar M s = (M.vhi - s) / (M.vhi - M.vlo) := by
  unfold Gbar
  have hw := w_pos M
  have h0 : 0 ≤ (M.vhi - s) / (M.vhi - M.vlo) := div_nonneg (by linarith) hw.le
  have h1' : (M.vhi - s) / (M.vhi - M.vlo) ≤ 1 := by rw [div_le_one hw]; linarith
  rw [max_eq_right h0, min_eq_right h1']

lemma sGbar_le_sm (M : Model) {v s : ℝ} (hv1 : M.vlo ≤ v) (hv2 : v ≤ M.vhi) (hs : v ≤ s) :
    s * Gbar M s ≤ sm M v * Gbar M (sm M v) := by
  have hw := w_pos M
  have hvhi := vhi_pos M
  have hsm1 : v ≤ sm M v := le_max_right _ _
  have hsm2 : sm M v ≤ M.vhi := max_le (by linarith) hv2
  have hv0 : 0 < v := by linarith [vB_lt_vlo M, M.vB_pos]
  rw [Gbar_mid M (by linarith) hsm2]
  rcases le_or_gt M.vhi s with h | h
  · rw [Gbar_eq_zero M h, mul_zero]
    exact mul_nonneg (by linarith) (div_nonneg (by linarith) hw.le)
  · rw [Gbar_mid M (by linarith) h.le, mul_div_assoc', mul_div_assoc']
    apply div_le_div_of_nonneg_right _ hw.le
    unfold sm
    rcases le_total v (M.vhi / 2) with h' | h'
    · rw [max_eq_left h']; nlinarith [sq_nonneg (s - M.vhi / 2)]
    · rw [max_eq_right h']; nlinarith

lemma xi_nonneg (M : Model) {α v : ℝ} (hα0 : 0 ≤ α) (hα1 : α ≤ 1) : 0 ≤ xi M α v := by
  unfold xi; nlinarith [Gbar_nonneg M v, Gbar_le_one M v]

lemma xi_le_one (M : Model) {α v : ℝ} (hα0 : 0 ≤ α) : xi M α v ≤ 1 := by
  unfold xi; nlinarith [Gbar_nonneg M v]

lemma xi_zero (M : Model) (v : ℝ) : xi M 0 v = 1 := by simp [xi]

lemma xi_vhi (M : Model) (α : ℝ) : xi M α M.vhi = 1 := by
  simp [xi, Gbar_eq_zero M le_rfl]

/-! ### Quick-response sale revenue -/

lemma qrSale_le_bound (M : Model) {α c₂ D vhat s I q₂ : ℝ} (hα0 : 0 ≤ α) (hc₂ : M.vB ≤ c₂)
    (hs0 : 0 ≤ s) (hsp : s ≤ M.p) (hq₂ : 0 ≤ q₂) :
    qrSaleRevenue M α c₂ D vhat s I q₂ ≤ M.p * (α * |D| + |I|) := by
  have hc₂0 : 0 ≤ c₂ := le_trans M.vB_pos.le hc₂
  have hp0 : 0 ≤ M.p := hs0.trans hsp
  have key : ∀ g : ℝ, 0 ≤ g → g ≤ 1 → ∀ J : ℝ,
      s * min (g * α * D) J - c₂ * q₂ ≤ M.p * (α * |D| + |I|) := by
    intro g hg0 hg1 J
    have h1 : min (g * α * D) J ≤ α * |D| := by
      refine (min_le_left _ _).trans ((le_abs_self _).trans ?_)
      rw [abs_mul, abs_mul, abs_of_nonneg hg0, abs_of_nonneg hα0]
      nlinarith [abs_nonneg D, mul_nonneg hα0 (abs_nonneg D)]
    have h2 : s * min (g * α * D) J ≤ s * (α * |D|) := mul_le_mul_of_nonneg_left h1 hs0
    have h3 : s * (α * |D|) ≤ M.p * (α * |D|) :=
      mul_le_mul_of_nonneg_right hsp (mul_nonneg hα0 (abs_nonneg D))
    nlinarith [mul_nonneg hc₂0 hq₂, mul_nonneg hp0 (abs_nonneg I)]
  unfold qrSaleRevenue
  split_ifs with h1 h2
  · exact key _ (Gbar_nonneg M s) (Gbar_le_one M s) _
  · exact key _ (Gbar_nonneg M vhat) (Gbar_le_one M vhat) _
  · have hsv : s ≤ M.vB := not_lt.mp h2
    have e1 : s * I ≤ M.p * |I| :=
      (mul_le_mul_of_nonneg_left (le_abs_self I) hs0).trans
        (mul_le_mul_of_nonneg_right hsp (abs_nonneg I))
    have e2 : (s - c₂) * q₂ ≤ 0 := mul_nonpos_of_nonpos_of_nonneg (by linarith) hq₂
    nlinarith [mul_nonneg hp0 (mul_nonneg hα0 (abs_nonneg D))]

lemma qrDom_nonempty (M : Model) : (Set.Icc 0 M.p ×ˢ Set.Ici (0 : ℝ)).Nonempty :=
  ⟨(0, 0), ⟨⟨le_rfl, (M.vB_pos.trans (vB_lt_p M)).le⟩, by simp⟩⟩

lemma qrBdd (M : Model) {α c₂ D vhat I : ℝ} (hα0 : 0 ≤ α) (hc₂ : M.vB ≤ c₂) :
    BddAbove ((fun z : ℝ × ℝ => qrSaleRevenue M α c₂ D vhat z.1 I z.2) ''
      (Set.Icc 0 M.p ×ˢ Set.Ici 0)) := by
  refine ⟨M.p * (α * |D| + |I|), ?_⟩
  rintro _ ⟨z, ⟨⟨hs0, hsp⟩, hq₂⟩, rfl⟩
  exact qrSale_le_bound M hα0 hc₂ hs0 hsp hq₂

lemma qrOpt_le_bound (M : Model) {α c₂ D vhat I : ℝ} (hα0 : 0 ≤ α) (hc₂ : M.vB ≤ c₂) :
    qrOptSaleRevenue M α c₂ D vhat I ≤ M.p * (α * |D| + |I|) := by
  apply csSup_le ((qrDom_nonempty M).image _)
  rintro _ ⟨z, ⟨⟨hs0, hsp⟩, hq₂⟩, rfl⟩
  exact qrSale_le_bound M hα0 hc₂ hs0 hsp hq₂

lemma qrOpt_ge (M : Model) {α c₂ D vhat I : ℝ} (hα0 : 0 ≤ α) (hc₂ : M.vB ≤ c₂)
    (hv : M.vB < vhat) : M.vB * I ≤ qrOptSaleRevenue M α c₂ D vhat I := by
  have hmem : (M.vB, (0 : ℝ)) ∈ Set.Icc 0 M.p ×ˢ Set.Ici (0 : ℝ) :=
    ⟨⟨M.vB_pos.le, (vB_lt_p M).le⟩, by simp⟩
  have := le_csSup (qrBdd M (D := D) (vhat := vhat) (I := I) hα0 hc₂) ⟨_, hmem, rfl⟩
  refine le_trans (le_of_eq ?_) this
  simp only [qrSaleRevenue]
  rw [if_neg (by linarith), if_neg (lt_irrefl _)]
  ring

lemma qrOpt_shift (M : Model) {α c₂ D vhat I d : ℝ} (hα0 : 0 ≤ α) (hc₂ : M.vB ≤ c₂)
    (hd : 0 ≤ d) :
    qrOptSaleRevenue M α c₂ D vhat (I + d) ≤ qrOptSaleRevenue M α c₂ D vhat I + c₂ * d := by
  apply csSup_le ((qrDom_nonempty M).image _)
  rintro _ ⟨z, ⟨hs, hq₂⟩, rfl⟩
  have hmem : (z.1, z.2 + d) ∈ Set.Icc 0 M.p ×ˢ Set.Ici (0 : ℝ) :=
    ⟨hs, by simp only [Set.mem_Ici] at hq₂ ⊢; linarith⟩
  have h := le_csSup (qrBdd M (D := D) (vhat := vhat) (I := I) hα0 hc₂) ⟨_, hmem, rfl⟩
  have e : qrSaleRevenue M α c₂ D vhat z.1 (I + d) z.2 =
      qrSaleRevenue M α c₂ D vhat z.1 I (z.2 + d) + c₂ * d := by
    simp only [qrSaleRevenue]
    split_ifs <;> (rw [show I + d + z.2 = I + (z.2 + d) by ring]; ring)
  simp only at h ⊢
  unfold qrOptSaleRevenue
  linarith

/-- In the low-demand region the optimal quick-response sale revenue is the salvage value. -/
lemma qrOpt_le_low (M : Model) {α c₂ x v I : ℝ} (hα0 : 0 ≤ α) (hc₂ : M.vB ≤ c₂)
    (hv1 : M.vlo ≤ v) (hv2 : v ≤ M.vhi) (hx : 0 ≤ x) (hI : 0 ≤ I)
    (hlow : sm M v * Gbar M (sm M v) * α * x ≤ M.vB * I) :
    qrOptSaleRevenue M α c₂ x v I ≤ M.vB * I := by
  have hc₂0 : 0 ≤ c₂ := le_trans M.vB_pos.le hc₂
  have hαx : 0 ≤ α * x := mul_nonneg hα0 hx
  apply csSup_le ((qrDom_nonempty M).image _)
  rintro _ ⟨z, ⟨⟨hs0, hsp⟩, hq₂⟩, rfl⟩
  simp only [Set.mem_Ici] at hq₂
  simp only [qrSaleRevenue]
  have hcq : 0 ≤ c₂ * z.2 := mul_nonneg hc₂0 hq₂
  split_ifs with h1 h2
  · have hm : z.1 * min (Gbar M z.1 * α * x) (I + z.2) ≤ z.1 * (Gbar M z.1 * α * x) :=
      mul_le_mul_of_nonneg_left (min_le_left _ _) hs0
    have hk := sGbar_le_sm M hv1 hv2 h1
    have : z.1 * (Gbar M z.1 * α * x) ≤ sm M v * Gbar M (sm M v) * α * x := by
      have := mul_le_mul_of_nonneg_right hk hαx
      linarith [show z.1 * (Gbar M z.1 * α * x) = z.1 * Gbar M z.1 * (α * x) by ring,
        show sm M v * Gbar M (sm M v) * α * x = sm M v * Gbar M (sm M v) * (α * x) by ring]
    linarith
  · have hm : z.1 * min (Gbar M v * α * x) (I + z.2) ≤ z.1 * (Gbar M v * α * x) :=
      mul_le_mul_of_nonneg_left (min_le_left _ _) hs0
    have hk := sGbar_le_sm M hv1 hv2 (le_refl v)
    have hG : 0 ≤ Gbar M v * α * x := by
      have := Gbar_nonneg M v; nlinarith
    have h3 : z.1 * (Gbar M v * α * x) ≤ v * (Gbar M v * α * x) :=
      mul_le_mul_of_nonneg_right (not_le.mp h1).le hG
    have : v * (Gbar M v * α * x) ≤ sm M v * Gbar M (sm M v) * α * x := by
      have := mul_le_mul_of_nonneg_right hk hαx
      linarith [show v * (Gbar M v * α * x) = v * Gbar M v * (α * x) by ring,
        show sm M v * Gbar M (sm M v) * α * x = sm M v * Gbar M (sm M v) * (α * x) by ring]
    linarith
  · have hsv : z.1 ≤ M.vB := not_lt.mp h2
    have e1 : z.1 * I ≤ M.vB * I := mul_le_mul_of_nonneg_right hsv hI
    have e2 : (z.1 - c₂) * z.2 ≤ 0 := mul_nonpos_of_nonpos_of_nonneg (by linarith) hq₂
    nlinarith

/-! ### Continuity in the demand realization -/

lemma qrSale_lip (M : Model) {α c₂ v ξ t s q₂ : ℝ} (hα0 : 0 ≤ α) (hξ0 : 0 ≤ ξ) (hξ1 : ξ ≤ 1)
    (hs0 : 0 ≤ s) (hsp : s ≤ M.p) (x y : ℝ) :
    qrSaleRevenue M α c₂ x v s (max (t - ξ * x) 0) q₂ ≤
      qrSaleRevenue M α c₂ y v s (max (t - ξ * y) 0) q₂ + M.p * (α + 1) * |x - y| := by
  have hxy := abs_nonneg (x - y)
  have hI : |max (t - ξ * x) 0 - max (t - ξ * y) 0| ≤ |x - y| := by
    refine (abs_max_sub_max_le_abs _ _ _).trans ?_
    rw [show t - ξ * x - (t - ξ * y) = ξ * (y - x) by ring, abs_mul, abs_of_nonneg hξ0,
      abs_sub_comm]
    nlinarith
  have hsm : ∀ a b : ℝ, |a - b| ≤ (α + 1) * |x - y| →
      s * a ≤ s * b + M.p * (α + 1) * |x - y| := by
    intro a b hd
    have h1 : s * (a - b) ≤ s * |a - b| := mul_le_mul_of_nonneg_left (le_abs_self _) hs0
    have h2 : s * |a - b| ≤ s * ((α + 1) * |x - y|) := mul_le_mul_of_nonneg_left hd hs0
    have h3 : s * ((α + 1) * |x - y|) ≤ M.p * ((α + 1) * |x - y|) :=
      mul_le_mul_of_nonneg_right hsp (mul_nonneg (by linarith) hxy)
    linarith [mul_sub s a b, mul_assoc M.p (α + 1) |x - y|]
  have key : ∀ g : ℝ, 0 ≤ g → g ≤ 1 →
      |min (g * α * x) (max (t - ξ * x) 0 + q₂) - min (g * α * y) (max (t - ξ * y) 0 + q₂)|
        ≤ (α + 1) * |x - y| := by
    intro g hg0 hg1
    refine (abs_min_sub_min_le_max _ _ _ _).trans (max_le ?_ ?_)
    · rw [show g * α * x - g * α * y = (g * α) * (x - y) by ring, abs_mul,
        abs_of_nonneg (mul_nonneg hg0 hα0)]
      nlinarith [mul_le_mul_of_nonneg_right hg1 hα0]
    · rw [show max (t - ξ * x) 0 + q₂ - (max (t - ξ * y) 0 + q₂) =
          max (t - ξ * x) 0 - max (t - ξ * y) 0 by ring]
      nlinarith
  unfold qrSaleRevenue
  split_ifs
  · linarith [hsm _ _ (key _ (Gbar_nonneg M s) (Gbar_le_one M s))]
  · linarith [hsm _ _ (key _ (Gbar_nonneg M v) (Gbar_le_one M v))]
  · have : |(max (t - ξ * x) 0 + q₂) - (max (t - ξ * y) 0 + q₂)| ≤ (α + 1) * |x - y| := by
      rw [show max (t - ξ * x) 0 + q₂ - (max (t - ξ * y) 0 + q₂) =
          max (t - ξ * x) 0 - max (t - ξ * y) 0 by ring]
      nlinarith
    linarith [hsm _ _ this]

lemma sSup_image_le_add {ι : Type*} (S : Set ι) (hS : S.Nonempty) (h : ι → ℝ → ℝ) (L : ℝ)
    (hL : ∀ z ∈ S, ∀ x y, h z x ≤ h z y + L * |x - y|)
    (hB : ∀ x, BddAbove ((fun z => h z x) '' S)) (x y : ℝ) :
    sSup ((fun z => h z x) '' S) ≤ sSup ((fun z => h z y) '' S) + L * |x - y| := by
  apply csSup_le (hS.image _)
  rintro _ ⟨z, hz, rfl⟩
  have := le_csSup (hB y) ⟨z, hz, rfl⟩
  linarith [hL z hz x y]

lemma qrOpt_continuous (M : Model) {α c₂ v ξ t : ℝ} (hα0 : 0 ≤ α) (hc₂ : M.vB ≤ c₂)
    (hξ0 : 0 ≤ ξ) (hξ1 : ξ ≤ 1) :
    Continuous (fun x => qrOptSaleRevenue M α c₂ x v (max (t - ξ * x) 0)) := by
  have hlip : ∀ x y : ℝ, qrOptSaleRevenue M α c₂ x v (max (t - ξ * x) 0) ≤
      qrOptSaleRevenue M α c₂ y v (max (t - ξ * y) 0) + M.p * (α + 1) * dist x y := by
    intro x y
    rw [Real.dist_eq]
    exact sSup_image_le_add (Set.Icc 0 M.p ×ˢ Set.Ici 0) (qrDom_nonempty M)
      (fun z x => qrSaleRevenue M α c₂ x v z.1 (max (t - ξ * x) 0) z.2) _
      (fun z hz x y => qrSale_lip M hα0 hξ0 hξ1 hz.1.1 hz.1.2 x y)
      (fun x => qrBdd M hα0 hc₂) x y
  exact (LipschitzWith.of_le_add_mul' _ hlip).continuous

lemma integrable_of_bound (f g : ℝ → ℝ) (hf : IsDemandDensity f) (hg : Continuous g)
    (A B : ℝ) (hb : ∀ x, |g x| ≤ A + B * |x|) : Integrable (fun x => g x * f x) := by
  refine Integrable.mono' ((hf.integrable.const_mul A).add
    (hf.integrable_mul_id.norm.const_mul B))
    (hg.aestronglyMeasurable.mul hf.integrable.aestronglyMeasurable)
    (Filter.Eventually.of_forall fun x => ?_)
  have hf0 := hf.nonneg x
  simp only [Real.norm_eq_abs, abs_mul, abs_of_nonneg hf0]
  have := mul_le_mul_of_nonneg_right (hb x) hf0
  simp only [Pi.add_apply, abs_of_nonneg hf0]
  nlinarith

lemma qrIntegrable (M : Model) {α c₁ c₂ v t : ℝ} (hα0 : 0 ≤ α) (hα1 : α ≤ 1)
    (hc₂ : M.vB ≤ c₂) (hv : M.vB < v) :
    Integrable (fun x => (M.p * (xi M α v * x) - c₂ * max (xi M α v * x - t) 0 - c₁ * t +
      qrOptSaleRevenue M α c₂ x v (max (t - xi M α v * x) 0)) * M.f x) := by
  have hξ0 := xi_nonneg M (v := v) hα0 hα1
  have hξ1 := xi_le_one M (v := v) hα0
  set ξ := xi M α v
  have hc₂0 : 0 ≤ c₂ := le_trans M.vB_pos.le hc₂
  have hp0 : 0 ≤ M.p := (M.vB_pos.trans (vB_lt_p M)).le
  apply integrable_of_bound M.f _ M.density (by
    have := qrOpt_continuous M (v := v) (t := t) hα0 hc₂ hξ0 hξ1
    fun_prop) (c₂ * |t| + |c₁| * |t| + M.p * |t|) (3 * M.p + c₂)
  intro x
  have hξx : |ξ * x| ≤ |x| := by
    rw [abs_mul, abs_of_nonneg hξ0]; nlinarith [abs_nonneg x]
  have hm0 : 0 ≤ max (ξ * x - t) 0 := le_max_right _ _
  have hm1 : max (ξ * x - t) 0 ≤ |x| + |t| :=
    max_le (by linarith [le_abs_self (ξ * x), neg_abs_le t]) (by positivity)
  have hI0 : 0 ≤ max (t - ξ * x) 0 := le_max_right _ _
  have hI1 : max (t - ξ * x) 0 ≤ |x| + |t| :=
    max_le (by linarith [neg_abs_le (ξ * x), le_abs_self t]) (by positivity)
  have hVlo := qrOpt_ge M (D := x) (I := max (t - ξ * x) 0) hα0 hc₂ hv
  have hVhi := qrOpt_le_bound M (D := x) (vhat := v) (I := max (t - ξ * x) 0) hα0 hc₂
  rw [abs_of_nonneg hI0] at hVhi
  have e1 : |M.p * (ξ * x)| ≤ M.p * |x| := by
    rw [abs_mul, abs_of_nonneg hp0]; exact mul_le_mul_of_nonneg_left hξx hp0
  have e2 : c₂ * max (ξ * x - t) 0 ≤ c₂ * (|x| + |t|) := mul_le_mul_of_nonneg_left hm1 hc₂0
  have e2' : 0 ≤ c₂ * max (ξ * x - t) 0 := mul_nonneg hc₂0 hm0
  have e3 : |c₁ * t| = |c₁| * |t| := abs_mul _ _
  have e4 : M.p * (α * |x| + max (t - ξ * x) 0) ≤ M.p * (|x| + (|x| + |t|)) := by
    apply mul_le_mul_of_nonneg_left _ hp0
    nlinarith [abs_nonneg x]
  have e5 : 0 ≤ M.vB * max (t - ξ * x) 0 := mul_nonneg M.vB_pos.le hI0
  rw [abs_le]
  constructor
  · nlinarith [abs_le.mp e1, neg_abs_le (c₁ * t), le_abs_self (c₁ * t), abs_nonneg x,
      abs_nonneg t, mul_nonneg hc₂0 (abs_nonneg x)]
  · nlinarith [abs_le.mp e1, neg_abs_le (c₁ * t), le_abs_self (c₁ * t), abs_nonneg x,
      abs_nonneg t, mul_nonneg hc₂0 (abs_nonneg x)]

/-! ### Theorem 2: under (6) every quick-response equilibrium has `v = v̄` -/

lemma max_pos_sub_max_neg (a : ℝ) : max a 0 - max (-a) 0 = a := by
  rcases le_total a 0 with h | h
  · rw [max_eq_right h, max_eq_left (by linarith)]; ring
  · rw [max_eq_left h, max_eq_right (by linarith)]; ring

lemma fillFrac_le_one (M : Model) {α q v x : ℝ} (hα0 : 0 ≤ α) (hx : 0 ≤ x) :
    fillFrac M α q v x ≤ 1 := by
  unfold fillFrac
  split_ifs with h
  · exact le_rfl
  · have h1 : 0 ≤ 1 - xi M α v := by unfold xi; nlinarith [Gbar_nonneg M v]
    have hd : 0 ≤ (1 - xi M α v) * x := mul_nonneg h1 hx
    rcases hd.eq_or_lt with h0 | h0
    · rw [← h0, div_zero]; exact zero_le_one
    · rw [div_le_one h0]; exact (not_le.mp h).le

lemma fillProb_le (M : Model) {α q v : ℝ} (hα0 : 0 ≤ α) :
    fillProb M α q v ≤ ∫ x in Set.Ico 0 (Dl M α q v), M.f x := by
  unfold fillProb
  by_cases hint : IntegrableOn (fun x => fillFrac M α q v x * M.f x) (Set.Ico 0 (Dl M α q v))
  · apply setIntegral_mono_on hint M.density.integrable.integrableOn measurableSet_Ico
    intro x hx
    have := fillFrac_le_one M (q := q) (v := v) hα0 hx.1
    nlinarith [M.density.nonneg x]
  · rw [integral_undef hint]
    exact setIntegral_nonneg measurableSet_Ico (fun x _ => M.density.nonneg x)

set_option maxHeartbeats 1000000 in
lemma thm2_v (M : Model) {α c₁ c₂ : ℝ} (hα0 : 0 < α) (hα1 : α ≤ 1) (hc₁ : M.vB < c₁)
    (hc₁₂ : c₁ ≤ c₂) (h6 : (c₂ - c₁) / (c₂ - M.vB) ≤ (M.vM - M.p) / (M.vhi - M.vB))
    {q v : ℝ} (heq : IsQREquilibrium M α c₁ c₂ q v) : v = M.vhi := by
  obtain ⟨hq0, hmax, ⟨hv1, hv2⟩, -, hBRhi⟩ := heq
  simp only [Set.mem_Ici] at hq0
  by_contra hne
  have hvlt : v < M.vhi := lt_of_le_of_ne hv2 hne
  have hBR := hBRhi hvlt
  have hf := M.density
  have hf0 := hf.nonneg
  have hc₂ : M.vB ≤ c₂ := by linarith
  have hvB := vB_lt_vlo M
  have hvBv : M.vB < v := by linarith
  have hvB0 := M.vB_pos
  have hvBne : M.vB ≠ 0 := hvB0.ne'
  have hξ0 := xi_nonneg M (v := v) hα0.le hα1
  have hξ1 := xi_le_one M (v := v) hα0.le
  have hsm_lt : sm M v < M.vhi := max_lt (by linarith [vhi_pos M]) hvlt
  have hsm_ge : v ≤ sm M v := le_max_right _ _
  have hsm_pos : 0 < sm M v := by linarith
  have hG : 0 < Gbar M (sm M v) := by
    rw [Gbar_mid M (by linarith) hsm_lt.le]; exact div_pos (by linarith) (w_pos M)
  have hfill := fillProb_le M (q := q) (v := v) hα0.le
  have hP0 : 0 ≤ ∫ x in Set.Ico 0 (Dl M α q v), M.f x :=
    setIntegral_nonneg measurableSet_Ico (fun x _ => hf0 x)
  set ξ := xi M α v with hξ
  set k := sm M v * Gbar M (sm M v) * α / M.vB with hk
  have hk0 : 0 < k := div_pos (mul_pos (mul_pos hsm_pos hG) hα0) hvB0
  have hK : 0 < ξ + k := by linarith
  have hDl : Dl M α q v = q / (ξ + k) := rfl
  set P := ∫ x in Set.Ico 0 (Dl M α q v), M.f x with hP
  have hmarg : (c₂ - M.vB) * P ≤ c₂ - c₁ := by
    rcases hq0.eq_or_lt with h0 | hqpos
    · have hD0 : Dl M α q v = 0 := by rw [hDl, ← h0, zero_div]
      have : P = 0 := by simp [hP, hD0]
      rw [this]; linarith
    · set δ := q * k / (ξ + k) with hδ
      have hδpos : 0 < δ := div_pos (mul_pos hqpos hk0) hK
      have hqδ : q - δ = q * ξ / (ξ + k) := by
        rw [hδ]; field_simp; ring
      have hqδ0 : 0 ≤ q - δ := by rw [hqδ]; exact div_nonneg (mul_nonneg hq0 hξ0) hK.le
      have hopt := isMaxOn_iff.mp hmax (q - δ) hqδ0
      let Φ : ℝ → ℝ → ℝ := fun t x => (M.p * (ξ * x) - c₂ * max (ξ * x - t) 0 - c₁ * t +
        qrOptSaleRevenue M α c₂ x v (max (t - ξ * x) 0)) * M.f x
      have hint : ∀ t, Integrable (Φ t) := fun t => qrIntegrable M hα0.le hα1 hc₂ hvBv
      have hπ : ∀ t, qrProfit M α c₁ c₂ t v = ∫ x, Φ t x := fun t => rfl
      let B : ℝ → ℝ := fun x => (c₂ - c₁) * δ * M.f x -
        (c₂ - M.vB) * δ * (Set.Ico 0 (Dl M α q v)).indicator M.f x
      have hBint : Integrable B := (hf.integrable.const_mul _).sub
        ((hf.integrable.indicator measurableSet_Ico).const_mul _)
      have hBval : ∫ x, B x = (c₂ - c₁) * δ - (c₂ - M.vB) * δ * P := by
        simp only [B]
        rw [integral_sub (hf.integrable.const_mul _)
          ((hf.integrable.indicator measurableSet_Ico).const_mul _), integral_const_mul,
          integral_const_mul, hf.integral_eq_one, integral_indicator measurableSet_Ico]
        ring
      have hpt : ∀ x, Φ q x - Φ (q - δ) x ≤ B x := by
        intro x
        simp only [Φ, B]
        by_cases hx : x ∈ Set.Ico 0 (Dl M α q v)
        · rw [Set.indicator_of_mem hx]
          obtain ⟨hx0, hxD⟩ := hx
          rw [hDl, lt_div_iff₀ hK] at hxD
          have hξx : ξ * x ≤ q - δ := by
            rw [hqδ, le_div_iff₀ hK]
            nlinarith [mul_le_mul_of_nonneg_left hxD.le hξ0]
          have hm1 : max (ξ * x - q) 0 = 0 := max_eq_right (by linarith)
          have hm2 : max (ξ * x - (q - δ)) 0 = 0 := max_eq_right (by linarith)
          have hI1 : max (q - ξ * x) 0 = q - ξ * x := max_eq_left (by linarith)
          have hI2 : max (q - δ - ξ * x) 0 = q - δ - ξ * x := max_eq_left (by linarith)
          rw [hm1, hm2, hI1, hI2]
          have hlow : sm M v * Gbar M (sm M v) * α * x ≤ M.vB * (q - ξ * x) := by
            have h1 : k * x ≤ q - ξ * x := by nlinarith
            have hkv : sm M v * Gbar M (sm M v) * α = k * M.vB := by
              rw [hk]; field_simp
            rw [hkv]; nlinarith
          have hV1 := qrOpt_le_low M (c₂ := c₂) hα0.le hc₂ hv1 hv2 hx0 (by linarith) hlow
          have hV2 := qrOpt_ge M (c₂ := c₂) (D := x) (I := q - δ - ξ * x) hα0.le hc₂ hvBv
          have hc : (M.p * (ξ * x) - c₂ * 0 - c₁ * q +
                qrOptSaleRevenue M α c₂ x v (q - ξ * x)) -
              (M.p * (ξ * x) - c₂ * 0 - c₁ * (q - δ) +
                qrOptSaleRevenue M α c₂ x v (q - δ - ξ * x)) ≤
              (c₂ - c₁) * δ - (c₂ - M.vB) * δ := by linarith
          linarith [mul_le_mul_of_nonneg_right hc (hf0 x)]
        · rw [Set.indicator_of_notMem hx]
          have e1 := max_pos_sub_max_neg (q - ξ * x)
          have e2 := max_pos_sub_max_neg (q - δ - ξ * x)
          rw [show -(q - ξ * x) = ξ * x - q by ring] at e1
          rw [show -(q - δ - ξ * x) = ξ * x - (q - δ) by ring] at e2
          have hd0 : 0 ≤ max (q - ξ * x) 0 - max (q - δ - ξ * x) 0 := by
            have := max_le_max_right (0 : ℝ) (show q - δ - ξ * x ≤ q - ξ * x by linarith)
            linarith
          have hshift := qrOpt_shift M (c₂ := c₂) (D := x) (vhat := v)
            (I := max (q - δ - ξ * x) 0) hα0.le hc₂ hd0
          rw [show max (q - δ - ξ * x) 0 + (max (q - ξ * x) 0 - max (q - δ - ξ * x) 0) =
            max (q - ξ * x) 0 by ring] at hshift
          have e3 : c₂ * (max (q - ξ * x) 0 - max (ξ * x - q) 0) = c₂ * (q - ξ * x) := by
            rw [e1]
          have e4 : c₂ * (max (q - δ - ξ * x) 0 - max (ξ * x - (q - δ)) 0) =
              c₂ * (q - δ - ξ * x) := by rw [e2]
          have hc : (M.p * (ξ * x) - c₂ * max (ξ * x - q) 0 - c₁ * q +
                qrOptSaleRevenue M α c₂ x v (max (q - ξ * x) 0)) -
              (M.p * (ξ * x) - c₂ * max (ξ * x - (q - δ)) 0 - c₁ * (q - δ) +
                qrOptSaleRevenue M α c₂ x v (max (q - δ - ξ * x) 0)) ≤ (c₂ - c₁) * δ := by
            linarith
          linarith [mul_le_mul_of_nonneg_right hc (hf0 x)]
      have hdiff : (∫ x, Φ q x) - (∫ x, Φ (q - δ) x) ≤ ∫ x, B x := by
        rw [← integral_sub (hint q) (hint (q - δ))]
        exact integral_mono ((hint q).sub (hint (q - δ))) hBint hpt
      rw [hπ, hπ] at hopt
      rw [hBval] at hdiff
      have h1 : 0 ≤ δ * ((c₂ - c₁) - (c₂ - M.vB) * P) := by
        rw [show δ * ((c₂ - c₁) - (c₂ - M.vB) * P) = (c₂ - c₁) * δ - (c₂ - M.vB) * δ * P by ring]
        linarith
      have h2 := (mul_nonneg_iff_of_pos_left hδpos).mp h1
      linarith
  have hw : M.vM - M.p ≤ (v - M.vB) * P := by
    have hws : waitSurplus M α q v = (v - M.vB) * fillProb M α q v := rfl
    have := mul_le_mul_of_nonneg_left hfill (by linarith : (0:ℝ) ≤ v - M.vB)
    linarith
  have hpv : 0 < M.vM - M.p := by linarith [M.p_lt_vM]
  have hc₂vB : 0 < c₂ - M.vB := by linarith
  have hvhivB : 0 < M.vhi - M.vB := by linarith
  have h1 : P ≤ (c₂ - c₁) / (c₂ - M.vB) := by rw [le_div_iff₀ hc₂vB]; linarith
  have h2 : P * (M.vhi - M.vB) ≤ M.vM - M.p := by
    have := h1.trans h6; rwa [le_div_iff₀ hvhivB] at this
  rcases hP0.eq_or_lt with hP0' | hPpos
  · rw [← hP0'] at hw; linarith
  · nlinarith [mul_lt_mul_of_pos_left hvlt hPpos]

lemma qrSale_vhi (M : Model) (α c₂ D s I q₂ : ℝ) :
    qrSaleRevenue M α c₂ D M.vhi s I q₂ = qrSaleRevenue M 0 c₂ D M.vhi s I q₂ := by
  unfold qrSaleRevenue
  split_ifs with h1 h2
  · rw [Gbar_eq_zero M h1]; simp
  · rw [Gbar_eq_zero M le_rfl]; simp
  · rfl

lemma qrProfit_at_vhi (M : Model) (α c₁ c₂ q : ℝ) :
    qrProfit M α c₁ c₂ q M.vhi = qrProfit M 0 c₁ c₂ q M.vhi := by
  unfold qrProfit qrOptSaleRevenue
  simp only [xi_vhi, qrSale_vhi M α]

/-! ### Theorem 1 (profit part), elementary: strategic profit is at most the myopic optimum -/

lemma opt0 (M : Model) (D : ℝ) {I : ℝ} (hI : 0 ≤ I) :
    optSaleRevenue M 0 D M.vhi I = M.vB * I := by
  apply IsGreatest.csSup_eq
  constructor
  · refine ⟨M.vB, ⟨M.vB_pos.le, (vB_lt_p M).le⟩, ?_⟩
    simp only [saleRevenue]
    rw [if_neg (by linarith [vB_lt_vlo M, M.vlo_lt_vhi]), if_neg (lt_irrefl _)]
  · rintro _ ⟨s, ⟨hs0, hsp⟩, rfl⟩
    dsimp only
    unfold saleRevenue
    split_ifs with h1 h2
    · rw [mul_zero, zero_mul, min_eq_left hI, mul_zero]; exact mul_nonneg M.vB_pos.le hI
    · rw [mul_zero, zero_mul, min_eq_left hI, mul_zero]; exact mul_nonneg M.vB_pos.le hI
    · exact mul_le_mul_of_nonneg_right (not_lt.mp h2) hI

lemma arith1 {p vB q x y B s : ℝ} (hy : y ≤ x) (hB0 : 0 ≤ B) (hB : B ≤ x - y) (hs0 : 0 ≤ s)
    (hsp : s ≤ p) (hvB : 0 ≤ vB) :
    p * min q y + s * min B (max (q - y) 0) ≤ p * min q x + vB * max (q - x) 0 := by
  have hp : 0 ≤ p := hs0.trans hsp
  have hv2 : 0 ≤ vB * max (q - x) 0 := mul_nonneg hvB (le_max_right _ _)
  rcases le_total q y with h | h
  · rw [max_eq_right (by linarith : q - y ≤ 0), min_eq_right hB0, mul_zero, min_eq_left h,
      min_eq_left (h.trans hy)]
    linarith
  · rw [max_eq_left (by linarith : 0 ≤ q - y), min_eq_right h]
    have hm0 : 0 ≤ min B (q - y) := le_min hB0 (by linarith)
    have h1 : s * min B (q - y) ≤ p * min B (q - y) := mul_le_mul_of_nonneg_right hsp hm0
    have h2 : y + min B (q - y) ≤ min q x :=
      le_min (by linarith [min_le_right B (q - y)]) (by linarith [min_le_left B (q - y)])
    nlinarith [mul_le_mul_of_nonneg_left h2 hp]

lemma arith2 {p vB q x y s : ℝ} (hy : y ≤ x) (hs0 : 0 ≤ s) (hsv : s ≤ vB) (hvp : vB ≤ p) :
    p * min q y + s * max (q - y) 0 ≤ p * min q x + vB * max (q - x) 0 := by
  rcases le_total q y with h | h
  · rw [max_eq_right (by linarith : q - y ≤ 0), min_eq_left h, min_eq_left (h.trans hy)]
    nlinarith [mul_nonneg (hs0.trans hsv) (le_max_right (q - x) 0)]
  · rcases le_total q x with h' | h'
    · rw [max_eq_left (by linarith : 0 ≤ q - y), min_eq_right h, min_eq_left h',
        max_eq_right (by linarith : q - x ≤ 0)]
      nlinarith [mul_le_mul_of_nonneg_right (hsv.trans hvp) (by linarith : (0:ℝ) ≤ q - y)]
    · rw [max_eq_left (by linarith : 0 ≤ q - y), min_eq_right h, min_eq_right h',
        max_eq_left (by linarith : 0 ≤ q - x)]
      nlinarith [mul_le_mul_of_nonneg_right hsv (by linarith : (0:ℝ) ≤ q - y),
        mul_le_mul_of_nonneg_right hvp (by linarith : (0:ℝ) ≤ x - y)]

lemma optSale_le (M : Model) {α x v q : ℝ} (hα0 : 0 ≤ α) (hα1 : α ≤ 1) (hx : 0 ≤ x) :
    M.p * min q (xi M α v * x) + optSaleRevenue M α x v (max (q - xi M α v * x) 0) ≤
      M.p * min q x + M.vB * max (q - x) 0 := by
  have hξ0 := xi_nonneg M (v := v) hα0 hα1
  have hξ1 := xi_le_one M (v := v) hα0
  have hy : xi M α v * x ≤ x := by nlinarith
  have hW : x - xi M α v * x = Gbar M v * α * x := by unfold xi; ring
  have hne : (Set.Icc 0 M.p).Nonempty :=
    Set.nonempty_Icc.2 (M.vB_pos.trans (vB_lt_p M)).le
  have key : ∀ y ∈ (fun s => saleRevenue M α x v s (max (q - xi M α v * x) 0)) '' Set.Icc 0 M.p,
      y ≤ M.p * min q x + M.vB * max (q - x) 0 - M.p * min q (xi M α v * x) := by
    rintro _ ⟨s, ⟨hs0, hsp⟩, rfl⟩
    dsimp only
    unfold saleRevenue
    split_ifs with h1 h2
    · have hB0 : 0 ≤ Gbar M s * α * x := mul_nonneg (mul_nonneg (Gbar_nonneg M s) hα0) hx
      have hB : Gbar M s * α * x ≤ x - xi M α v * x := by
        rw [hW]
        exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (Gbar_anti M h1) hα0) hx
      linarith [arith1 (p := M.p) (vB := M.vB) (q := q) hy hB0 hB hs0 hsp M.vB_pos.le]
    · have hB0 : 0 ≤ Gbar M v * α * x := mul_nonneg (mul_nonneg (Gbar_nonneg M v) hα0) hx
      linarith [arith1 (p := M.p) (vB := M.vB) (q := q) hy hB0 hW.ge hs0 hsp M.vB_pos.le]
    · linarith [arith2 (p := M.p) (q := q) hy hs0 (not_lt.mp h2) (vB_lt_p M).le]
  have := csSup_le (hne.image _) key
  unfold optSaleRevenue
  linarith

lemma profit_zero_myopic (M : Model) (c : ℝ) : profit M 0 c 0 M.vhi = 0 := by
  unfold profit
  refine integral_eq_zero_of_ae (Filter.Eventually.of_forall fun x => ?_)
  simp only [Pi.zero_apply]
  rw [xi_zero, one_mul, opt0 M x (le_max_right _ _)]
  rcases le_or_gt 0 x with hx | hx
  · rw [min_eq_left hx, max_eq_right (by linarith)]; ring
  · rw [M.density.eq_zero_of_neg x hx]; ring

lemma myopic_integrable (M : Model) (c q : ℝ) :
    Integrable (fun x => (M.p * min q (xi M 0 M.vhi * x) - c * q +
      optSaleRevenue M 0 x M.vhi (max (q - xi M 0 M.vhi * x) 0)) * M.f x) := by
  have e : (fun x => (M.p * min q (xi M 0 M.vhi * x) - c * q +
      optSaleRevenue M 0 x M.vhi (max (q - xi M 0 M.vhi * x) 0)) * M.f x) =
      fun x => (M.p * min q x - c * q + M.vB * max (q - x) 0) * M.f x := by
    funext x; rw [xi_zero, one_mul, opt0 M x (le_max_right _ _)]
  rw [e]
  have hp : 0 ≤ M.p := (M.vB_pos.trans (vB_lt_p M)).le
  apply integrable_of_bound M.f _ M.density (by fun_prop)
    (M.p * |q| + |c * q| + M.vB * |q|) (M.p + M.vB)
  intro x
  have hmin : |min q x| ≤ |q| + |x| := by
    rw [abs_le]; constructor
    · exact le_min (by linarith [neg_abs_le q, abs_nonneg x]) (by linarith [neg_abs_le x, abs_nonneg q])
    · linarith [min_le_left q x, le_abs_self q, abs_nonneg x]
  have e1 : |M.p * min q x| ≤ M.p * (|q| + |x|) := by
    rw [abs_mul, abs_of_nonneg hp]; exact mul_le_mul_of_nonneg_left hmin hp
  have hm1 : max (q - x) 0 ≤ |q| + |x| :=
    max_le (by linarith [le_abs_self q, neg_abs_le x]) (by positivity)
  have e2 : M.vB * max (q - x) 0 ≤ M.vB * (|q| + |x|) :=
    mul_le_mul_of_nonneg_left hm1 M.vB_pos.le
  have e2' : 0 ≤ M.vB * max (q - x) 0 := mul_nonneg M.vB_pos.le (le_max_right _ _)
  rw [abs_le]; constructor
  · nlinarith [abs_le.mp e1, neg_abs_le (c * q), le_abs_self (c * q), abs_nonneg x,
      abs_nonneg q, mul_nonneg M.vB_pos.le (abs_nonneg x)]
  · nlinarith [abs_le.mp e1, neg_abs_le (c * q), le_abs_self (c * q), abs_nonneg x,
      abs_nonneg q, mul_nonneg M.vB_pos.le (abs_nonneg x)]

lemma profit_le_myopic (M : Model) {α c q v qm : ℝ} (hα0 : 0 ≤ α) (hα1 : α ≤ 1)
    (hq : q ∈ Set.Ici (0 : ℝ))
    (hmax : IsMaxOn (fun q' => profit M 0 c q' M.vhi) (Set.Ici 0) qm) :
    profit M α c q v ≤ profit M 0 c qm M.vhi := by
  have h1 := isMaxOn_iff.mp hmax q hq
  have h0 := isMaxOn_iff.mp hmax 0 (Set.mem_Ici.mpr le_rfl)
  rw [profit_zero_myopic] at h0
  by_cases hint : Integrable (fun x => (M.p * min q (xi M α v * x) - c * q +
      optSaleRevenue M α x v (max (q - xi M α v * x) 0)) * M.f x)
  · have : profit M α c q v ≤ profit M 0 c q M.vhi := by
      unfold profit
      apply integral_mono hint (myopic_integrable M c q)
      intro x
      dsimp only
      have hf0 := M.density.nonneg x
      rcases le_or_gt 0 x with hx | hx
      · apply mul_le_mul_of_nonneg_right _ hf0
        rw [xi_zero, one_mul, opt0 M x (le_max_right _ _)]
        linarith [optSale_le M (v := v) (q := q) hα0 hα1 hx]
      · rw [M.density.eq_zero_of_neg x hx]; simp
    linarith
  · have : profit M α c q v = 0 := integral_undef hint
    linarith

end StrategicQR.Game.QV3e18

open StrategicQR.Game in
theorem solution (M : Model) (hmslr : MSLR M.f) (hNR : NoRationing M)
    {α c₁ c₂ : ℝ} (hα0 : 0 < α) (hα1 : α ≤ 1) (hc₁ : M.vB < c₁) (hc₁p : c₁ < M.p)
    (hc₁₂ : c₁ ≤ c₂) (hc₂p : c₂ ≤ M.p)
    (h6 : (c₂ - c₁) / (c₂ - M.vB) ≤ (M.vM - M.p) / (M.vhi - M.vB))
    {q v qr vr qm qrm : ℝ}
    (heq : IsEquilibrium M α c₁ q v) (hqr : IsQREquilibrium M α c₁ c₂ qr vr)
    (hqm : qm ∈ Set.Ici (0 : ℝ))
    (hmax : IsMaxOn (fun q' => profit M 0 c₁ q' M.vhi) (Set.Ici 0) qm)
    (hqrm : qrm ∈ Set.Ici (0 : ℝ))
    (hrmax : IsMaxOn (fun q' => qrProfit M 0 c₁ c₂ q' M.vhi) (Set.Ici 0) qrm) :
    qrProfit M 0 c₁ c₂ qrm M.vhi - profit M 0 c₁ qm M.vhi ≤
      qrProfit M α c₁ c₂ qr vr - profit M α c₁ q v := by
  have hvr := QV3e18.thm2_v M hα0 hα1 hc₁ hc₁₂ h6 hqr
  obtain ⟨-, hqrmax, -⟩ := hqr
  subst hvr
  have hA : qrProfit M 0 c₁ c₂ qrm M.vhi ≤ qrProfit M α c₁ c₂ qr M.vhi := by
    rw [← QV3e18.qrProfit_at_vhi M α c₁ c₂ qrm]
    exact isMaxOn_iff.mp hqrmax qrm hqrm
  have hB : profit M α c₁ q v ≤ profit M 0 c₁ qm M.vhi :=
    QV3e18.profit_le_myopic M hα0.le hα1 heq.1 hmax
  linarith
