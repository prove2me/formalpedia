-- Prove2me | solution 1 for ShortWDRODual.Legendre.lemma_2_G
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-04T12:09:18.20619+00:00
-- url     : https://prove2.me/submissions/d249840f-79a2-4449-a2c4-5cec15c43221

import Mathlib
import Definitions.Def_ModelRiskOT_Duality_extIntegral
import Definitions.Def_ShortWDRODual_Legendre_Setting

open MeasureTheory ModelRiskOT.Duality ShortWDRODual.Legendre Filter Topology

namespace WDRO1L2G

variable {X : Type*} [MeasurableSpace X]

lemma lamMul_eq (lam : ℝ) {t : ENNReal} (ht : t ≠ ⊤) :
    lamMul lam t = ((lam * t.toReal : ℝ) : EReal) := by
  unfold lamMul
  rw [if_neg ht, EReal.coe_mul, EReal.coe_ennreal_toReal ht]

lemma lamMul_mono (t : ENNReal) {a b : ℝ} (hab : a ≤ b) : lamMul a t ≤ lamMul b t := by
  by_cases ht : t = ⊤
  · unfold lamMul; rw [if_pos ht, if_pos ht]
  · rw [lamMul_eq a ht, lamMul_eq b ht]
    exact_mod_cast mul_le_mul_of_nonneg_right hab ENNReal.toReal_nonneg

lemma phi_top (c : X → X → ENNReal) (f : X → ℝ) (lam : ℝ) (p : X × X) (h : c p.1 p.2 = ⊤) :
    phiLam c f lam p = ⊥ := by
  unfold phiLam lamMul; rw [if_pos h, EReal.sub_top]

lemma phi_fin (c : X → X → ENNReal) (f : X → ℝ) (lam : ℝ) (p : X × X) (h : c p.1 p.2 ≠ ⊤) :
    phiLam c f lam p = ((f p.2 - lam * (c p.1 p.2).toReal : ℝ) : EReal) := by
  unfold phiLam; rw [lamMul_eq lam h, ← EReal.coe_sub]

lemma extIntegral_mono (μ : Measure X) {φ ψ : X → EReal} (h : ∀ x, φ x ≤ ψ x) :
    extIntegral μ φ ≤ extIntegral μ ψ := by
  unfold extIntegral
  apply EReal.sub_le_sub
  · exact_mod_cast lintegral_mono fun x => EReal.toENNReal_le_toENNReal (h x)
  · exact_mod_cast lintegral_mono fun x => EReal.toENNReal_le_toENNReal (EReal.neg_le_neg_iff.mpr (h x))

lemma f_le_u (c : X → X → ENNReal) (f : X → ℝ) (hc0 : ∀ x, c x x = 0) (lam : ℝ) (xh : X) :
    (f xh : EReal) ≤ supFn (phiLam c f lam) xh := by
  unfold supFn
  refine le_iSup_of_le xh ?_
  rw [phi_fin c f lam (xh, xh) (by simp [hc0])]
  simp [hc0]

lemma u_anti (c : X → X → ENNReal) (f : X → ℝ) {a b : ℝ} (hab : a ≤ b) (xh : X) :
    supFn (phiLam c f b) xh ≤ supFn (phiLam c f a) xh := by
  unfold supFn
  exact iSup_mono fun x => EReal.sub_le_sub le_rfl (lamMul_mono _ hab)

lemma real_sup (a b lam0 : ℝ) (hb : 0 ≤ b) :
    ⨆ n : ℕ, (((a - (lam0 + 1 / ((n : ℝ) + 1)) * b) : ℝ) : EReal) = ((a - lam0 * b : ℝ) : EReal) := by
  apply le_antisymm
  · refine iSup_le fun n => ?_
    have : 0 ≤ 1 / ((n : ℝ) + 1) * b := by positivity
    exact_mod_cast (by nlinarith : a - (lam0 + 1 / ((n : ℝ) + 1)) * b ≤ a - lam0 * b)
  · refine le_of_forall_lt fun y hy => ?_
    induction y using EReal.rec with
    | bot => exact lt_of_lt_of_le (EReal.bot_lt_coe _) (le_iSup_of_le 0 le_rfl)
    | top => exact absurd hy (not_lt.mpr le_top)
    | coe y =>
      have hy' : y < a - lam0 * b := by exact_mod_cast hy
      obtain ⟨n, hn⟩ := exists_nat_gt (b / (a - lam0 * b - y))
      refine lt_of_lt_of_le ?_ (le_iSup_of_le n le_rfl)
      have hd : 0 < a - lam0 * b - y := by linarith
      have hn1 : (0 : ℝ) < (n : ℝ) + 1 := by positivity
      have : 1 / ((n : ℝ) + 1) * b < a - lam0 * b - y := by
        rw [div_lt_iff₀ hd] at hn
        rw [one_div_mul_eq_div, div_lt_iff₀ hn1]
        nlinarith
      exact_mod_cast (by nlinarith : y < a - (lam0 + 1 / ((n : ℝ) + 1)) * b)

lemma phi_sup (c : X → X → ENNReal) (f : X → ℝ) (lam0 : ℝ) (p : X × X) :
    ⨆ n : ℕ, phiLam c f (lam0 + 1 / ((n : ℝ) + 1)) p = phiLam c f lam0 p := by
  by_cases h : c p.1 p.2 = ⊤
  · simp [phi_top c f _ p h]
  · simp_rw [phi_fin c f _ p h]
    exact real_sup _ _ _ ENNReal.toReal_nonneg

lemma u_sup (c : X → X → ENNReal) (f : X → ℝ) (lam0 : ℝ) (xh : X) :
    supFn (phiLam c f lam0) xh = ⨆ n : ℕ, supFn (phiLam c f (lam0 + 1 / ((n : ℝ) + 1))) xh := by
  unfold supFn
  rw [iSup_comm]
  congr 1; funext x
  exact (phi_sup c f lam0 (xh, x)).symm

lemma u_mono_seq (c : X → X → ENNReal) (f : X → ℝ) (lam0 : ℝ) (xh : X) :
    Monotone fun n : ℕ => supFn (phiLam c f (lam0 + 1 / ((n : ℝ) + 1))) xh := by
  intro n m hnm
  apply u_anti
  have : (n : ℝ) ≤ m := by exact_mod_cast hnm
  have h1 : (0 : ℝ) < n + 1 := by positivity
  have : 1 / ((m : ℝ) + 1) ≤ 1 / ((n : ℝ) + 1) := one_div_le_one_div_of_le h1 (by linarith)
  linarith

/-- pointwise identity behind linearity of `extIntegral` -/
lemma pw_id (x y : EReal) (hx : x ≠ ⊥) (hy : y ≠ ⊥) (p q : ℝ) (hp : 0 < p) (hq : 0 < q) :
    ((p : EReal) * x + (q : EReal) * y).toENNReal +
        (ENNReal.ofReal p * (-x).toENNReal + ENNReal.ofReal q * (-y).toENNReal) =
      (-((p : EReal) * x + (q : EReal) * y)).toENNReal +
        (ENNReal.ofReal p * x.toENNReal + ENNReal.ofReal q * y.toENNReal) := by
  have hp0 : ENNReal.ofReal p ≠ 0 := (ENNReal.ofReal_pos.mpr hp).ne'
  have hq0 : ENNReal.ofReal q ≠ 0 := (ENNReal.ofReal_pos.mpr hq).ne'
  induction x using EReal.rec with
  | bot => exact absurd rfl hx
  | top =>
    have hqy : (q : EReal) * y ≠ ⊥ := by
      induction y using EReal.rec with
      | bot => exact absurd rfl hy
      | top => rw [EReal.coe_mul_top_of_pos hq]; exact top_ne_bot
      | coe y => rw [← EReal.coe_mul]; exact EReal.coe_ne_bot _
    rw [EReal.coe_mul_top_of_pos hp, EReal.top_add_of_ne_bot hqy]
    simp [ENNReal.mul_top hp0]
  | coe r =>
    induction y using EReal.rec with
    | bot => exact absurd rfl hy
    | top =>
      have hpr : (p : EReal) * (r : EReal) ≠ ⊥ := by rw [← EReal.coe_mul]; exact EReal.coe_ne_bot _
      rw [EReal.coe_mul_top_of_pos hq, EReal.add_top_of_ne_bot hpr, EReal.toENNReal_top,
        EReal.neg_top, EReal.toENNReal_bot, ENNReal.mul_top hq0]
      rw [top_add, add_top, add_top]
    | coe s =>
      rw [← EReal.coe_mul, ← EReal.coe_mul, ← EReal.coe_add, ← EReal.coe_neg, ← EReal.coe_neg,
        ← EReal.coe_neg]
      simp only [EReal.real_coe_toENNReal]
      rw [← ENNReal.ofReal_mul hp.le, ← ENNReal.ofReal_mul hq.le, ← ENNReal.ofReal_mul hp.le,
        ← ENNReal.ofReal_mul hq.le]
      have key : ∀ w : ℝ, max w 0 = max (-w) 0 + w := by
        intro w; rcases le_total w 0 with h | h
        · rw [max_eq_right h, max_eq_left (by linarith)]; ring
        · rw [max_eq_left h, max_eq_right (by linarith)]; ring
      rw [← ENNReal.toReal_eq_toReal_iff' (by finiteness) (by finiteness)]
      rw [ENNReal.toReal_add (by finiteness) (by finiteness),
        ENNReal.toReal_add (by finiteness) (by finiteness),
        ENNReal.toReal_add (by finiteness) (by finiteness),
        ENNReal.toReal_add (by finiteness) (by finiteness)]
      simp only [ENNReal.toReal_ofReal']
      have e1 : p * -r = -(p * r) := by ring
      have e2 : q * -s = -(q * s) := by ring
      rw [e1, e2, key (p * r + q * s), key (p * r), key (q * s)]
      ring

lemma ennreal_coe_sub_fin {a b : ENNReal} (ha : a ≠ ⊤) (hb : b ≠ ⊤) :
    ((a : EReal) - (b : EReal)) = ((a.toReal - b.toReal : ℝ) : EReal) := by
  rw [EReal.coe_sub, EReal.coe_ennreal_toReal ha, EReal.coe_ennreal_toReal hb]

/-- convexity of `extIntegral` (in fact linearity) for functions bounded below. -/
lemma conv_ext (μ : Measure X) (v1 v2 : X → EReal) (h1 : AEMeasurable v1 μ)
    (h2 : AEMeasurable v2 μ) (hb1 : ∀ x, v1 x ≠ ⊥) (hb2 : ∀ x, v2 x ≠ ⊥)
    (hN1 : ∫⁻ x, (-v1 x).toENNReal ∂μ ≠ ⊤) (hN2 : ∫⁻ x, (-v2 x).toENNReal ∂μ ≠ ⊤)
    (p q : ℝ) (hp : 0 < p) (hq : 0 < q) :
    extIntegral μ (fun x => (p : EReal) * v1 x + (q : EReal) * v2 x) ≤
      (p : EReal) * extIntegral μ v1 + (q : EReal) * extIntegral μ v2 := by
  have hneg : Measurable (fun e : EReal => -e) := (continuous_neg : Continuous fun e : EReal => -e).measurable
  have hw : AEMeasurable (fun x => (p : EReal) * v1 x + (q : EReal) * v2 x) μ :=
    (h1.const_mul _).add (h2.const_mul _)
  have hw1 := hw.ereal_toENNReal
  have hw2 : AEMeasurable (fun x => (-((p : EReal) * v1 x + (q : EReal) * v2 x)).toENNReal) μ :=
    (hneg.comp_aemeasurable hw).ereal_toENNReal
  have hv1p := h1.ereal_toENNReal
  have hv2p := h2.ereal_toENNReal
  have hv1m : AEMeasurable (fun x => (-v1 x).toENNReal) μ :=
    (hneg.comp_aemeasurable h1).ereal_toENNReal
  have hv2m : AEMeasurable (fun x => (-v2 x).toENNReal) μ :=
    (hneg.comp_aemeasurable h2).ereal_toENNReal
  have hid := lintegral_congr (μ := μ) (fun x => pw_id (v1 x) (v2 x) (hb1 x) (hb2 x) p q hp hq)
  rw [lintegral_add_left' hw1, lintegral_add_left' (hv1m.const_mul _),
    lintegral_const_mul'' _ hv1m, lintegral_const_mul'' _ hv2m,
    lintegral_add_left' hw2, lintegral_add_left' (hv1p.const_mul _),
    lintegral_const_mul'' _ hv1p, lintegral_const_mul'' _ hv2p] at hid
  set Wp := ∫⁻ x, ((p : EReal) * v1 x + (q : EReal) * v2 x).toENNReal ∂μ
  set Wm := ∫⁻ x, (-((p : EReal) * v1 x + (q : EReal) * v2 x)).toENNReal ∂μ
  set P1 := ∫⁻ x, (v1 x).toENNReal ∂μ
  set P2 := ∫⁻ x, (v2 x).toENNReal ∂μ
  set N1 := ∫⁻ x, (-v1 x).toENNReal ∂μ
  set N2 := ∫⁻ x, (-v2 x).toENNReal ∂μ
  unfold extIntegral
  change (Wp : EReal) - (Wm : EReal) ≤ (p : EReal) * ((P1 : EReal) - (N1 : EReal)) +
    (q : EReal) * ((P2 : EReal) - (N2 : EReal))
  have hnb : ∀ (P N : ENNReal), N ≠ ⊤ → (P : EReal) - (N : EReal) ≠ ⊥ := by
    intro P N hN
    rw [← EReal.coe_ennreal_toReal hN]
    refine ne_bot_of_le_ne_bot (EReal.coe_ne_bot (-N.toReal)) ?_
    have := EReal.sub_le_sub (EReal.coe_ennreal_nonneg P) (le_refl ((N.toReal : ℝ) : EReal))
    rw [zero_sub, ← EReal.coe_neg] at this
    exact this
  have hmulnb : ∀ (r : ℝ) (e : EReal), 0 < r → e ≠ ⊥ → (r : EReal) * e ≠ ⊥ := by
    intro r e hr he
    induction e using EReal.rec with
    | bot => exact absurd rfl he
    | top => rw [EReal.coe_mul_top_of_pos hr]; exact top_ne_bot
    | coe e => rw [← EReal.coe_mul]; exact EReal.coe_ne_bot _
  by_cases hP1 : P1 = ⊤
  · rw [hP1, EReal.coe_ennreal_top, ← EReal.coe_ennreal_toReal hN1, EReal.top_sub_coe,
      EReal.coe_mul_top_of_pos hp, EReal.top_add_of_ne_bot (hmulnb q _ hq (hnb P2 N2 hN2))]
    exact le_top
  by_cases hP2 : P2 = ⊤
  · rw [hP2, EReal.coe_ennreal_top, ← EReal.coe_ennreal_toReal hN2, EReal.top_sub_coe,
      EReal.coe_mul_top_of_pos hq, EReal.add_top_of_ne_bot (hmulnb p _ hp (hnb P1 N1 hN1))]
    exact le_top
  by_cases hWm : Wm = ⊤
  · rw [hWm, EReal.coe_ennreal_top, EReal.sub_top]; exact bot_le
  have hfinR : ENNReal.ofReal p * P1 + ENNReal.ofReal q * P2 ≠ ⊤ := by finiteness
  have hfinL : ENNReal.ofReal p * N1 + ENNReal.ofReal q * N2 ≠ ⊤ := by finiteness
  have hWp : Wp ≠ ⊤ := by
    intro h
    rw [h, top_add] at hid
    exact (ENNReal.add_ne_top.mpr ⟨hWm, hfinR⟩) hid.symm
  have hr := congrArg ENNReal.toReal hid
  rw [ENNReal.toReal_add hWp hfinL, ENNReal.toReal_add hWm hfinR,
    ENNReal.toReal_add (by finiteness) (by finiteness),
    ENNReal.toReal_add (by finiteness) (by finiteness)] at hr
  simp only [ENNReal.toReal_mul, ENNReal.toReal_ofReal hp.le, ENNReal.toReal_ofReal hq.le] at hr
  rw [ennreal_coe_sub_fin hWp hWm, ennreal_coe_sub_fin hP1 hN1, ennreal_coe_sub_fin hP2 hN2,
    ← EReal.coe_mul, ← EReal.coe_mul, ← EReal.coe_add]
  exact_mod_cast (by linarith : Wp.toReal - Wm.toReal ≤
    p * (P1.toReal - N1.toReal) + q * (P2.toReal - N2.toReal))

end WDRO1L2G

open WDRO1L2G

theorem solution {X : Type*} [MeasurableSpace X]
    (Phat : Measure X) [IsProbabilityMeasure Phat]
    (f : X → ℝ) (c : X → X → ENNReal)
    (hf : Measurable f)
    (hfint : ⊥ < extIntegral Phat (fun x => (f x : EReal)))
    (hc : Measurable (fun p : X × X => c p.1 p.2))
    (hc0 : ∀ x, c x x = 0)
    (hG : ∀ lam : ℝ, 0 < lam → NullMeasurable (supFn (phiLam c f lam)) Phat) :
    (∀ lam : ℝ, 0 ≤ lam → extIntegral Phat (fun x => (f x : EReal)) ≤ dualG c f Phat lam) ∧
    AntitoneOn (dualG c f Phat) (Set.Ici 0) ∧
    (∀ a b t : ℝ, 0 ≤ a → 0 ≤ b → 0 ≤ t → t ≤ 1 →
      dualG c f Phat ((1 - t) * a + t * b) ≤
        ((1 - t : ℝ) : EReal) * dualG c f Phat a + ((t : ℝ) : EReal) * dualG c f Phat b) ∧
    LowerSemicontinuousOn (dualG c f Phat) (Set.Ici 0) := by
  set u : ℝ → X → EReal := fun lam => supFn (phiLam c f lam) with hu
  have hG' : ∀ lam, dualG c f Phat lam = extIntegral Phat (u lam) := fun lam => rfl
  -- integrability of the negative part of `f`
  have hNf : ∫⁻ x, (-(f x : EReal)).toENNReal ∂Phat ≠ ⊤ := by
    intro h
    unfold extIntegral at hfint
    rw [h, EReal.coe_ennreal_top, EReal.sub_top] at hfint
    exact lt_irrefl _ hfint
  have hNu : ∀ lam, ∫⁻ x, (-(u lam x)).toENNReal ∂Phat ≠ ⊤ := by
    intro lam
    refine ne_top_of_le_ne_top hNf (lintegral_mono fun x => ?_)
    exact EReal.toENNReal_le_toENNReal (EReal.neg_le_neg_iff.mpr (f_le_u c f hc0 lam x))
  have hub : ∀ lam x, u lam x ≠ ⊥ := fun lam x =>
    ne_bot_of_le_ne_bot (EReal.coe_ne_bot _) (f_le_u c f hc0 lam x)
  -- measurability for `λ ≥ 0`
  have hmeas : ∀ lam : ℝ, 0 ≤ lam → AEMeasurable (u lam) Phat := by
    intro lam hlam
    rcases hlam.lt_or_eq with hpos | h0
    · exact (hG lam hpos).aemeasurable
    · have : u lam = fun xh => ⨆ n : ℕ, u (lam + 1 / ((n : ℝ) + 1)) xh := by
        funext xh; exact u_sup c f lam xh
      rw [this]
      refine AEMeasurable.iSup fun n => (hG _ ?_).aemeasurable
      rw [← h0]; positivity
  have hlb : ∀ lam : ℝ, 0 ≤ lam → extIntegral Phat (fun x => (f x : EReal)) ≤ dualG c f Phat lam :=
    fun lam _ => extIntegral_mono Phat (f_le_u c f hc0 lam)
  have hanti : AntitoneOn (dualG c f Phat) (Set.Ici 0) :=
    fun a _ b _ hab => extIntegral_mono Phat (u_anti c f hab)
  refine ⟨hlb, hanti, ?_, ?_⟩
  · -- convexity
    intro a b t ha hb ht0 ht1
    rcases ht0.lt_or_eq with ht0' | ht0'
    swap
    · subst ht0'; simp
    rcases ht1.lt_or_eq with ht1' | ht1'
    swap
    · subst ht1'; simp
    have hpw : ∀ xh, u ((1 - t) * a + t * b) xh ≤
        ((1 - t : ℝ) : EReal) * u a xh + ((t : ℝ) : EReal) * u b xh := by
      intro xh
      refine iSup_le fun x => ?_
      have h1 : phiLam c f ((1 - t) * a + t * b) (xh, x) ≤
          ((1 - t : ℝ) : EReal) * phiLam c f a (xh, x) + ((t : ℝ) : EReal) * phiLam c f b (xh, x) := by
        by_cases hcx : c xh x = ⊤
        · rw [phi_top c f _ (xh, x) hcx]; exact bot_le
        · rw [phi_fin c f _ (xh, x) hcx, phi_fin c f _ (xh, x) hcx, phi_fin c f _ (xh, x) hcx,
            ← EReal.coe_mul, ← EReal.coe_mul, ← EReal.coe_add]
          exact_mod_cast le_of_eq (by ring)
      refine h1.trans (add_le_add ?_ ?_)
      · exact mul_le_mul_of_nonneg_left (le_iSup (fun x => phiLam c f a (xh, x)) x)
          (by exact_mod_cast (by linarith : (0 : ℝ) ≤ 1 - t))
      · exact mul_le_mul_of_nonneg_left (le_iSup (fun x => phiLam c f b (xh, x)) x)
          (by exact_mod_cast ht0)
    calc dualG c f Phat ((1 - t) * a + t * b)
        ≤ extIntegral Phat (fun xh => ((1 - t : ℝ) : EReal) * u a xh + ((t : ℝ) : EReal) * u b xh) :=
          extIntegral_mono Phat hpw
      _ ≤ _ := conv_ext Phat (u a) (u b) (hmeas a ha) (hmeas b hb) (hub a) (hub b) (hNu a) (hNu b)
          (1 - t) t (by linarith) ht0'
  · -- lower semicontinuity
    intro lam0 hlam0 y hy
    have hlam0' : 0 ≤ lam0 := hlam0
    set ln : ℕ → ℝ := fun n => lam0 + 1 / ((n : ℝ) + 1) with hln
    have hln0 : ∀ n, 0 ≤ ln n := fun n => by simp only [hln]; positivity
    have hmono : ∀ xh, Monotone fun n => u (ln n) xh := u_mono_seq c f lam0
    have hsupx : ∀ xh, u lam0 xh = ⨆ n, u (ln n) xh := u_sup c f lam0
    -- positive parts
    have hpos_pt : ∀ xh, (u lam0 xh).toENNReal = ⨆ n, (u (ln n) xh).toENNReal := by
      intro xh
      have ht : Tendsto (fun n => u (ln n) xh) atTop (𝓝 (u lam0 xh)) := by
        rw [hsupx xh]; exact tendsto_atTop_iSup (hmono xh)
      have ht' := (EReal.continuous_toENNReal.tendsto _).comp ht
      exact (iSup_eq_of_tendsto (fun n m h => EReal.toENNReal_le_toENNReal (hmono xh h)) ht').symm
    have hneg_pt : ∀ xh, (-(u lam0 xh)).toENNReal = ⨅ n, (-(u (ln n) xh)).toENNReal := by
      intro xh
      have ht : Tendsto (fun n => u (ln n) xh) atTop (𝓝 (u lam0 xh)) := by
        rw [hsupx xh]; exact tendsto_atTop_iSup (hmono xh)
      have ht' := (EReal.continuous_toENNReal.tendsto _).comp
        (((continuous_neg : Continuous fun e : EReal => -e).tendsto _).comp ht)
      exact (iInf_eq_of_tendsto (fun n m h => EReal.toENNReal_le_toENNReal
        (EReal.neg_le_neg_iff.mpr (hmono xh h))) ht').symm
    have hneg : Measurable (fun e : EReal => -e) := (continuous_neg : Continuous fun e : EReal => -e).measurable
    have hA : ∫⁻ xh, (u lam0 xh).toENNReal ∂Phat = ⨆ n, ∫⁻ xh, (u (ln n) xh).toENNReal ∂Phat := by
      simp_rw [hpos_pt]
      exact lintegral_iSup' (fun n => (hmeas _ (hln0 n)).ereal_toENNReal)
        (ae_of_all _ fun xh n m h => EReal.toENNReal_le_toENNReal (hmono xh h))
    have hB : ∫⁻ xh, (-(u lam0 xh)).toENNReal ∂Phat = ⨅ n, ∫⁻ xh, (-(u (ln n) xh)).toENNReal ∂Phat := by
      simp_rw [hneg_pt]
      exact lintegral_iInf' (fun n => (hneg.comp_aemeasurable (hmeas _ (hln0 n))).ereal_toENNReal)
        (ae_of_all _ fun xh n m h => EReal.toENNReal_le_toENNReal
          (EReal.neg_le_neg_iff.mpr (hmono xh h))) (hNu _)
    set a : ℕ → ENNReal := fun n => ∫⁻ xh, (u (ln n) xh).toENNReal ∂Phat
    set b : ℕ → ENNReal := fun n => ∫⁻ xh, (-(u (ln n) xh)).toENNReal ∂Phat
    have ha_mono : Monotone a := fun n m h =>
      lintegral_mono fun xh => EReal.toENNReal_le_toENNReal (hmono xh h)
    have hb_anti : Antitone b := fun n m h =>
      lintegral_mono fun xh => EReal.toENNReal_le_toENNReal (EReal.neg_le_neg_iff.mpr (hmono xh h))
    have hta : Tendsto a atTop (𝓝 (⨆ n, a n)) := tendsto_atTop_iSup ha_mono
    have htb : Tendsto b atTop (𝓝 (⨅ n, b n)) := tendsto_atTop_iInf hb_anti
    have hBfin : (⨅ n, b n) ≠ ⊤ := by rw [← hB]; exact hNu _
    have hG0 : dualG c f Phat lam0 = ((⨆ n, a n : ENNReal) : EReal) - ((⨅ n, b n : ENNReal) : EReal) := by
      rw [hG', ← hA, ← hB]; rfl
    have hGn : ∀ n, dualG c f Phat (ln n) = ((a n : ENNReal) : EReal) - ((b n : ENNReal) : EReal) :=
      fun n => rfl
    have hlim : Tendsto (fun n => dualG c f Phat (ln n)) atTop (𝓝 (dualG c f Phat lam0)) := by
      simp_rw [hGn, hG0, sub_eq_add_neg]
      have h1 := (continuous_coe_ennreal_ereal.tendsto _).comp hta
      have h2 := ((continuous_neg : Continuous fun e : EReal => -e).tendsto _).comp ((continuous_coe_ennreal_ereal.tendsto _).comp htb)
      refine (EReal.continuousAt_add ?_ ?_).tendsto.comp (h1.prodMk_nhds h2)
      · right
        simp only [ne_eq, EReal.neg_eq_bot_iff, EReal.coe_ennreal_eq_top_iff]
        exact hBfin
      · left; exact EReal.coe_ennreal_ne_bot _
    obtain ⟨n, hn⟩ := (hlim.eventually (lt_mem_nhds hy)).exists
    have hlt : lam0 < ln n := by
      simp only [hln]
      have : (0:ℝ) < 1 / ((n : ℝ) + 1) := by positivity
      linarith
    have hev : ∀ᶠ lam in 𝓝[Set.Ici 0] lam0, lam ∈ Set.Ici (0 : ℝ) ∧ lam < ln n :=
      eventually_mem_nhdsWithin.and ((eventually_lt_nhds hlt).filter_mono nhdsWithin_le_nhds)
    refine hev.mono fun lam ⟨hl0, hl1⟩ => ?_
    exact lt_of_lt_of_le hn (hanti hl0 (Set.mem_Ici.mpr (hln0 n)) hl1.le)
