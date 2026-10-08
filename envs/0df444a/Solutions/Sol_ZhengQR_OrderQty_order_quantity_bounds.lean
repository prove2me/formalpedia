-- Prove2me | solution 1 for ZhengQR.OrderQty.order_quantity_bounds
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-05T23:18:27.247275+00:00
-- url     : https://prove2.me/submissions/3e4c47d5-5040-4302-90c9-ef7e85e22707

import Mathlib
import Definitions.Def_ZhengQR_OrderQty_newsvendorCost
import Definitions.Def_ZhengQR_OrderQty_qrMachinery

open MeasureTheory Filter Topology


namespace ZhengQR.OrderQty

/-! ### Abstract part: `G` continuous, strictly decreasing then strictly increasing. -/

lemma aux_ihq_deriv {G : ℝ → ℝ} (hc : Continuous G) (Q r : ℝ) :
    HasDerivAt (fun r => ∫ y in r..r + Q, G y) (G (r + Q) - G r) r := by
  have h1 : ∀ u, HasDerivAt (fun u => ∫ y in (0:ℝ)..u, G y) (G u) u := fun u =>
    (hc.integral_hasStrictDerivAt 0 u).hasDerivAt
  have h2 : HasDerivAt (fun r => ∫ y in (0:ℝ)..r + Q, G y) (G (r + Q)) r := by
    exact HasDerivAt.comp_add_const r Q (h1 (r + Q))
  have h3 := h2.sub (h1 r)
  have heq : (fun r => ∫ y in r..r + Q, G y) =
      fun r => (∫ y in (0:ℝ)..r + Q, G y) - ∫ y in (0:ℝ)..r, G y := by
    funext r
    rw [intervalIntegral.integral_interval_sub_left]
    · exact hc.intervalIntegrable _ _
    · exact hc.intervalIntegrable _ _
  rw [heq]; exact h3

lemma aux_ihq_crit {G : ℝ → ℝ} (hc : Continuous G) {Q r : ℝ}
    (hr : ∀ r' : ℝ, (∫ y in r..r + Q, G y) ≤ ∫ y in r'..r' + Q, G y) :
    G (r + Q) - G r = 0 := by
  have hmin : IsLocalMin (fun r => ∫ y in r..r + Q, G y) r :=
    Filter.Eventually.of_forall hr
  exact hmin.hasDerivAt_eq_zero (aux_ihq_deriv hc Q r)

lemma aux_ihq_pos {G : ℝ → ℝ} {y0 : ℝ} (hanti : StrictAntiOn G (Set.Iic y0))
    (hmono : StrictMonoOn G (Set.Ici y0))
    {Q r : ℝ} (hQ : 0 < Q) (h : G (r + Q) = G r) : r < y0 ∧ y0 < r + Q := by
  constructor
  · by_contra hc; push Not at hc
    have := hmono (Set.mem_Ici.2 hc) (Set.mem_Ici.2 (by linarith)) (by linarith : r < r + Q)
    linarith
  · by_contra hc; push Not at hc
    have := hanti (Set.mem_Iic.2 (by linarith)) (Set.mem_Iic.2 hc) (by linarith : r < r + Q)
    linarith

lemma aux_ihq_exists {G : ℝ → ℝ} {y0 : ℝ} (hc : Continuous G)
    (hanti : StrictAntiOn G (Set.Iic y0)) (hmono : StrictMonoOn G (Set.Ici y0))
    {Q : ℝ} (hQ : 0 < Q) :
    ∃ r, ∀ r' : ℝ, (∫ y in r..r + Q, G y) ≤ ∫ y in r'..r' + Q, G y := by
  set φ : ℝ → ℝ := fun t => G (t + Q) - G t with hφ
  have hφc : Continuous φ := (hc.comp (continuous_id.add continuous_const)).sub hc
  have ha : φ (y0 - Q) ≤ 0 := by
    have := hanti (Set.mem_Iic.2 (by linarith : y0 - Q ≤ y0)) (Set.mem_Iic.2 le_rfl)
      (by linarith : y0 - Q < y0)
    simp only [hφ, sub_add_cancel]; linarith
  have hb : 0 ≤ φ y0 := by
    have := hmono (Set.mem_Ici.2 le_rfl) (Set.mem_Ici.2 (by linarith : y0 ≤ y0 + Q))
      (by linarith : y0 < y0 + Q)
    simp only [hφ]; linarith
  obtain ⟨r, hr, hr0⟩ := intermediate_value_Icc (by linarith : y0 - Q ≤ y0) hφc.continuousOn
    ⟨ha, hb⟩
  simp only [hφ] at hr0
  have hry : r ≤ y0 := hr.2
  have hry' : y0 ≤ r + Q := by linarith [hr.1]
  have hpos : ∀ t, r ≤ t → 0 ≤ G (t + Q) - G t := by
    intro t ht
    rcases le_total t y0 with h1 | h1
    · have e1 : G t ≤ G r := hanti.antitoneOn (Set.mem_Iic.2 hry) (Set.mem_Iic.2 h1) ht
      have e2 : G (r + Q) ≤ G (t + Q) :=
        hmono.monotoneOn (Set.mem_Ici.2 hry') (Set.mem_Ici.2 (by linarith)) (by linarith)
      linarith
    · have := hmono.monotoneOn (Set.mem_Ici.2 h1) (Set.mem_Ici.2 (by linarith))
        (by linarith : t ≤ t + Q)
      linarith
  have hneg : ∀ t, t ≤ r → G (t + Q) - G t ≤ 0 := by
    intro t ht
    rcases le_total (t + Q) y0 with h1 | h1
    · have := hanti.antitoneOn (Set.mem_Iic.2 (by linarith)) (Set.mem_Iic.2 h1)
        (by linarith : t ≤ t + Q)
      linarith
    · have e1 : G (t + Q) ≤ G (r + Q) :=
        hmono.monotoneOn (Set.mem_Ici.2 h1) (Set.mem_Ici.2 hry') (by linarith)
      have e2 : G r ≤ G t := hanti.antitoneOn (Set.mem_Iic.2 (by linarith)) (Set.mem_Iic.2 hry) ht
      linarith
  have hcont : Continuous (fun r => ∫ y in r..r + Q, G y) :=
    continuous_iff_continuousAt.2 fun x => (aux_ihq_deriv hc Q x).continuousAt
  refine ⟨r, fun r' => ?_⟩
  rcases lt_trichotomy r r' with h | h | h
  · obtain ⟨c, hc', hceq⟩ := exists_hasDerivAt_eq_slope (fun r => ∫ y in r..r + Q, G y)
      (fun t => G (t + Q) - G t) h hcont.continuousOn (fun x _ => aux_ihq_deriv hc Q x)
    have h1 := hpos c hc'.1.le
    rw [hceq] at h1
    have hd : 0 < r' - r := by linarith
    have := (le_div_iff₀ hd).1 h1
    simp only [zero_mul] at this
    linarith
  · rw [h]
  · obtain ⟨c, hc', hceq⟩ := exists_hasDerivAt_eq_slope (fun r => ∫ y in r..r + Q, G y)
      (fun t => G (t + Q) - G t) h hcont.continuousOn (fun x _ => aux_ihq_deriv hc Q x)
    have h1 := hneg c hc'.2.le
    rw [hceq] at h1
    have hd : 0 < r - r' := by linarith
    have := (div_le_iff₀ hd).1 h1
    simp only [zero_mul] at this
    linarith

lemma aux_ihq_optmin {G : ℝ → ℝ} {y0 : ℝ} (hc : Continuous G)
    (hanti : StrictAntiOn G (Set.Iic y0)) (hmono : StrictMonoOn G (Set.Ici y0))
    {Q : ℝ} (hQ : 0 < Q) :
    ∀ r', (∫ y in optReorder G Q..optReorder G Q + Q, G y) ≤ ∫ y in r'..r' + Q, G y := by
  have hex := aux_ihq_exists hc hanti hmono hQ
  simp only [optReorder, dif_pos hex]
  exact hex.choose_spec

lemma aux_ihq_opteq {G : ℝ → ℝ} {y0 : ℝ} (hc : Continuous G)
    (hanti : StrictAntiOn G (Set.Iic y0)) (hmono : StrictMonoOn G (Set.Ici y0))
    {Q : ℝ} (hQ : 0 < Q) :
    G (optReorder G Q + Q) = G (optReorder G Q) := by
  have := aux_ihq_crit hc (aux_ihq_optmin hc hanti hmono hQ)
  linarith

lemma aux_ihq_optpos {G : ℝ → ℝ} {y0 : ℝ} (hc : Continuous G)
    (hanti : StrictAntiOn G (Set.Iic y0)) (hmono : StrictMonoOn G (Set.Ici y0))
    {Q : ℝ} (hQ : 0 < Q) :
    optReorder G Q < y0 ∧ y0 < optReorder G Q + Q :=
  aux_ihq_pos hanti hmono hQ (aux_ihq_opteq hc hanti hmono hQ)

lemma aux_ihq_optmono {G : ℝ → ℝ} {y0 : ℝ} (hc : Continuous G)
    (hanti : StrictAntiOn G (Set.Iic y0)) (hmono : StrictMonoOn G (Set.Ici y0))
    {Q Q' : ℝ} (hQ : 0 < Q) (hQQ : Q < Q') :
    optReorder G Q' ≤ optReorder G Q ∧ optReorder G Q + Q ≤ optReorder G Q' + Q' := by
  have hQ' : 0 < Q' := by linarith
  have e1 := aux_ihq_opteq hc hanti hmono hQ
  have e2 := aux_ihq_opteq hc hanti hmono hQ'
  obtain ⟨p1, p2⟩ := aux_ihq_optpos hc hanti hmono hQ
  obtain ⟨p3, p4⟩ := aux_ihq_optpos hc hanti hmono hQ'
  set a := optReorder G Q
  set a' := optReorder G Q'
  constructor
  · by_contra hcon; push Not at hcon
    have i1 := hanti (Set.mem_Iic.2 p1.le) (Set.mem_Iic.2 p3.le) hcon
    have i2 := hmono (Set.mem_Ici.2 p2.le) (Set.mem_Ici.2 p4.le) (by linarith : a + Q < a' + Q')
    linarith
  · by_contra hcon; push Not at hcon
    have i2 := hmono (Set.mem_Ici.2 p4.le) (Set.mem_Ici.2 p2.le) hcon
    have i1 := hanti (Set.mem_Iic.2 p3.le) (Set.mem_Iic.2 p1.le) (by linarith : a' < a)
    linarith

lemma aux_ihq_bounds {G : ℝ → ℝ} {y0 : ℝ} (hc : Continuous G)
    (hanti : StrictAntiOn G (Set.Iic y0)) (hmono : StrictMonoOn G (Set.Ici y0))
    (hmp : minPoint G = y0) {s t : ℝ} (hs : 0 ≤ s) (hst : s < t) :
    Hfun G s * (t - s) ≤
        (∫ y in optReorder G t..optReorder G t + t, G y) -
          (∫ y in optReorder G s..optReorder G s + s, G y) ∧
      (∫ y in optReorder G t..optReorder G t + t, G y) -
          (∫ y in optReorder G s..optReorder G s + s, G y) ≤ Hfun G t * (t - s) := by
  have ht : 0 < t := by linarith
  have hgm : ∀ x, G y0 ≤ G x := by
    intro x
    rcases le_total x y0 with h1 | h1
    · exact hanti.antitoneOn (Set.mem_Iic.2 h1) (Set.mem_Iic.2 le_rfl) h1
    · exact hmono.monotoneOn (Set.mem_Ici.2 le_rfl) (Set.mem_Ici.2 h1) h1
  have hII : ∀ a b, IntervalIntegrable G volume a b := fun a b => hc.intervalIntegrable a b
  have hIc : ∀ (c : ℝ) a b, IntervalIntegrable (fun _ => c) volume a b :=
    fun c a b => intervalIntegrable_const
  have e2 := aux_ihq_opteq hc hanti hmono ht
  obtain ⟨p3, p4⟩ := aux_ihq_optpos hc hanti hmono ht
  have Ht : Hfun G t = G (optReorder G t) := by simp [Hfun, ht]
  rw [Ht]
  set a' := optReorder G t
  rcases eq_or_lt_of_le hs with h0 | h0
  · subst h0
    have H0 : Hfun G 0 = G y0 := by simp [Hfun, hmp]
    rw [H0]
    simp only [add_zero, intervalIntegral.integral_same, sub_zero]
    constructor
    · have := intervalIntegral.integral_mono_on (by linarith : a' ≤ a' + t) (hIc (G y0) _ _)
        (hII _ _) (fun x _ => hgm x)
      simp only [intervalIntegral.integral_const, smul_eq_mul] at this
      linarith
    · have := intervalIntegral.integral_mono_on (by linarith : a' ≤ a' + t) (hII _ _)
        (hIc (G a') _ _) (fun x hx => by
          rcases le_total x y0 with h1 | h1
          · exact hanti.antitoneOn (Set.mem_Iic.2 p3.le) (Set.mem_Iic.2 h1) hx.1
          · rw [← e2]
            exact hmono.monotoneOn (Set.mem_Ici.2 h1) (Set.mem_Ici.2 p4.le) hx.2)
      simp only [intervalIntegral.integral_const, smul_eq_mul] at this
      linarith
  · have Hs : Hfun G s = G (optReorder G s) := by simp [Hfun, h0]
    rw [Hs]
    have e1 := aux_ihq_opteq hc hanti hmono h0
    obtain ⟨p1, p2⟩ := aux_ihq_optpos hc hanti hmono h0
    obtain ⟨m1, m2⟩ := aux_ihq_optmono hc hanti hmono h0 hst
    set a := optReorder G s
    have split : (∫ y in a'..a' + t, G y) - (∫ y in a..a + s, G y) =
        (∫ y in a'..a, G y) + ∫ y in a + s..a' + t, G y := by
      rw [← intervalIntegral.integral_add_adjacent_intervals (hII a' a) (hII a (a' + t)),
        ← intervalIntegral.integral_add_adjacent_intervals (hII a (a + s)) (hII (a + s) (a' + t))]
      ring
    rw [split]
    -- bounds on [a', a]
    have L1 := intervalIntegral.integral_mono_on m1 (hIc (G a) _ _) (hII _ _)
      (fun x hx => hanti.antitoneOn (Set.mem_Iic.2 (le_trans hx.2 p1.le)) (Set.mem_Iic.2 p1.le) hx.2)
    have U1 := intervalIntegral.integral_mono_on m1 (hII _ _) (hIc (G a') _ _)
      (fun x hx => hanti.antitoneOn (Set.mem_Iic.2 p3.le) (Set.mem_Iic.2 (le_trans hx.2 p1.le)) hx.1)
    have L2 := intervalIntegral.integral_mono_on m2 (hIc (G a) _ _) (hII _ _)
      (fun x hx => by
        rw [← e1]
        exact hmono.monotoneOn (Set.mem_Ici.2 p2.le) (Set.mem_Ici.2 (le_trans p2.le hx.1)) hx.1)
    have U2 := intervalIntegral.integral_mono_on m2 (hII _ _) (hIc (G a') _ _)
      (fun x hx => by
        rw [← e2]
        exact hmono.monotoneOn (Set.mem_Ici.2 (le_trans p2.le hx.1)) (Set.mem_Ici.2 p4.le) hx.2)
    simp only [intervalIntegral.integral_const, smul_eq_mul] at L1 U1 L2 U2
    constructor <;> nlinarith

lemma aux_ihq_riemann {F H : ℝ → ℝ} {Q : ℝ} (hQ : 0 < Q) (hH : MonotoneOn H (Set.Icc 0 Q))
    (hF : ∀ s t, 0 ≤ s → s < t → t ≤ Q →
      H s * (t - s) ≤ F t - F s ∧ F t - F s ≤ H t * (t - s))
    (hF0 : F 0 = 0) : F Q = ∫ y in (0:ℝ)..Q, H y := by
  have hint : ∀ s t, 0 ≤ s → s ≤ t → t ≤ Q → IntervalIntegrable H volume s t := by
    intro s t hs hst htQ
    apply MonotoneOn.intervalIntegrable
    apply hH.mono
    rw [Set.uIcc_of_le hst]
    exact Set.Icc_subset_Icc hs htQ
  set Φ : ℝ → ℝ := fun t => F t - ∫ y in (0:ℝ)..t, H y with hΦ
  have key : ∀ s t, 0 ≤ s → s ≤ t → t ≤ Q → |Φ t - Φ s| ≤ (H t - H s) * (t - s) := by
    intro s t hs hst htQ
    rcases eq_or_lt_of_le hst with h | h
    · subst h; simp
    have hsub : (∫ y in (0:ℝ)..t, H y) - (∫ y in (0:ℝ)..s, H y) = ∫ y in s..t, H y :=
      intervalIntegral.integral_interval_sub_left (hint 0 t le_rfl (by linarith) htQ)
        (hint 0 s le_rfl hs (by linarith))
    have hL := intervalIntegral.integral_mono_on hst (intervalIntegrable_const) (hint s t hs hst htQ)
      (fun x hx => hH ⟨hs, by linarith [hx.1]⟩ ⟨by linarith [hx.1], le_trans hx.2 htQ⟩ hx.1
        : ∀ x ∈ Set.Icc s t, (fun _ => H s) x ≤ H x)
    have hU := intervalIntegral.integral_mono_on hst (hint s t hs hst htQ) (intervalIntegrable_const)
      (fun x hx => hH ⟨by linarith [hx.1], le_trans hx.2 htQ⟩ ⟨by linarith, htQ⟩ hx.2
        : ∀ x ∈ Set.Icc s t, H x ≤ (fun _ => H t) x)
    simp only [intervalIntegral.integral_const, smul_eq_mul] at hL hU
    obtain ⟨b1, b2⟩ := hF s t hs h htQ
    have : Φ t - Φ s = (F t - F s) - ∫ y in s..t, H y := by
      simp only [hΦ]; rw [← hsub]; ring
    rw [this, abs_le]
    constructor <;> nlinarith
  have hΦ0 : Φ 0 = 0 := by simp [hΦ, hF0]
  have hbound : ∀ n : ℕ, 0 < n → |Φ Q| ≤ Q * (H Q - H 0) / n := by
    intro n hn
    have hn' : (0 : ℝ) < n := by exact_mod_cast hn
    set tt : ℕ → ℝ := fun i => Q * i / n with htt
    have htt0 : ∀ i, 0 ≤ tt i := fun i => by positivity
    have httQ : ∀ i, i ≤ n → tt i ≤ Q := by
      intro i hi
      simp only [htt]
      rw [div_le_iff₀ hn']
      have : (i : ℝ) ≤ n := by exact_mod_cast hi
      nlinarith
    have httmono : ∀ i, tt i ≤ tt (i + 1) := by
      intro i; simp only [htt]; push_cast
      apply div_le_div_of_nonneg_right _ hn'.le; nlinarith
    have httd : ∀ i, tt (i + 1) - tt i = Q / n := by
      intro i; simp only [htt]; push_cast; field_simp; ring
    have htel : Φ Q - Φ 0 = ∑ i ∈ Finset.range n, (Φ (tt (i + 1)) - Φ (tt i)) := by
      rw [Finset.sum_range_sub (fun i => Φ (tt i)) n]
      simp only [htt]
      congr 2
      · field_simp
      · simp
    have htelH : H Q - H 0 = ∑ i ∈ Finset.range n, (H (tt (i + 1)) - H (tt i)) := by
      rw [Finset.sum_range_sub (fun i => H (tt i)) n]
      simp only [htt]
      congr 2
      · field_simp
      · simp
    rw [hΦ0, sub_zero] at htel
    rw [htel]
    calc |∑ i ∈ Finset.range n, (Φ (tt (i + 1)) - Φ (tt i))|
        ≤ ∑ i ∈ Finset.range n, |Φ (tt (i + 1)) - Φ (tt i)| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ i ∈ Finset.range n, (H (tt (i + 1)) - H (tt i)) * (Q / n) := by
          apply Finset.sum_le_sum
          intro i hi
          rw [← httd i]
          apply key _ _ (htt0 i) (httmono i)
          apply httQ
          have := Finset.mem_range.1 hi
          omega
      _ = Q * (H Q - H 0) / n := by
          rw [← Finset.sum_mul, ← htelH]; ring
  by_contra hne
  have hpos : 0 < |Φ Q| := abs_pos.2 (by
    intro h0; apply hne; simp only [hΦ] at h0; linarith)
  obtain ⟨n, hn⟩ := exists_nat_gt (Q * (H Q - H 0) / |Φ Q|)
  have hn0 : 0 < n := by
    have : 0 ≤ Q * (H Q - H 0) / |Φ Q| := by
      apply div_nonneg _ hpos.le
      apply mul_nonneg hQ.le
      have := hH ⟨le_rfl, hQ.le⟩ ⟨hQ.le, le_rfl⟩ hQ.le
      linarith
    have : (0 : ℝ) < n := by linarith
    exact_mod_cast this
  have hb := hbound n hn0
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn0
  rw [div_lt_iff₀ hpos] at hn
  rw [le_div_iff₀ hn'] at hb
  linarith

/-! ### Properties of the newsvendor cost `G`. -/

lemma aux_ihq_int {lam L h p : ℝ} {μ : Measure ℝ} (hμ : IsLeadtimeDemand lam L μ) (y : ℝ) :
    Integrable (fun x => h * max (y - x) 0 + p * max (x - y) 0) μ := by
  have := hμ.isProb
  have h1 : Integrable (fun x : ℝ => y - x) μ := (integrable_const y).sub hμ.integrable
  have h2 : Integrable (fun x : ℝ => x - y) μ := hμ.integrable.sub (integrable_const y)
  exact (h1.pos_part.const_mul h).add (h2.pos_part.const_mul p)

lemma aux_ihq_maxconv (u v a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    max (a * u + b * v) 0 ≤ a * max u 0 + b * max v 0 := by
  apply max_le
  · have := mul_le_mul_of_nonneg_left (le_max_left u 0) ha
    have := mul_le_mul_of_nonneg_left (le_max_left v 0) hb
    linarith
  · have := mul_nonneg ha (le_max_right u 0)
    have := mul_nonneg hb (le_max_right v 0)
    linarith

lemma aux_ihq_conv {lam L h p : ℝ} {μ : Measure ℝ} (hμ : IsLeadtimeDemand lam L μ)
    (hh : 0 ≤ h) (hp : 0 ≤ p) (y z a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1) :
    newsvendorCost h p μ (a * y + b * z) ≤
      a * newsvendorCost h p μ y + b * newsvendorCost h p μ z := by
  unfold newsvendorCost
  rw [← integral_const_mul, ← integral_const_mul, ← integral_add]
  · apply integral_mono (aux_ihq_int hμ _)
    · exact ((aux_ihq_int hμ y).const_mul a).add ((aux_ihq_int hμ z).const_mul b)
    · intro x
      have e1 : a * y + b * z - x = a * (y - x) + b * (z - x) := by
        have : x = a * x + b * x := by rw [← add_mul, hab, one_mul]
        linarith [this]
      have e2 : x - (a * y + b * z) = a * (x - y) + b * (x - z) := by
        have : x = a * x + b * x := by rw [← add_mul, hab, one_mul]
        linarith [this]
      simp only
      rw [e1, e2]
      have m1 := mul_le_mul_of_nonneg_left (aux_ihq_maxconv (y - x) (z - x) a b ha hb) hh
      have m2 := mul_le_mul_of_nonneg_left (aux_ihq_maxconv (x - y) (x - z) a b ha hb) hp
      nlinarith
  · exact (aux_ihq_int hμ y).const_mul a
  · exact (aux_ihq_int hμ z).const_mul b

lemma aux_ihq_lip {lam L h p : ℝ} {μ : Measure ℝ} (hμ : IsLeadtimeDemand lam L μ)
    (hh : 0 ≤ h) (hp : 0 ≤ p) (y z : ℝ) :
    |newsvendorCost h p μ y - newsvendorCost h p μ z| ≤ (h + p) * |y - z| := by
  have := hμ.isProb
  unfold newsvendorCost
  rw [← integral_sub (aux_ihq_int hμ y) (aux_ihq_int hμ z)]
  have hpt : ∀ x : ℝ, |(h * max (y - x) 0 + p * max (x - y) 0) -
      (h * max (z - x) 0 + p * max (x - z) 0)| ≤ (h + p) * |y - z| := by
    intro x
    have a1 : |max (y - x) 0 - max (z - x) 0| ≤ |y - z| := by
      have := abs_max_sub_max_le_abs (y - x) (z - x) 0
      rwa [show y - x - (z - x) = y - z by ring] at this
    have a2 : |max (x - y) 0 - max (x - z) 0| ≤ |y - z| := by
      have := abs_max_sub_max_le_abs (x - y) (x - z) 0
      rwa [show x - y - (x - z) = -(y - z) by ring, abs_neg] at this
    have : (h * max (y - x) 0 + p * max (x - y) 0) - (h * max (z - x) 0 + p * max (x - z) 0)
        = h * (max (y - x) 0 - max (z - x) 0) + p * (max (x - y) 0 - max (x - z) 0) := by ring
    rw [this]
    calc _ ≤ |h * (max (y - x) 0 - max (z - x) 0)| + |p * (max (x - y) 0 - max (x - z) 0)| :=
          abs_add_le _ _
      _ = h * |max (y - x) 0 - max (z - x) 0| + p * |max (x - y) 0 - max (x - z) 0| := by
          rw [abs_mul, abs_mul, abs_of_nonneg hh, abs_of_nonneg hp]
      _ ≤ h * |y - z| + p * |y - z| := by
          have := mul_le_mul_of_nonneg_left a1 hh
          have := mul_le_mul_of_nonneg_left a2 hp
          linarith
      _ = (h + p) * |y - z| := by ring
  calc |∫ x, ((h * max (y - x) 0 + p * max (x - y) 0) -
          (h * max (z - x) 0 + p * max (x - z) 0)) ∂μ|
      ≤ ∫ x, |(h * max (y - x) 0 + p * max (x - y) 0) -
          (h * max (z - x) 0 + p * max (x - z) 0)| ∂μ := abs_integral_le_integral_abs
    _ ≤ ∫ x, (h + p) * |y - z| ∂μ := by
        apply integral_mono
        · exact ((aux_ihq_int hμ y).sub (aux_ihq_int hμ z)).abs
        · exact integrable_const _
        · intro x; exact hpt x
    _ = (h + p) * |y - z| := by simp

lemma aux_ihq_cont {lam L h p : ℝ} {μ : Measure ℝ} (hμ : IsLeadtimeDemand lam L μ)
    (hh : 0 ≤ h) (hp : 0 ≤ p) : Continuous (newsvendorCost h p μ) := by
  rw [Metric.continuous_iff]
  intro b ε hε
  refine ⟨ε / (h + p + 1), by positivity, fun a ha => ?_⟩
  rw [Real.dist_eq] at ha ⊢
  have := aux_ihq_lip hμ hh hp a b
  have h1 : (h + p) * |a - b| ≤ (h + p + 1) * |a - b| := by
    have := abs_nonneg (a - b); nlinarith
  have h2 : (h + p + 1) * |a - b| < ε := by
    rw [lt_div_iff₀ (by positivity)] at ha; linarith
  linarith

lemma aux_ihq_strict {G : ℝ → ℝ}
    (hconv : ∀ y z a b : ℝ, 0 ≤ a → 0 ≤ b → a + b = 1 → G (a * y + b * z) ≤ a * G y + b * G z)
    {y0 : ℝ} (hmin : ∀ z, z ≠ y0 → G y0 < G z) {s t a b : ℝ} (ha : 0 < a) (hb : 0 ≤ b)
    (hab : a + b = 1) (hs : s = a * y0 + b * t) (ht : t ≠ y0) : G s < G t := by
  have h1 := hconv y0 t a b ha.le hb hab
  have h2 := hmin t ht
  rw [hs]
  have : a * G y0 < a * G t := mul_lt_mul_of_pos_left h2 ha
  have e : G t = a * G t + b * G t := by rw [← add_mul, hab, one_mul]
  linarith

lemma aux_ihq_shape {G : ℝ → ℝ}
    (hconv : ∀ y z a b : ℝ, 0 ≤ a → 0 ≤ b → a + b = 1 → G (a * y + b * z) ≤ a * G y + b * G z)
    {y0 : ℝ} (hmin : ∀ z, z ≠ y0 → G y0 < G z) :
    StrictAntiOn G (Set.Iic y0) ∧ StrictMonoOn G (Set.Ici y0) := by
  constructor
  · intro s hs t ht hst
    simp only [Set.mem_Iic] at hs ht
    have hd : 0 < y0 - s := by linarith
    apply aux_ihq_strict hconv hmin (a := (t - s) / (y0 - s)) (b := (y0 - t) / (y0 - s))
    · exact div_pos (by linarith) hd
    · exact div_nonneg (by linarith) hd.le
    · field_simp; ring
    · field_simp; ring
    · exact ne_of_lt (by linarith)
  · intro s hs t ht hst
    simp only [Set.mem_Ici] at hs ht
    have hd : 0 < t - y0 := by linarith
    apply aux_ihq_strict hconv hmin (a := (t - s) / (t - y0)) (b := (s - y0) / (t - y0))
    · exact div_pos (by linarith) hd
    · exact div_nonneg (by linarith) hd.le
    · field_simp; ring
    · field_simp; ring
    · exact ne_of_gt (by linarith)


/-! ### Abstract setting for Theorem 2. -/

structure aux_oqb_Good (G : ℝ → ℝ) (h p m y0 : ℝ) : Prop where
  hh : 0 < h
  hp : 0 < p
  cont : Continuous G
  anti : StrictAntiOn G (Set.Iic y0)
  mono : StrictMonoOn G (Set.Ici y0)
  mp : minPoint G = y0
  conv : ∀ y z a b : ℝ, 0 ≤ a → 0 ≤ b → a + b = 1 → G (a * y + b * z) ≤ a * G y + b * G z
  up : ∀ x y, x ≤ y → G y ≤ G x + h * (y - x)
  dn : ∀ x y, x ≤ y → G x ≤ G y + p * (y - x)
  lb1 : ∀ y, h * (y - m) ≤ G y
  lb2 : ∀ y, p * (m - y) ≤ G y

noncomputable def aux_oqb_R (G : ℝ → ℝ) (y0 Q : ℝ) : ℝ := if 0 < Q then optReorder G Q else y0

section abs
variable {G : ℝ → ℝ} {h p m y0 : ℝ}

lemma aux_oqb_cost (hG : aux_oqb_Good G h p m y0) (lam K : ℝ) {Q : ℝ} (hQ : 0 < Q) :
    optCost G lam K Q = (lam * K + ∫ y in (0 : ℝ)..Q, Hfun G y) / Q := by
  have hanti := hG.anti
  have hmono := hG.mono
  have hc := hG.cont
  have hmp := hG.mp
  set F : ℝ → ℝ := fun t => ∫ y in optReorder G t..optReorder G t + t, G y with hF
  have hF0 : F 0 = 0 := by simp [hF]
  have hB : ∀ s t, 0 ≤ s → s < t →
      Hfun G s * (t - s) ≤ F t - F s ∧ F t - F s ≤ Hfun G t * (t - s) :=
    fun s t hs hst => aux_ihq_bounds hc hanti hmono hmp hs hst
  have hHm : MonotoneOn (Hfun G) (Set.Icc 0 Q) := by
    intro s hs t ht hst
    rcases eq_or_lt_of_le hst with h | h
    · rw [h]
    · have := hB s t hs.1 h
      have hd : 0 < t - s := by linarith
      have : Hfun G s * (t - s) ≤ Hfun G t * (t - s) := le_trans this.1 this.2
      exact le_of_mul_le_mul_right this hd
  have key : F Q = ∫ y in (0:ℝ)..Q, Hfun G y :=
    aux_ihq_riemann hQ hHm (fun s t hs hst _ => hB s t hs hst) hF0
  simp only [optCost, qrCost]
  rw [← key]

lemma aux_oqb_g0 (hG : aux_oqb_Good G h p m y0) : 0 ≤ G y0 := by
  have h1 := hG.lb1 y0
  have h2 := hG.lb2 y0
  rcases le_total y0 m with h3 | h3
  · have := mul_nonneg hG.hp.le (sub_nonneg.2 h3); linarith
  · have := mul_nonneg hG.hh.le (sub_nonneg.2 h3); linarith

lemma aux_oqb_H_eq (hG : aux_oqb_Good G h p m y0) (Q : ℝ) : Hfun G Q = G (aux_oqb_R G y0 Q) := by
  unfold Hfun aux_oqb_R
  split_ifs <;> simp [hG.mp]

lemma aux_oqb_H0_eq (hG : aux_oqb_Good G h p m y0) (Q : ℝ) : H0fun G Q = Hfun G Q - G y0 := by
  simp [H0fun, hG.mp]

lemma aux_oqb_Rprop (hG : aux_oqb_Good G h p m y0) {Q : ℝ} (hQ : 0 ≤ Q) :
    aux_oqb_R G y0 Q ≤ y0 ∧ y0 ≤ aux_oqb_R G y0 Q + Q ∧
      G (aux_oqb_R G y0 Q + Q) = G (aux_oqb_R G y0 Q) := by
  rcases eq_or_lt_of_le hQ with h0 | h0
  · subst h0; simp [aux_oqb_R]
  · simp only [aux_oqb_R, if_pos h0]
    obtain ⟨a, b⟩ := aux_ihq_optpos hG.cont hG.anti hG.mono h0
    exact ⟨a.le, b.le, aux_ihq_opteq hG.cont hG.anti hG.mono h0⟩

lemma aux_oqb_Rpos (hG : aux_oqb_Good G h p m y0) {Q : ℝ} (hQ : 0 < Q) :
    aux_oqb_R G y0 Q < y0 := by
  simp only [aux_oqb_R, if_pos hQ]
  exact (aux_ihq_optpos hG.cont hG.anti hG.mono hQ).1

lemma aux_oqb_Rmono (hG : aux_oqb_Good G h p m y0) {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) :
    aux_oqb_R G y0 t ≤ aux_oqb_R G y0 s ∧ aux_oqb_R G y0 s + s ≤ aux_oqb_R G y0 t + t := by
  rcases eq_or_lt_of_le hst with h1 | h1
  · subst h1; exact ⟨le_rfl, le_rfl⟩
  rcases eq_or_lt_of_le hs with h0 | h0
  · subst h0
    obtain ⟨a, b, -⟩ := aux_oqb_Rprop hG (le_of_lt h1)
    simp only [aux_oqb_R, lt_irrefl, if_false, add_zero]
    simp only [aux_oqb_R] at a b
    exact ⟨a, b⟩
  · have ht : 0 < t := by linarith
    simp only [aux_oqb_R, if_pos h0, if_pos ht]
    exact aux_ihq_optmono hG.cont hG.anti hG.mono h0 h1

lemma aux_oqb_lip (hG : aux_oqb_Good G h p m y0) {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) :
    (h + p) * (Hfun G t - Hfun G s) ≤ h * p * (t - s) := by
  obtain ⟨m1, m2⟩ := aux_oqb_Rmono hG hs hst
  obtain ⟨a1, b1, e1⟩ := aux_oqb_Rprop hG hs
  obtain ⟨a2, b2, e2⟩ := aux_oqb_Rprop hG (le_trans hs hst)
  rw [aux_oqb_H_eq hG, aux_oqb_H_eq hG]
  set a := aux_oqb_R G y0 s
  set a' := aux_oqb_R G y0 t
  have i1 := hG.dn a' a m1
  have i2 := hG.up (a + s) (a' + t) m2
  rw [e1, e2] at i2
  have hh := hG.hh
  have hp := hG.hp
  have j1 := mul_le_mul_of_nonneg_left i1 hh.le
  have j2 := mul_le_mul_of_nonneg_left i2 hp.le
  nlinarith

lemma aux_oqb_lower (hG : aux_oqb_Good G h p m y0) {Q : ℝ} (hQ : 0 ≤ Q) :
    h * p * Q ≤ (h + p) * Hfun G Q := by
  obtain ⟨a1, b1, e1⟩ := aux_oqb_Rprop hG hQ
  rw [aux_oqb_H_eq hG]
  set a := aux_oqb_R G y0 Q
  have i1 := hG.lb1 (a + Q)
  have i2 := hG.lb2 a
  rw [e1] at i1
  have j1 := mul_le_mul_of_nonneg_left i1 hG.hp.le
  have j2 := mul_le_mul_of_nonneg_left i2 hG.hh.le
  nlinarith

lemma aux_oqb_smono (hG : aux_oqb_Good G h p m y0) {s t : ℝ} (hs : 0 ≤ s) (hst : s < t) :
    Hfun G s < Hfun G t := by
  have ht : 0 < t := by linarith
  obtain ⟨m1, m2⟩ := aux_oqb_Rmono hG hs hst.le
  obtain ⟨a1, b1, e1⟩ := aux_oqb_Rprop hG hs
  obtain ⟨a2, b2, e2⟩ := aux_oqb_Rprop hG ht.le
  rw [aux_oqb_H_eq hG, aux_oqb_H_eq hG]
  rcases eq_or_lt_of_le m1 with h1 | h1
  · rw [← e1, ← e2]
    apply hG.mono (Set.mem_Ici.2 b1) (Set.mem_Ici.2 b2)
    rw [h1]; linarith
  · exact hG.anti (Set.mem_Iic.2 a2) (Set.mem_Iic.2 a1) h1

lemma aux_oqb_conv_side (hG : aux_oqb_Good G h p m y0) {x x' z : ℝ}
    (h1 : min x z ≤ x') (h2 : x' ≤ max x z) :
    (G x' - G z) * |z - x| ≤ |z - x'| * (G x - G z) := by
  rcases eq_or_ne x z with hxz | hxz
  · subst hxz
    have : x' = x := le_antisymm (by simpa using h2) (by simpa using h1)
    subst this; simp
  have hd : 0 < |z - x| := abs_pos.2 (sub_ne_zero.2 (Ne.symm hxz))
  set θ := |z - x'| / |z - x| with hθ
  have hθ0 : 0 ≤ θ := div_nonneg (abs_nonneg _) hd.le
  rcases lt_or_gt_of_ne hxz with hl | hl
  · rw [min_eq_left hl.le] at h1; rw [max_eq_right hl.le] at h2
    have e1 : |z - x| = z - x := abs_of_pos (by linarith)
    have e2 : |z - x'| = z - x' := abs_of_nonneg (by linarith)
    have hθ1 : 1 - θ = (x' - x) / (z - x) := by
      rw [hθ, e1, e2]; field_simp; ring
    have hx' : x' = θ * x + (1 - θ) * z := by
      rw [hθ1, hθ, e1, e2]; field_simp; ring
    have hc := hG.conv x z θ (1 - θ) hθ0 (by rw [hθ1]; exact div_nonneg (by linarith) (by linarith))
      (by ring)
    rw [← hx'] at hc
    have : G x' - G z ≤ θ * (G x - G z) := by linarith
    have := mul_le_mul_of_nonneg_right this hd.le
    calc (G x' - G z) * |z - x| ≤ θ * (G x - G z) * |z - x| := this
      _ = |z - x'| * (G x - G z) := by rw [hθ]; field_simp
  · rw [min_eq_right hl.le] at h1; rw [max_eq_left hl.le] at h2
    have e1 : |z - x| = x - z := by rw [abs_sub_comm]; exact abs_of_pos (by linarith)
    have e2 : |z - x'| = x' - z := by rw [abs_sub_comm]; exact abs_of_nonneg (by linarith)
    have hθ1 : 1 - θ = (x - x') / (x - z) := by
      rw [hθ, e1, e2]; field_simp; ring
    have hx' : x' = θ * x + (1 - θ) * z := by
      rw [hθ1, hθ, e1, e2]; field_simp; ring
    have hc := hG.conv x z θ (1 - θ) hθ0 (by rw [hθ1]; exact div_nonneg (by linarith) (by linarith))
      (by ring)
    rw [← hx'] at hc
    have : G x' - G z ≤ θ * (G x - G z) := by linarith
    have := mul_le_mul_of_nonneg_right this hd.le
    calc (G x' - G z) * |z - x| ≤ θ * (G x - G z) * |z - x| := this
      _ = |z - x'| * (G x - G z) := by rw [hθ]; field_simp

lemma aux_oqb_ratio (hG : aux_oqb_Good G h p m y0) {y Q : ℝ} (hy : 0 ≤ y) (hyQ : y ≤ Q) :
    (Hfun G y - G y0) * Q ≤ y * (Hfun G Q - G y0) := by
  have hQ : 0 ≤ Q := le_trans hy hyQ
  obtain ⟨m1, m2⟩ := aux_oqb_Rmono hG hy hyQ
  obtain ⟨a1, b1, e1⟩ := aux_oqb_Rprop hG hy
  obtain ⟨a2, b2, e2⟩ := aux_oqb_Rprop hG hQ
  rw [aux_oqb_H_eq hG, aux_oqb_H_eq hG]
  set a := aux_oqb_R G y0 y
  set a' := aux_oqb_R G y0 Q
  have L := aux_oqb_conv_side hG (x := a') (x' := a) (z := y0) (by simp [m1]) (by simp [a1])
  have R := aux_oqb_conv_side hG (x := a' + Q) (x' := a + y) (z := y0) (by simp [b1])
    (by simp [m2])
  rw [abs_of_nonneg (by linarith : (0:ℝ) ≤ y0 - a'), abs_of_nonneg (by linarith : (0:ℝ) ≤ y0 - a)]
    at L
  rw [abs_sub_comm, abs_of_nonneg (by linarith : (0:ℝ) ≤ a' + Q - y0), abs_sub_comm,
    abs_of_nonneg (by linarith : (0:ℝ) ≤ a + y - y0), e1, e2] at R
  nlinarith

lemma aux_oqb_Hmax (hG : aux_oqb_Good G h p m y0) (Q : ℝ) : Hfun G Q = Hfun G (max Q 0) := by
  rcases le_total Q 0 with h1 | h1
  · rw [max_eq_right h1]
    simp [Hfun, not_lt.2 h1]
  · rw [max_eq_left h1]

lemma aux_oqb_Hcont (hG : aux_oqb_Good G h p m y0) : Continuous (Hfun G) := by
  have hh := hG.hh
  have hp := hG.hp
  have hL : ∀ x y, |Hfun G x - Hfun G y| ≤ (h * p / (h + p)) * |x - y| := by
    have key : ∀ s t, 0 ≤ s → s ≤ t → |Hfun G t - Hfun G s| ≤ (h * p / (h + p)) * (t - s) := by
      intro s t hs hst
      have h1 := aux_oqb_lip hG hs hst
      have h2 : Hfun G s ≤ Hfun G t := by
        rcases eq_or_lt_of_le hst with e | e
        · rw [e]
        · exact (aux_oqb_smono hG hs e).le
      rw [abs_of_nonneg (by linarith), div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
      linarith
    intro x y
    rw [aux_oqb_Hmax hG x, aux_oqb_Hmax hG y]
    have hxy : |max x 0 - max y 0| ≤ |x - y| := abs_max_sub_max_le_abs x y 0
    have hc : 0 ≤ h * p / (h + p) := by positivity
    rcases le_total (max x 0) (max y 0) with e | e
    · have := key _ _ (le_max_right x 0) e
      rw [abs_sub_comm]
      calc _ ≤ _ := this
        _ = (h * p / (h + p)) * |max x 0 - max y 0| := by
          rw [abs_sub_comm, abs_of_nonneg (by linarith)]
        _ ≤ _ := mul_le_mul_of_nonneg_left hxy hc
    · have := key _ _ (le_max_right y 0) e
      calc _ ≤ _ := this
        _ = (h * p / (h + p)) * |max x 0 - max y 0| := by
          rw [abs_of_nonneg (by linarith)]
        _ ≤ _ := mul_le_mul_of_nonneg_left hxy hc
  have hLip : LipschitzWith (Real.toNNReal (h * p / (h + p))) (Hfun G) :=
    LipschitzWith.of_dist_le_mul fun x y => by
      rw [Real.dist_eq, Real.dist_eq, Real.coe_toNNReal _ (by positivity)]
      exact hL x y
  exact hLip.continuous

end abs

section abs2
variable {G : ℝ → ℝ} {h p m y0 : ℝ}

lemma aux_oqb_H0c (hG : aux_oqb_Good G h p m y0) : Continuous (H0fun G) := by
  have : H0fun G = fun Q => Hfun G Q - G y0 := funext (aux_oqb_H0_eq hG)
  rw [this]; exact (aux_oqb_Hcont hG).sub continuous_const

lemma aux_oqb_H00 (hG : aux_oqb_Good G h p m y0) : H0fun G 0 = 0 := by
  rw [aux_oqb_H0_eq hG]; simp [Hfun, hG.mp]

lemma aux_oqb_H0smono (hG : aux_oqb_Good G h p m y0) {s t : ℝ} (hs : 0 ≤ s) (hst : s < t) :
    H0fun G s < H0fun G t := by
  rw [aux_oqb_H0_eq hG, aux_oqb_H0_eq hG]
  have := aux_oqb_smono hG hs hst; linarith

lemma aux_oqb_H0pos (hG : aux_oqb_Good G h p m y0) {t : ℝ} (ht : 0 < t) : 0 < H0fun G t := by
  have := aux_oqb_H0smono hG le_rfl ht
  rwa [aux_oqb_H00 hG] at this

lemma aux_oqb_H0nn (hG : aux_oqb_Good G h p m y0) {t : ℝ} (ht : 0 ≤ t) : 0 ≤ H0fun G t := by
  rcases eq_or_lt_of_le ht with e | e
  · rw [← e, aux_oqb_H00 hG]
  · exact (aux_oqb_H0pos hG e).le

lemma aux_oqb_H0lip (hG : aux_oqb_Good G h p m y0) {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) :
    (h + p) * (H0fun G t - H0fun G s) ≤ h * p * (t - s) := by
  rw [aux_oqb_H0_eq hG, aux_oqb_H0_eq hG]
  have := aux_oqb_lip hG hs hst
  linarith

lemma aux_oqb_H0ratio (hG : aux_oqb_Good G h p m y0) {y Q : ℝ} (hy : 0 ≤ y) (hyQ : y ≤ Q) :
    H0fun G y * Q ≤ y * H0fun G Q := by
  rw [aux_oqb_H0_eq hG, aux_oqb_H0_eq hG]
  exact aux_oqb_ratio hG hy hyQ

lemma aux_oqb_H0lower (hG : aux_oqb_Good G h p m y0) {Q : ℝ} (hQ : 0 ≤ Q) :
    h * p * Q ≤ (h + p) * (H0fun G Q + G y0) := by
  rw [aux_oqb_H0_eq hG]
  have := aux_oqb_lower hG hQ
  simpa using this

lemma aux_oqb_II (hG : aux_oqb_Good G h p m y0) (a b : ℝ) :
    IntervalIntegrable (H0fun G) volume a b := (aux_oqb_H0c hG).intervalIntegrable a b

lemma aux_oqb_half (hG : aux_oqb_Good G h p m y0) {Q : ℝ} (hQ : 0 ≤ Q) :
    2 * (∫ y in (0:ℝ)..Q, H0fun G y) ≤ Q * H0fun G Q := by
  rcases eq_or_lt_of_le hQ with e | e
  · subst e; simp
  have hm := intervalIntegral.integral_mono_on (g := fun y => y * (H0fun G Q / Q)) hQ
    (aux_oqb_II hG 0 Q)
    ((by fun_prop : Continuous fun y : ℝ => y * (H0fun G Q / Q)).intervalIntegrable 0 Q)
    (fun y hy => by
      show H0fun G y ≤ y * (H0fun G Q / Q)
      rw [← mul_div_assoc, le_div_iff₀ e]
      exact aux_oqb_H0ratio hG hy.1 hy.2)
  try simp only [id] at hm
  rw [intervalIntegral.integral_mul_const, integral_id] at hm
  have : (Q ^ 2 - 0 ^ 2) / 2 * (H0fun G Q / Q) = Q * H0fun G Q / 2 := by
    field_simp; ring
  linarith

lemma aux_oqb_Abound (hG : aux_oqb_Good G h p m y0) {Q : ℝ} (hQ : 0 ≤ Q) :
    2 * (h + p) * (Q * H0fun G Q - ∫ y in (0:ℝ)..Q, H0fun G y) ≤ h * p * Q ^ 2 := by
  have hh := hG.hh
  have hp := hG.hp
  set k := h * p / (h + p) with hk
  have hm := intervalIntegral.integral_mono_on (f := fun y => H0fun G Q - k * (Q - y)) hQ
    ((by fun_prop : Continuous fun y : ℝ => H0fun G Q - k * (Q - y)).intervalIntegrable 0 Q)
    (aux_oqb_II hG 0 Q)
    (fun y hy => by
      show H0fun G Q - k * (Q - y) ≤ H0fun G y
      have := aux_oqb_H0lip hG hy.1 hy.2
      have h2 : H0fun G Q - H0fun G y ≤ h * p * (Q - y) / (h + p) := by
        rw [le_div_iff₀ (by positivity)]; linarith
      rw [hk, div_mul_eq_mul_div]
      linarith)
  try simp only [id] at hm
  rw [intervalIntegral.integral_sub intervalIntegrable_const
    ((by fun_prop : Continuous fun y : ℝ => k * (Q - y)).intervalIntegrable 0 Q),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_sub (f := fun _ => Q)
    (g := fun x => x) intervalIntegrable_const (continuous_id.intervalIntegrable 0 Q), integral_id] at hm
  simp only [intervalIntegral.integral_const, smul_eq_mul, sub_zero] at hm
  have e2 : (h + p) * k = h * p := by rw [hk]; field_simp
  nlinarith

lemma aux_oqb_Phismono (hG : aux_oqb_Good G h p m y0) {s t : ℝ} (hs : 0 ≤ s) (hst : s < t) :
    (∫ y in (0:ℝ)..s, H0fun G y) < ∫ y in (0:ℝ)..t, H0fun G y := by
  have hsub := intervalIntegral.integral_interval_sub_left (aux_oqb_II hG 0 t) (aux_oqb_II hG 0 s)
  have hpos : 0 < ∫ y in s..t, H0fun G y :=
    intervalIntegral.intervalIntegral_pos_of_pos_on (aux_oqb_II hG s t)
      (fun x hx => aux_oqb_H0pos hG (by linarith [hx.1])) hst
  linarith

lemma aux_oqb_Phic (hG : aux_oqb_Good G h p m y0) :
    Continuous (fun Q => ∫ y in (0:ℝ)..Q, H0fun G y) :=
  continuous_iff_continuousAt.2 fun u =>
    ((aux_oqb_H0c hG).integral_hasStrictDerivAt 0 u).hasDerivAt.continuousAt

lemma aux_oqb_Philow (hG : aux_oqb_Good G h p m y0) {Q : ℝ} (hQ : 0 ≤ Q) :
    (Q ^ 2 / 2 - Q) * H0fun G 1 ≤ ∫ y in (0:ℝ)..Q, H0fun G y := by
  have h1 := aux_oqb_H0pos hG one_pos
  have hm := intervalIntegral.integral_mono_on (f := fun y => (y - 1) * H0fun G 1) hQ
    ((by fun_prop : Continuous fun y : ℝ => (y - 1) * H0fun G 1).intervalIntegrable 0 Q)
    (aux_oqb_II hG 0 Q)
    (fun y hy => by
      show (y - 1) * H0fun G 1 ≤ H0fun G y
      rcases le_total y 1 with e | e
      · have := aux_oqb_H0nn hG hy.1
        nlinarith
      · have := aux_oqb_H0ratio hG zero_le_one e
        nlinarith)
  try simp only [id] at hm
  rw [intervalIntegral.integral_mul_const, intervalIntegral.integral_sub (f := fun x => x)
    (g := fun _ => (1:ℝ)) (continuous_id.intervalIntegrable 0 Q) intervalIntegrable_const, integral_id] at hm
  simp only [intervalIntegral.integral_const, smul_eq_mul, sub_zero] at hm
  nlinarith

lemma aux_oqb_exu {F : ℝ → ℝ} (hF : Continuous F) (hF0 : F 0 = 0)
    (hsm : ∀ s t, 0 ≤ s → s < t → F s < F t) {c : ℝ} (hc : 0 < c)
    (hM : ∃ M, 0 ≤ M ∧ c ≤ F M) : ∃! Q, 0 < Q ∧ F Q = c := by
  obtain ⟨M, hM0, hMc⟩ := hM
  obtain ⟨Q, hQ, hQc⟩ := intermediate_value_Icc hM0 hF.continuousOn ⟨by rw [hF0]; exact hc.le, hMc⟩
  have hQ0 : 0 < Q := by
    rcases eq_or_lt_of_le hQ.1 with e | e
    · subst e; rw [hF0] at hQc; linarith
    · exact e
  refine ⟨Q, ⟨hQ0, hQc⟩, fun Q' ⟨hQ', hQ'c⟩ => ?_⟩
  rcases lt_trichotomy Q' Q with e | e | e
  · have := hsm Q' Q hQ'.le e; linarith
  · exact e
  · have := hsm Q Q' hQ0.le e; linarith

lemma aux_oqb_foc (hG : aux_oqb_Good G h p m y0) {lam K Qs : ℝ} (hopt : IsOptQty G lam K Qs) :
    Qs * H0fun G Qs = lam * K + ∫ y in (0:ℝ)..Qs, H0fun G y := by
  obtain ⟨hQs, hmin⟩ := hopt
  set f : ℝ → ℝ := fun Q => (lam * K + ∫ y in (0:ℝ)..Q, Hfun G y) / Q with hf
  have hloc : IsLocalMin f Qs := by
    filter_upwards [lt_mem_nhds hQs] with Q hQ
    simp only [hf]
    rw [← aux_oqb_cost hG lam K hQs, ← aux_oqb_cost hG lam K hQ]
    exact hmin Q hQ
  have hd : HasDerivAt f ((Hfun G Qs * Qs - (lam * K + ∫ y in (0:ℝ)..Qs, Hfun G y) * 1) / Qs ^ 2)
      Qs := by
    have h1 : HasDerivAt (fun Q => lam * K + ∫ y in (0:ℝ)..Q, Hfun G y) (Hfun G Qs) Qs :=
      ((aux_oqb_Hcont hG).integral_hasStrictDerivAt 0 Qs).hasDerivAt.const_add _
    exact h1.div (hasDerivAt_id Qs) hQs.ne'
  have h0 := hloc.hasDerivAt_eq_zero hd
  have hQ2 : Qs ^ 2 ≠ 0 := by positivity
  rw [div_eq_zero_iff] at h0
  rcases h0 with h0 | h0
  · have hint : (∫ y in (0:ℝ)..Qs, Hfun G y) = (∫ y in (0:ℝ)..Qs, H0fun G y) + Qs * G y0 := by
      have : (fun y => H0fun G y) = fun y => Hfun G y - G y0 := funext (aux_oqb_H0_eq hG)
      rw [this, intervalIntegral.integral_sub ((aux_oqb_Hcont hG).intervalIntegrable 0 Qs)
        intervalIntegrable_const]
      simp
    rw [aux_oqb_H0_eq hG]
    rw [hint] at h0
    linarith
  · exact absurd h0 hQ2

end abs2

lemma aux_oqb_eoqH {lam L h p : ℝ} (hh : 0 < h) (hp : 0 < p) {Q : ℝ} (hQ : 0 < Q) :
    (h + p) * Hfun (eoqCost lam L h p) Q = h * p * Q := by
  set m := lam * L
  set G := eoqCost lam L h p with hGd
  have hl : ∀ y, y ≤ m → G y = p * (m - y) := by
    intro y hy; simp only [hGd, eoqCost]
    rw [max_eq_right (by linarith), max_eq_left (by linarith)]; ring
  have hr : ∀ y, m ≤ y → G y = h * (y - m) := by
    intro y hy; simp only [hGd, eoqCost]
    rw [max_eq_left (by linarith), max_eq_right (by linarith)]; ring
  have hc : Continuous G := by
    show Continuous (fun y => h * max (y - lam * L) 0 + p * max (lam * L - y) 0)
    fun_prop
  have hanti : StrictAntiOn G (Set.Iic m) := by
    intro s hs t ht hst
    rw [hl s hs, hl t ht]; nlinarith
  have hmono : StrictMonoOn G (Set.Ici m) := by
    intro s hs t ht hst
    rw [hr s hs, hr t ht]; nlinarith
  have e := aux_ihq_opteq hc hanti hmono hQ
  obtain ⟨a, b⟩ := aux_ihq_optpos hc hanti hmono hQ
  have hH : Hfun G Q = G (optReorder G Q) := by simp [Hfun, hQ]
  rw [hH]
  rw [hr _ b.le, hl _ a.le] at e
  rw [hl _ a.le]
  nlinarith

lemma aux_oqb_nvgood {lam L h p : ℝ} {μ : Measure ℝ} (hh : 0 < h) (hp : 0 < p)
    (hμ : IsLeadtimeDemand lam L μ) {y0 : ℝ} (hy0 : IsMinimizer (newsvendorCost h p μ) y0)
    (huniq : ∀ y, IsMinimizer (newsvendorCost h p μ) y → y = y0) :
    aux_oqb_Good (newsvendorCost h p μ) h p (lam * L) y0 := by
  have := hμ.isProb
  set G := newsvendorCost h p μ with hGdef
  have hmin : ∀ z, z ≠ y0 → G y0 < G z := by
    intro z hz
    refine lt_of_le_of_ne (hy0 z) (fun heq => hz ?_)
    exact huniq z (fun w => heq ▸ hy0 w)
  have hmp : minPoint G = y0 := by
    have hex : ∃ y, IsMinimizer G y := ⟨y0, hy0⟩
    simp only [minPoint, dif_pos hex]
    exact huniq _ hex.choose_spec
  have hconv : ∀ y z a b : ℝ, 0 ≤ a → 0 ≤ b → a + b = 1 →
      G (a * y + b * z) ≤ a * G y + b * G z :=
    fun y z a b ha hb hab => aux_ihq_conv hμ hh.le hp.le y z a b ha hb hab
  obtain ⟨hanti, hmono⟩ := aux_ihq_shape hconv hmin
  refine ⟨hh, hp, aux_ihq_cont hμ hh.le hp.le, hanti, hmono, hmp, hconv, ?_, ?_, ?_, ?_⟩
  · intro x y hxy
    simp only [hGdef, newsvendorCost]
    have hmono : ∫ ω, (h * max (y - ω) 0 + p * max (ω - y) 0) ∂μ ≤
        ∫ ω, (h * max (x - ω) 0 + p * max (ω - x) 0 + h * (y - x)) ∂μ :=
      integral_mono (aux_ihq_int hμ y) ((aux_ihq_int hμ x).add (integrable_const (h * (y - x))))
      (fun ω => by
        have h1 : max (y - ω) 0 ≤ max (x - ω) 0 + (y - x) :=
          max_le (by linarith [le_max_left (x - ω) 0]) (by linarith [le_max_right (x - ω) 0])
        have h2 : max (ω - y) 0 ≤ max (ω - x) 0 := max_le_max (by linarith) le_rfl
        have := mul_le_mul_of_nonneg_left h1 hh.le
        have := mul_le_mul_of_nonneg_left h2 hp.le
        simp only [Pi.add_apply]
        nlinarith)
    rw [integral_add (aux_ihq_int hμ x) (integrable_const _), integral_const] at hmono
    simpa using hmono
  · intro x y hxy
    simp only [hGdef, newsvendorCost]
    have hmono : ∫ ω, (h * max (x - ω) 0 + p * max (ω - x) 0) ∂μ ≤
        ∫ ω, (h * max (y - ω) 0 + p * max (ω - y) 0 + p * (y - x)) ∂μ :=
      integral_mono (aux_ihq_int hμ x) ((aux_ihq_int hμ y).add (integrable_const (p * (y - x))))
      (fun ω => by
        have h1 : max (ω - x) 0 ≤ max (ω - y) 0 + (y - x) :=
          max_le (by linarith [le_max_left (ω - y) 0]) (by linarith [le_max_right (ω - y) 0])
        have h2 : max (x - ω) 0 ≤ max (y - ω) 0 := max_le_max (by linarith) le_rfl
        have := mul_le_mul_of_nonneg_left h1 hp.le
        have := mul_le_mul_of_nonneg_left h2 hh.le
        simp only [Pi.add_apply]
        nlinarith)
    rw [integral_add (aux_ihq_int hμ y) (integrable_const _), integral_const] at hmono
    simpa using hmono
  · intro y
    simp only [hGdef, newsvendorCost]
    have hmono : ∫ ω, h * (y - ω) ∂μ ≤ ∫ ω, (h * max (y - ω) 0 + p * max (ω - y) 0) ∂μ :=
      integral_mono (((integrable_const y).sub hμ.integrable).const_mul h) (aux_ihq_int hμ y)
      (fun ω => by
        have h1 : y - ω ≤ max (y - ω) 0 := le_max_left _ _
        have h2 : 0 ≤ max (ω - y) 0 := le_max_right _ _
        have := mul_le_mul_of_nonneg_left h1 hh.le
        have := mul_nonneg hp.le h2
        simp only [Pi.sub_apply]
        nlinarith)
    rw [integral_const_mul, integral_sub (integrable_const _) hμ.integrable, integral_const,
      hμ.mean_eq] at hmono
    simpa using hmono
  · intro y
    simp only [hGdef, newsvendorCost]
    have hmono : ∫ ω, p * (ω - y) ∂μ ≤ ∫ ω, (h * max (y - ω) 0 + p * max (ω - y) 0) ∂μ :=
      integral_mono ((hμ.integrable.sub (integrable_const y)).const_mul p) (aux_ihq_int hμ y)
      (fun ω => by
        have h1 : ω - y ≤ max (ω - y) 0 := le_max_left _ _
        have h2 : 0 ≤ max (y - ω) 0 := le_max_right _ _
        have := mul_le_mul_of_nonneg_left h1 hp.le
        have := mul_nonneg hh.le h2
        simp only [Pi.sub_apply]
        nlinarith)
    rw [integral_const_mul, integral_sub hμ.integrable (integrable_const _), integral_const,
      hμ.mean_eq] at hmono
    simpa using hmono

lemma aux_oqb_E {lam K h p : ℝ} (hlam : 0 < lam) (hK : 0 < K) (hh : 0 < h) (hp : 0 < p) :
    0 < eoqQty lam K h p ∧ h * p * eoqQty lam K h p ^ 2 = 2 * lam * K * (h + p) := by
  have hpos : 0 < 2 * lam * K * (h + p) / (h * p) := by positivity
  refine ⟨Real.sqrt_pos.2 hpos, ?_⟩
  unfold eoqQty
  rw [Real.sq_sqrt hpos.le]
  field_simp

lemma aux_oqb_Emono {lam K K' h p : ℝ} (hh : 0 < h) (hp : 0 < p) (hlam : 0 < lam) (hKK : K ≤ K') :
    eoqQty lam K h p ≤ eoqQty lam K' h p := by
  unfold eoqQty
  apply Real.sqrt_le_sqrt
  apply div_le_div_of_nonneg_right _ (by positivity)
  have : 0 < h + p := by linarith
  have := mul_le_mul_of_nonneg_left hKK (by positivity : (0:ℝ) ≤ 2 * lam)
  nlinarith

theorem order_quantity_bounds_core
    {lam L h p : ℝ} {μ : Measure ℝ}
    (hlam : 0 < lam) (hL : 0 < L) (hh : 0 < h) (hp : 0 < p)
    (hμ : IsLeadtimeDemand lam L μ)
    (hG : ∃! y : ℝ, IsMinimizer (newsvendorCost h p μ) y) :
    (∀ K : ℝ, 0 < K →
      (∃! Q : ℝ, 0 < Q ∧ Q * H0fun (newsvendorCost h p μ) Q = 2 * lam * K) ∧
      (∃! Q : ℝ, 0 < Q ∧
        H0fun (newsvendorCost h p μ) Q = Hfun (eoqCost lam L h p) (eoqQty lam K h p)) ∧
      (∃! Q : ℝ, 0 < Q ∧ (∫ y in (0 : ℝ)..Q, H0fun (newsvendorCost h p μ) y) = lam * K) ∧
      ∀ Qs Qb Qb1 Qb2 : ℝ,
        IsOptQty (newsvendorCost h p μ) lam K Qs →
        0 < Qb → Qb * H0fun (newsvendorCost h p μ) Qb = 2 * lam * K →
        0 < Qb1 →
        H0fun (newsvendorCost h p μ) Qb1 = Hfun (eoqCost lam L h p) (eoqQty lam K h p) →
        0 < Qb2 → (∫ y in (0 : ℝ)..Qb2, H0fun (newsvendorCost h p μ) y) = lam * K →
        eoqQty lam K h p ≤ Qs ∧ Qs ≤ Qb ∧ Qb ≤ Qb1 ∧ Qb ≤ Qb2) ∧
    ∀ Qb1 : ℝ → ℝ,
      (∀ K : ℝ, 0 < K → 0 < Qb1 K ∧
        H0fun (newsvendorCost h p μ) (Qb1 K) = Hfun (eoqCost lam L h p) (eoqQty lam K h p)) →
      MonotoneOn (fun K => Qb1 K - eoqQty lam K h p) (Set.Ioi 0) ∧
      ∃ c : ℝ, Tendsto (fun K => Qb1 K - eoqQty lam K h p) atTop (𝓝 c) := by
  obtain ⟨y0, hy0, huniq⟩ := hG
  have hGd := aux_oqb_nvgood hh hp hμ hy0 huniq
  set G := newsvendorCost h p μ with hGdef
  have hcd : ∀ K, 0 < K → (h + p) * Hfun (eoqCost lam L h p) (eoqQty lam K h p) =
      h * p * eoqQty lam K h p := fun K hK =>
    aux_oqb_eoqH hh hp (aux_oqb_E hlam hK hh hp).1
  have h1pos : 0 < H0fun G 1 := aux_oqb_H0pos hGd one_pos
  have hfsm : ∀ s t, 0 ≤ s → s < t → s * H0fun G s < t * H0fun G t := by
    intro s t hs hst
    have a := aux_oqb_H0smono hGd hs hst
    have b := aux_oqb_H0nn hGd hs
    nlinarith
  have hHge : ∀ M, 1 ≤ M → M * H0fun G 1 ≤ H0fun G M := by
    intro M hM
    have := aux_oqb_H0ratio hGd zero_le_one hM
    linarith
  refine ⟨fun K hK => ?_, ?_⟩
  · obtain ⟨hE, hE2⟩ := aux_oqb_E hlam hK hh hp
    set E := eoqQty lam K h p with hEdef
    set cd := Hfun (eoqCost lam L h p) E with hcddef
    have hcdE : (h + p) * cd = h * p * E := hcd K hK
    have hcdpos : 0 < cd := by
      have : 0 < (h + p) * cd := by rw [hcdE]; positivity
      exact pos_of_mul_pos_right this (by linarith)
    have hlK : 0 < lam * K := mul_pos hlam hK
    refine ⟨?_, ?_, ?_, ?_⟩
    · apply aux_oqb_exu ((continuous_id.mul (aux_oqb_H0c hGd))) (by simp)
        hfsm (by positivity)
      refine ⟨max 1 (2 * lam * K / H0fun G 1), by positivity, ?_⟩
      set M := max 1 (2 * lam * K / H0fun G 1)
      have hM1 : 1 ≤ M := le_max_left _ _
      have hM2 : 2 * lam * K / H0fun G 1 ≤ M := le_max_right _ _
      rw [div_le_iff₀ h1pos] at hM2
      have := hHge M hM1
      show 2 * lam * K ≤ M * H0fun G M
      nlinarith
    · apply aux_oqb_exu (aux_oqb_H0c hGd) (aux_oqb_H00 hGd)
        (fun s t hs hst => aux_oqb_H0smono hGd hs hst) hcdpos
      refine ⟨max 1 (cd / H0fun G 1), by positivity, ?_⟩
      set M := max 1 (cd / H0fun G 1)
      have hM1 : 1 ≤ M := le_max_left _ _
      have hM2 : cd / H0fun G 1 ≤ M := le_max_right _ _
      rw [div_le_iff₀ h1pos] at hM2
      have := hHge M hM1
      linarith
    · apply aux_oqb_exu (aux_oqb_Phic hGd) (by simp)
        (fun s t hs hst => aux_oqb_Phismono hGd hs hst) hlK
      refine ⟨2 + 2 * (lam * K) / H0fun G 1, by positivity, ?_⟩
      have := aux_oqb_Philow hGd (by positivity : (0:ℝ) ≤ 2 + 2 * (lam * K) / H0fun G 1)
      refine le_trans ?_ this
      have e : ((2 + 2 * (lam * K) / H0fun G 1) ^ 2 / 2 - (2 + 2 * (lam * K) / H0fun G 1)) * H0fun G 1 =
          (2 + 2 * (lam * K) / H0fun G 1) * (lam * K) := by
        field_simp; ring
      rw [e]
      have : 0 ≤ 2 * (lam * K) / H0fun G 1 := by positivity
      nlinarith
    · intro Qs Qb Qb1 Qb2 hopt hQb hQbe hQb1 hQb1e hQb2 hQb2e
      have hQs := hopt.1
      have foc := aux_oqb_foc hGd hopt
      have hA := aux_oqb_Abound hGd hQs.le
      have hhalf := aux_oqb_half hGd hQs.le
      refine ⟨?_, ?_, ?_, ?_⟩
      · -- E ≤ Qs
        have h2 : 2 * (h + p) * (lam * K) ≤ h * p * Qs ^ 2 := by
          have : Qs * H0fun G Qs - ∫ y in (0:ℝ)..Qs, H0fun G y = lam * K := by linarith
          rw [this] at hA; exact hA
        by_contra hc
        push Not at hc
        have : Qs ^ 2 < E ^ 2 := by nlinarith
        have : h * p * Qs ^ 2 < h * p * E ^ 2 := mul_lt_mul_of_pos_left this (by positivity)
        nlinarith
      · -- Qs ≤ Qb
        have : Qs * H0fun G Qs ≤ Qb * H0fun G Qb := by
          show Qs * H0fun G Qs ≤ Qb * H0fun G Qb
          linarith
        by_contra hc; push Not at hc
        have := hfsm Qb Qs hQb.le hc
        linarith
      · -- Qb ≤ Qb1
        by_contra hc; push Not at hc
        have i1 := aux_oqb_H0smono hGd hQb1.le hc
        rw [hQb1e] at i1
        have i2 := aux_oqb_H0lip hGd le_rfl hQb.le
        rw [aux_oqb_H00 hGd] at i2
        have hEQ : E < Qb := by
          by_contra hc2; push Not at hc2
          have : (h + p) * cd < (h + p) * H0fun G Qb := mul_lt_mul_of_pos_left i1 (by linarith)
          nlinarith
        have : E * cd < Qb * H0fun G Qb := by
          have := mul_lt_mul_of_pos_right hEQ hcdpos
          have := mul_lt_mul_of_pos_left i1 hQb
          linarith
        have : (h + p) * (E * cd) < (h + p) * (Qb * H0fun G Qb) :=
          mul_lt_mul_of_pos_left this (by linarith)
        rw [hQbe] at this
        have : (h + p) * (E * cd) = h * p * E ^ 2 := by
          calc (h + p) * (E * cd) = E * ((h + p) * cd) := by ring
            _ = h * p * E ^ 2 := by rw [hcdE]; ring
        nlinarith
      · -- Qb ≤ Qb2
        have hb := aux_oqb_half hGd hQb.le
        by_contra hc; push Not at hc
        have := aux_oqb_Phismono hGd hQb2.le hc
        linarith
  · intro Qb1 hQb1
    have hstep : ∀ K K', 0 < K → K ≤ K' →
        Qb1 K - eoqQty lam K h p ≤ Qb1 K' - eoqQty lam K' h p := by
      intro K K' hK hKK
      have hK' : 0 < K' := lt_of_lt_of_le hK hKK
      obtain ⟨p1, e1⟩ := hQb1 K hK
      obtain ⟨p2, e2⟩ := hQb1 K' hK'
      have c1 := hcd K hK
      have c2 := hcd K' hK'
      have hEm := aux_oqb_Emono hh hp hlam hKK (lam := lam)
      have hle : Qb1 K ≤ Qb1 K' := by
        by_contra hc; push Not at hc
        have := aux_oqb_H0smono hGd p2.le hc
        rw [e1, e2] at this
        have : (h + p) * Hfun (eoqCost lam L h p) (eoqQty lam K' h p) <
            (h + p) * Hfun (eoqCost lam L h p) (eoqQty lam K h p) :=
          mul_lt_mul_of_pos_left this (by linarith)
        rw [c1, c2] at this
        have : eoqQty lam K' h p < eoqQty lam K h p := lt_of_mul_lt_mul_left this (by positivity)
        linarith
      have := aux_oqb_H0lip hGd p1.le hle
      rw [e1, e2, mul_sub, c1, c2] at this
      have hhp : 0 < h * p := by positivity
      nlinarith
    refine ⟨fun K hK K' hK' hKK => hstep K K' hK hKK, ?_⟩
    set f := fun K => Qb1 K - eoqQty lam K h p with hf
    have hbd : ∀ K, 0 < K → f K ≤ (h + p) * G y0 / (h * p) := by
      intro K hK
      obtain ⟨p1, e1⟩ := hQb1 K hK
      have := aux_oqb_H0lower hGd p1.le
      rw [e1, mul_add, hcd K hK] at this
      rw [le_div_iff₀ (by positivity)]
      simp only [hf]
      nlinarith
    set g := fun K => f (max K 1) with hg
    have hgm : Monotone g := fun a b hab =>
      hstep _ _ (lt_of_lt_of_le one_pos (le_max_right a 1)) (max_le_max hab le_rfl)
    have hgb : BddAbove (Set.range g) :=
      ⟨(h + p) * G y0 / (h * p), by
        rintro _ ⟨K, rfl⟩
        exact hbd _ (lt_of_lt_of_le one_pos (le_max_right K 1))⟩
    refine ⟨⨆ i, g i, (tendsto_atTop_ciSup hgm hgb).congr' ?_⟩
    filter_upwards [eventually_ge_atTop 1] with K hK
    simp only [hg, max_eq_left hK]
end ZhengQR.OrderQty

open ZhengQR.OrderQty


theorem solution
    {lam L h p : ℝ} {μ : Measure ℝ}
    (hlam : 0 < lam) (hL : 0 < L) (hh : 0 < h) (hp : 0 < p)
    (hμ : IsLeadtimeDemand lam L μ)
    (hG : ∃! y : ℝ, IsMinimizer (newsvendorCost h p μ) y) :
    (∀ K : ℝ, 0 < K →
      (∃! Q : ℝ, 0 < Q ∧ Q * H0fun (newsvendorCost h p μ) Q = 2 * lam * K) ∧
      (∃! Q : ℝ, 0 < Q ∧
        H0fun (newsvendorCost h p μ) Q = Hfun (eoqCost lam L h p) (eoqQty lam K h p)) ∧
      (∃! Q : ℝ, 0 < Q ∧ (∫ y in (0 : ℝ)..Q, H0fun (newsvendorCost h p μ) y) = lam * K) ∧
      ∀ Qs Qb Qb1 Qb2 : ℝ,
        IsOptQty (newsvendorCost h p μ) lam K Qs →
        0 < Qb → Qb * H0fun (newsvendorCost h p μ) Qb = 2 * lam * K →
        0 < Qb1 →
        H0fun (newsvendorCost h p μ) Qb1 = Hfun (eoqCost lam L h p) (eoqQty lam K h p) →
        0 < Qb2 → (∫ y in (0 : ℝ)..Qb2, H0fun (newsvendorCost h p μ) y) = lam * K →
        eoqQty lam K h p ≤ Qs ∧ Qs ≤ Qb ∧ Qb ≤ Qb1 ∧ Qb ≤ Qb2) ∧
    ∀ Qb1 : ℝ → ℝ,
      (∀ K : ℝ, 0 < K → 0 < Qb1 K ∧
        H0fun (newsvendorCost h p μ) (Qb1 K) = Hfun (eoqCost lam L h p) (eoqQty lam K h p)) →
      MonotoneOn (fun K => Qb1 K - eoqQty lam K h p) (Set.Ioi 0) ∧
      ∃ c : ℝ, Tendsto (fun K => Qb1 K - eoqQty lam K h p) atTop (𝓝 c) := by
  exact order_quantity_bounds_core hlam hL hh hp hμ hG
