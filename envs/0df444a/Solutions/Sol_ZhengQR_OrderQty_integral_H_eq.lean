-- Prove2me | solution 1 for ZhengQR.OrderQty.integral_H_eq
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-29T04:52:46.011681+00:00
-- url     : https://prove2.me/submissions/7be9ecf2-4054-476e-ac9e-0d4e46cc99ee

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

end ZhengQR.OrderQty

open ZhengQR.OrderQty

theorem solution
    {lam L K h p : ℝ} {μ : Measure ℝ}
    (hlam : 0 < lam) (hL : 0 < L) (hK : 0 < K) (hh : 0 < h) (hp : 0 < p)
    (hμ : IsLeadtimeDemand lam L μ)
    (hG : ∃! y : ℝ, IsMinimizer (newsvendorCost h p μ) y)
    {Q : ℝ} (hQ : 0 < Q) :
    (∫ y in optReorder (newsvendorCost h p μ) Q..optReorder (newsvendorCost h p μ) Q + Q,
        newsvendorCost h p μ y) =
      (∫ y in (0 : ℝ)..Q, Hfun (newsvendorCost h p μ) y) ∧
    optCost (newsvendorCost h p μ) lam K Q =
      (lam * K + ∫ y in (0 : ℝ)..Q, Hfun (newsvendorCost h p μ) y) / Q := by
  set G := newsvendorCost h p μ with hGdef
  obtain ⟨y0, hy0, huniq⟩ := hG
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
  have hc : Continuous G := aux_ihq_cont hμ hh.le hp.le
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
  refine ⟨key, ?_⟩
  simp only [optCost, qrCost]
  rw [← key]
