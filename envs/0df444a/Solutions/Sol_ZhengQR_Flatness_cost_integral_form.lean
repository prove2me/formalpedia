-- Prove2me | solution 1 for ZhengQR.Flatness.cost_integral_form
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-29T02:36:14.093252+00:00
-- url     : https://prove2.me/submissions/6432e90e-70fc-4cf6-9a10-20c82319f7f9

import Mathlib
import Definitions.Def_ZhengQR_Flatness_QRModel

namespace ZhengQR.Flatness

open MeasureTheory Set Filter Topology

lemma aux_cif_int (M : QRModel) (y : ℝ) :
    Integrable (fun x : ℝ => M.h * max (y - x) 0 + M.p * max (x - y) 0) M.μ := by
  have := M.isProb
  have h1 : Integrable (fun x : ℝ => y - x) M.μ := (integrable_const y).sub M.integrable
  have h2 : Integrable (fun x : ℝ => x - y) M.μ := M.integrable.sub (integrable_const y)
  exact (h1.pos_part.const_mul M.h).add (h2.pos_part.const_mul M.p)

lemma aux_cif_lip (M : QRModel) (y y' : ℝ) :
    |M.G y - M.G y'| ≤ (M.h + M.p) * |y - y'| := by
  have := M.isProb
  have hh := M.h_pos.le
  have hp := M.p_pos.le
  show |newsvendorCost M.h M.p M.μ y - newsvendorCost M.h M.p M.μ y'| ≤ _
  unfold newsvendorCost
  rw [← integral_sub (aux_cif_int M y) (aux_cif_int M y')]
  have hb : ∀ x : ℝ, ‖(M.h * max (y - x) 0 + M.p * max (x - y) 0) -
      (M.h * max (y' - x) 0 + M.p * max (x - y') 0)‖ ≤ (M.h + M.p) * |y - y'| := by
    intro x
    rw [Real.norm_eq_abs]
    have e1 : |max (y - x) 0 - max (y' - x) 0| ≤ |y - y'| := by
      have := abs_max_sub_max_le_abs (y - x) (y' - x) 0
      rw [show y - x - (y' - x) = y - y' by ring] at this
      exact this
    have e2 : |max (x - y) 0 - max (x - y') 0| ≤ |y - y'| := by
      have := abs_max_sub_max_le_abs (x - y) (x - y') 0
      rw [show x - y - (x - y') = -(y - y') by ring, abs_neg] at this
      exact this
    calc |(M.h * max (y - x) 0 + M.p * max (x - y) 0) -
          (M.h * max (y' - x) 0 + M.p * max (x - y') 0)|
        = |M.h * (max (y - x) 0 - max (y' - x) 0) +
            M.p * (max (x - y) 0 - max (x - y') 0)| := by congr 1; ring
      _ ≤ |M.h * (max (y - x) 0 - max (y' - x) 0)| +
            |M.p * (max (x - y) 0 - max (x - y') 0)| := abs_add_le _ _
      _ = M.h * |max (y - x) 0 - max (y' - x) 0| +
            M.p * |max (x - y) 0 - max (x - y') 0| := by
          rw [abs_mul, abs_mul, abs_of_nonneg hh, abs_of_nonneg hp]
      _ ≤ M.h * |y - y'| + M.p * |y - y'| := by gcongr
      _ = (M.h + M.p) * |y - y'| := by ring
  have := norm_integral_le_of_norm_le_const (μ := M.μ) (Filter.Eventually.of_forall hb)
  rw [Real.norm_eq_abs] at this
  simpa using this

lemma aux_cif_convex (M : QRModel) : ConvexOn ℝ univ M.G := by
  have := M.isProb
  have hh := M.h_pos.le
  have hp := M.p_pos.le
  refine ⟨convex_univ, ?_⟩
  intro y1 _ y2 _ a b ha hb hab
  simp only [smul_eq_mul]
  show newsvendorCost M.h M.p M.μ (a * y1 + b * y2) ≤
    a * newsvendorCost M.h M.p M.μ y1 + b * newsvendorCost M.h M.p M.μ y2
  unfold newsvendorCost
  rw [← integral_const_mul, ← integral_const_mul,
    ← integral_add ((aux_cif_int M y1).const_mul a) ((aux_cif_int M y2).const_mul b)]
  refine integral_mono (aux_cif_int M _)
    (((aux_cif_int M y1).const_mul a).add ((aux_cif_int M y2).const_mul b)) ?_
  intro x
  simp only
  have c1 : a * y1 + b * y2 - x = a * (y1 - x) + b * (y2 - x) := by
    linear_combination x * hab
  have c2 : x - (a * y1 + b * y2) = a * (x - y1) + b * (x - y2) := by
    linear_combination (-x) * hab
  have e1 : max (a * y1 + b * y2 - x) 0 ≤ a * max (y1 - x) 0 + b * max (y2 - x) 0 := by
    apply max_le
    · rw [c1]
      exact add_le_add (mul_le_mul_of_nonneg_left (le_max_left _ _) ha)
        (mul_le_mul_of_nonneg_left (le_max_left _ _) hb)
    · exact add_nonneg (mul_nonneg ha (le_max_right _ _)) (mul_nonneg hb (le_max_right _ _))
  have e2 : max (x - (a * y1 + b * y2)) 0 ≤ a * max (x - y1) 0 + b * max (x - y2) 0 := by
    apply max_le
    · rw [c2]
      exact add_le_add (mul_le_mul_of_nonneg_left (le_max_left _ _) ha)
        (mul_le_mul_of_nonneg_left (le_max_left _ _) hb)
    · exact add_nonneg (mul_nonneg ha (le_max_right _ _)) (mul_nonneg hb (le_max_right _ _))
  nlinarith [mul_le_mul_of_nonneg_left e1 hh, mul_le_mul_of_nonneg_left e2 hp]

lemma aux_cif_P {G : ℝ → ℝ} (hc : ConvexOn ℝ univ G) {a b : ℝ} (hab : a < b)
    (he : G a = G b) :
    (∀ y ∈ Icc a b, G y ≤ G a) ∧ (∀ y, y ∉ Ioc a b → G a ≤ G y) := by
  constructor
  · intro y hy
    have := hc.le_on_segment (mem_univ a) (mem_univ b)
      (show y ∈ segment ℝ a b by rw [segment_eq_Icc hab.le]; exact hy)
    rw [← he, max_self] at this
    exact this
  · intro y hy
    rw [mem_Ioc, not_and_or, not_lt, not_le] at hy
    rcases hy with hy | hy
    · rcases hy.lt_or_eq with hy | hy
      · exact hc.le_left_of_right_le (mem_univ y) (mem_univ b)
          (show a ∈ openSegment ℝ y b by rw [openSegment_eq_Ioo (hy.trans hab)]; exact ⟨hy, hab⟩)
          (le_of_eq he.symm)
      · rw [hy]
    · have := hc.le_right_of_left_le (mem_univ a) (mem_univ y)
        (show b ∈ openSegment ℝ a y by rw [openSegment_eq_Ioo (hab.trans hy)]; exact ⟨hab, hy⟩)
        (le_of_eq he)
      rw [he]; exact this

lemma aux_cif_L {G : ℝ → ℝ} (hG : Continuous G) (hc : ConvexOn ℝ univ G) {a b : ℝ}
    (hab : a < b) (he : G a = G b) (r q : ℝ) (hq : 0 ≤ q) :
    (∫ y in a..b, G y) + (q - (b - a)) * G a ≤ ∫ y in r..r + q, G y := by
  obtain ⟨P1, P2⟩ := aux_cif_P hc hab he
  have hg : Continuous (fun y => G y - G a) := hG.sub continuous_const
  have eI : ∫ y in r..r + q, (G y - G a) = (∫ y in r..r + q, G y) - q * G a := by
    rw [intervalIntegral.integral_sub (hG.intervalIntegrable _ _) intervalIntegrable_const,
      intervalIntegral.integral_const, smul_eq_mul]
    ring
  have eJ : ∫ y in a..b, (G y - G a) = (∫ y in a..b, G y) - (b - a) * G a := by
    rw [intervalIntegral.integral_sub (hG.intervalIntegrable _ _) intervalIntegrable_const,
      intervalIntegral.integral_const, smul_eq_mul]
  have key : ∫ y in a..b, (G y - G a) ≤ ∫ y in r..r + q, (G y - G a) := by
    rw [intervalIntegral.integral_of_le hab.le, intervalIntegral.integral_of_le (by linarith)]
    have hIi : IntegrableOn (fun y => G y - G a) (Ioc r (r + q)) := hg.integrableOn_Ioc
    have hJi : IntegrableOn (fun y => G y - G a) (Ioc a b) := hg.integrableOn_Ioc
    have s1 := integral_inter_add_sdiff (s := Ioc r (r + q)) (t := Ioc a b)
      measurableSet_Ioc hIi
    have s2 := integral_inter_add_sdiff (s := Ioc a b) (t := Ioc r (r + q))
      measurableSet_Ioc hJi
    rw [inter_comm (Ioc a b) (Ioc r (r + q))] at s2
    have h1 : 0 ≤ ∫ y in Ioc r (r + q) \ Ioc a b, (G y - G a) :=
      setIntegral_nonneg (measurableSet_Ioc.diff measurableSet_Ioc)
        (fun y hy => by have := P2 y hy.2; linarith)
    have h2 : ∫ y in Ioc a b \ Ioc r (r + q), (G y - G a) ≤ 0 :=
      setIntegral_nonpos (measurableSet_Ioc.diff measurableSet_Ioc)
        (fun y hy => by have := P1 y (Ioc_subset_Icc_self hy.1); linarith)
    linarith
  linarith

lemma aux_cif_foc {G : ℝ → ℝ} (hG : Continuous G) (q r : ℝ)
    (hmin : ∀ r', (∫ y in r..r + q, G y) ≤ ∫ y in r'..r' + q, G y) : G r = G (r + q) := by
  have hd : ∀ s, HasDerivAt (fun s => ∫ y in s..s + q, G y) (G (s + q) - G s) s := by
    intro s
    have h1 : HasDerivAt (fun u => ∫ x in (0:ℝ)..u, G x) (G (s + q)) (s + q) :=
      (hG.integral_hasStrictDerivAt 0 (s + q)).hasDerivAt
    have h2 : HasDerivAt (fun s : ℝ => s + q) 1 s := (hasDerivAt_id' s).add_const q
    have h3 := (h1.comp s h2).sub (hG.integral_hasStrictDerivAt 0 s).hasDerivAt
    rw [mul_one] at h3
    have e : (fun s => ∫ y in s..s + q, G y) =
        ((fun u => ∫ x in (0:ℝ)..u, G x) ∘ fun s => s + q) - fun u => ∫ x in (0:ℝ)..u, G x := by
      funext t
      simp only [Function.comp, Pi.sub_apply]
      rw [intervalIntegral.integral_interval_sub_left (hG.intervalIntegrable _ _)
        (hG.intervalIntegrable _ _)]
    rw [e]
    exact h3
  have hlm : IsLocalMin (fun s => ∫ y in s..s + q, G y) r := Filter.Eventually.of_forall hmin
  have := hlm.hasDerivAt_eq_zero (hd r)
  linarith

lemma aux_cif_ivt {G : ℝ → ℝ} (hG : Continuous G) {y0 : ℝ} (hy0 : ∀ z, G y0 ≤ G z) {q : ℝ}
    (hq : 0 < q) : ∃ r, G r = G (r + q) := by
  have hc : ContinuousOn (fun s => G (s + q) - G s) (Icc (y0 - q) y0) :=
    ((hG.comp (continuous_add_const q)).sub hG).continuousOn
  have h0 : (0:ℝ) ∈ Icc ((fun s => G (s + q) - G s) (y0 - q)) ((fun s => G (s + q) - G s) y0) := by
    simp only [sub_add_cancel]
    constructor
    · linarith [hy0 (y0 - q)]
    · linarith [hy0 (y0 + q)]
  obtain ⟨s, _, hs⟩ := intermediate_value_Icc (by linarith) hc h0
  exact ⟨s, by simp only at hs; linarith⟩

lemma aux_cif_opt {G : ℝ → ℝ} (hG : Continuous G) (hc : ConvexOn ℝ univ G) {y0 : ℝ}
    (hy0 : ∀ z, G y0 ≤ G z) (lam K : ℝ) {q : ℝ} (hq : 0 < q) :
    (∀ r', (∫ y in optReorder G lam K q..optReorder G lam K q + q, G y) ≤
      ∫ y in r'..r' + q, G y) ∧
    G (optReorder G lam K q) = G (optReorder G lam K q + q) := by
  obtain ⟨s, hs⟩ := aux_cif_ivt hG hy0 hq
  have hex : ∃ r, IsOptReorder G lam K q r := by
    refine ⟨s, fun r' => ?_⟩
    unfold qrCost
    have := aux_cif_L hG hc (show s < s + q by linarith) hs r' q hq.le
    rw [show q - (s + q - s) = 0 by ring, zero_mul, add_zero] at this
    exact div_le_div_of_nonneg_right (by linarith) hq.le
  have hopt : IsOptReorder G lam K q (optReorder G lam K q) := by
    unfold optReorder
    rw [dif_pos hex]
    exact hex.choose_spec
  have hmin : ∀ r', (∫ y in optReorder G lam K q..optReorder G lam K q + q, G y) ≤
      ∫ y in r'..r' + q, G y := by
    intro r'
    have := hopt r'
    unfold qrCost at this
    rw [div_le_div_iff_of_pos_right hq] at this
    linarith
  exact ⟨hmin, aux_cif_foc hG q _ hmin⟩

lemma aux_cif_main (M : QRModel) (Q : ℝ) (hQ : 0 < Q) :
    (∫ y in M.r Q..M.r Q + Q, M.G y) = (∫ y in (0 : ℝ)..Q, M.H y) := by
  have hG : Continuous M.G := by
    refine (LipschitzWith.of_dist_le_mul (K := Real.toNNReal (M.h + M.p)) fun y y' => ?_).continuous
    rw [Real.dist_eq, Real.dist_eq, Real.coe_toNNReal _ (by linarith [M.h_pos, M.p_pos])]
    exact aux_cif_lip M y y'
  have hc := aux_cif_convex M
  obtain ⟨y1, hy1, -⟩ := M.unique_min
  have hex : ∃ y, ∀ z, M.G y ≤ M.G z := ⟨y1, hy1⟩
  have hy0 : ∀ z, M.G (minPoint M.G) ≤ M.G z := by
    unfold minPoint
    rw [dif_pos hex]
    exact hex.choose_spec
  obtain ⟨F, hFq⟩ : ∃ F : ℝ → ℝ, ∀ q, F q = ∫ y in M.r q..M.r q + q, M.G y :=
    ⟨fun q => ∫ y in M.r q..M.r q + q, M.G y, fun q => rfl⟩
  have hH : ∀ q, 0 < q → M.H q = M.G (M.r q) := fun q hq => by
    show Hfun M.G M.lam M.K q = _
    unfold Hfun
    rw [if_pos hq]
    rfl
  have hH0 : ∀ q, ¬ 0 < q → M.H q = M.G (minPoint M.G) := fun q hq => by
    show Hfun M.G M.lam M.K q = _
    unfold Hfun
    rw [if_neg hq]
  have hopt : ∀ q, 0 < q → (∀ r', (∫ y in M.r q..M.r q + q, M.G y) ≤ ∫ y in r'..r' + q, M.G y)
      ∧ M.G (M.r q) = M.G (M.r q + q) :=
    fun q hq => aux_cif_opt hG hc hy0 M.lam M.K hq
  have hlow : ∀ q, 0 < q → ∀ q', 0 ≤ q' → F q + (q' - q) * M.H q ≤ F q' := by
    intro q hq q' hq'
    have := aux_cif_L hG hc (show M.r q < M.r q + q by linarith) (hopt q hq).2 (M.r q') q' hq'
    rw [show M.r q + q - M.r q = q by ring] at this
    rw [hH q hq, hFq, hFq]
    exact this
  have hup : ∀ q, 0 < q → ∀ q', 0 < q' →
      F q' ≤ F q + (q' - q) * M.H q + (M.h + M.p) * (q' - q) ^ 2 := by
    intro q hq q' hq'
    have h1 := (hopt q' hq').1 (M.r q)
    have hl : M.G (M.r q + q) = M.H q := by rw [hH q hq, (hopt q hq).2]
    rw [hFq, hFq]
    set a := M.r q
    have hsplit : (∫ y in a..a + q', M.G y) =
        (∫ y in a..a + q, M.G y) + ∫ y in a + q..a + q', M.G y :=
      (intervalIntegral.integral_add_adjacent_intervals (hG.intervalIntegrable _ _)
        (hG.intervalIntegrable _ _)).symm
    have hbd : |(∫ y in a + q..a + q', M.G y) - (q' - q) * M.G (a + q)| ≤
        (M.h + M.p) * (q' - q) ^ 2 := by
      have e : (∫ y in a + q..a + q', M.G y) - (q' - q) * M.G (a + q) =
          ∫ y in a + q..a + q', (M.G y - M.G (a + q)) := by
        rw [intervalIntegral.integral_sub (hG.intervalIntegrable _ _) intervalIntegrable_const,
          intervalIntegral.integral_const, smul_eq_mul]
        ring
      rw [e]
      have hhp : 0 ≤ M.h + M.p := by linarith [M.h_pos, M.p_pos]
      have := intervalIntegral.norm_integral_le_of_norm_le_const (a := a + q) (b := a + q')
        (C := (M.h + M.p) * |q' - q|) (f := fun y => M.G y - M.G (a + q)) (fun x hx => by
          rw [Real.norm_eq_abs]
          have h2 := Set.abs_sub_left_of_mem_uIcc (Set.uIoc_subset_uIcc hx)
          rw [show a + q' - (a + q) = q' - q by ring] at h2
          calc |M.G x - M.G (a + q)| ≤ (M.h + M.p) * |x - (a + q)| := aux_cif_lip M _ _
            _ ≤ (M.h + M.p) * |q' - q| := by gcongr)
      rw [Real.norm_eq_abs, show a + q' - (a + q) = q' - q by ring] at this
      calc _ ≤ _ := this
        _ = (M.h + M.p) * (q' - q) ^ 2 := by rw [mul_assoc, abs_mul_abs_self, sq]
    rw [hl] at hbd
    have := (abs_le.mp hbd).2
    linarith
  have hderiv : ∀ q, 0 < q → HasDerivAt F (M.H q) q := by
    intro q hq
    rw [hasDerivAt_iff_isLittleO]
    have hO : (fun x => F x - F q - (x - q) • M.H q) =O[𝓝 q] (fun x => ‖x - q‖ ^ 2) := by
      refine Asymptotics.IsBigO.of_bound (M.h + M.p) ?_
      filter_upwards [Ioi_mem_nhds hq] with x hx
      have l1 := hlow q hq x (le_of_lt hx)
      have l2 := hup q hq x hx
      simp only [Real.norm_eq_abs, sq_abs, abs_pow, smul_eq_mul]
      rw [abs_le]
      constructor <;> nlinarith [sq_nonneg (x - q), M.h_pos, M.p_pos]
    exact hO.trans_isLittleO (Asymptotics.isLittleO_pow_sub_sub q one_lt_two)
  have hF0 : F 0 = 0 := by rw [hFq]; simp
  have hcont : ContinuousOn F (Icc 0 Q) := by
    intro x hx
    rcases hx.1.lt_or_eq with hx0 | hx0
    · exact (hderiv x hx0).continuousAt.continuousWithinAt
    · subst hx0
      have hlo : ∀ x ∈ Icc (0:ℝ) Q, x * M.G (minPoint M.G) ≤ F x := by
        intro x hx
        rw [hFq]
        have := intervalIntegral.integral_mono_on (μ := volume)
          (show M.r x ≤ M.r x + x by linarith [hx.1])
          intervalIntegrable_const (hG.intervalIntegrable _ _) (fun y _ => hy0 y)
        rw [intervalIntegral.integral_const, smul_eq_mul,
          show M.r x + x - M.r x = x by ring] at this
        exact this
      have hhi : ∀ x ∈ Icc (0:ℝ) Q, F x ≤ ∫ y in (0:ℝ)..x, M.G y := by
        intro x hx
        rcases hx.1.lt_or_eq with hx' | hx'
        · have := (hopt x hx').1 0
          rw [zero_add] at this
          rw [hFq]
          exact this
        · subst hx'
          rw [hF0]
          simp
      show Tendsto F (𝓝[Icc 0 Q] 0) (𝓝 (F 0))
      rw [hF0]
      apply tendsto_of_tendsto_of_tendsto_of_le_of_le' (g := fun x => x * M.G (minPoint M.G))
        (h := fun x => ∫ y in (0:ℝ)..x, M.G y)
      · have : Tendsto (fun x : ℝ => x * M.G (minPoint M.G)) (𝓝 0)
            (𝓝 (0 * M.G (minPoint M.G))) :=
          (continuous_id.mul continuous_const).tendsto 0
        rw [zero_mul] at this
        exact this.mono_left nhdsWithin_le_nhds
      · have := (hG.integral_hasStrictDerivAt 0 0).hasDerivAt.continuousAt.tendsto
        rw [intervalIntegral.integral_same] at this
        exact this.mono_left nhdsWithin_le_nhds
      · exact eventually_nhdsWithin_of_forall hlo
      · exact eventually_nhdsWithin_of_forall hhi
  have hmono : MonotoneOn M.H (Icc 0 Q) := by
    intro x hx y hy hxy
    rcases hx.1.lt_or_eq with hx0 | hx0
    · have hy0' : 0 < y := lt_of_lt_of_le hx0 hxy
      have l1 := hlow x hx0 y hy0'.le
      have l2 := hlow y hy0' x hx0.le
      rcases hxy.lt_or_eq with h | h
      · nlinarith
      · rw [h]
    · rw [← hx0, hH0 0 (lt_irrefl 0)]
      by_cases hy' : 0 < y
      · rw [hH y hy']; exact hy0 _
      · rw [hH0 y hy']
  have hint : IntervalIntegrable M.H volume 0 Q := by
    apply MonotoneOn.intervalIntegrable
    rw [uIcc_of_le hQ.le]
    exact hmono
  have := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hQ.le hcont
    (fun x hx => hderiv x hx.1) hint
  rw [this, hF0, sub_zero, hFq]

end ZhengQR.Flatness

open ZhengQR.Flatness

theorem solution (M : QRModel) (Q : ℝ) (hQ : 0 < Q) :
    (∫ y in M.r Q..M.r Q + Q, M.G y) = (∫ y in (0 : ℝ)..Q, M.H y) ∧
      M.C Q = (M.lam * M.K + ∫ y in (0 : ℝ)..Q, M.H y) / Q := by
  have h1 := aux_cif_main M Q hQ
  refine ⟨h1, ?_⟩
  show (M.lam * M.K + ∫ y in M.r Q..M.r Q + Q, M.G y) / Q = _
  rw [h1]
