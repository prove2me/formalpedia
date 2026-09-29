-- Prove2me | solution 1 for StochasticOrders.MonotoneConvex.icx_icv_convolution
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-29T04:25:54.512748+00:00
-- url     : https://prove2.me/submissions/c00b0ef2-0bee-497c-bb19-4c0a495932cc

import Mathlib
import Definitions.Def_StochasticOrders_MonotoneConvex_IcxOrder
import Definitions.Def_StochasticOrders_MonotoneConvex_IcvOrder

namespace StochasticOrders.MonotoneConvex

open MeasureTheory ProbabilityTheory Filter Topology

/-- measure-level increasing convex order -/
def aux_icc_MIcx (P Q : Measure ℝ) : Prop :=
  ∀ φ : ℝ → ℝ, Monotone φ → ConvexOn ℝ Set.univ φ → Integrable φ P → Integrable φ Q →
    ∫ x, φ x ∂P ≤ ∫ x, φ x ∂Q

/-- lintegral version for bounded-below functions -/
def aux_icc_LIcx (P Q : Measure ℝ) : Prop :=
  ∀ (ψ : ℝ → ℝ) (c : ℝ), Monotone ψ → ConvexOn ℝ Set.univ ψ → (∀ x, c ≤ ψ x) →
    ∫⁻ x, ENNReal.ofReal (ψ x - c) ∂P ≤ ∫⁻ x, ENNReal.ofReal (ψ x - c) ∂Q

lemma aux_icc_subgrad {ψ : ℝ → ℝ} (hc : ConvexOn ℝ Set.univ ψ) (b y : ℝ) :
    ψ b + derivWithin ψ (Set.Ioi b) b * (y - b) ≤ ψ y := by
  have hb : b ∈ interior (Set.univ : Set ℝ) := by simp
  rcases lt_trichotomy y b with hyb | rfl | hyb
  · have h1 := hc.slope_le_leftDeriv_of_mem_interior (Set.mem_univ y) hb hyb
    have h2 := hc.leftDeriv_le_rightDeriv_of_mem_interior hb
    have h3 : slope ψ y b ≤ derivWithin ψ (Set.Ioi b) b := h1.trans h2
    rw [slope_def_field, div_le_iff₀ (by linarith)] at h3
    nlinarith
  · simp
  · have h3 := hc.rightDeriv_le_slope_of_mem_interior hb (Set.mem_univ y) hyb
    rw [slope_def_field, le_div_iff₀ (by linarith)] at h3
    nlinarith

lemma aux_icc_subgrad_nonneg {ψ : ℝ → ℝ} (hm : Monotone ψ) (hc : ConvexOn ℝ Set.univ ψ) (b : ℝ) :
    0 ≤ derivWithin ψ (Set.Ioi b) b := by
  have hb : b ∈ interior (Set.univ : Set ℝ) := by simp
  have h1 := hc.slope_le_leftDeriv_of_mem_interior (Set.mem_univ (b - 1)) hb (by linarith)
  have h2 := hc.leftDeriv_le_rightDeriv_of_mem_interior hb
  have h4 : ψ (b - 1) ≤ ψ b := hm (by linarith)
  have h5 : 0 ≤ slope ψ (b - 1) b := by
    rw [slope_def_field]; apply div_nonneg <;> linarith
  linarith

lemma aux_icc_trunc_convex {ψ : ℝ → ℝ} (hc : ConvexOn ℝ Set.univ ψ) (b d : ℝ)
    (hsub : ∀ y, ψ b + d * (y - b) ≤ ψ y) :
    ConvexOn ℝ Set.univ (fun x => ψ (min x b) + d * max (x - b) 0) := by
  have hle : ∀ t, t ≤ b → ψ (min t b) + d * max (t - b) 0 = ψ t := by
    intro t ht
    rw [min_eq_left ht, max_eq_right (by linarith)]; ring
  have hge : ∀ t, b ≤ t → ψ (min t b) + d * max (t - b) 0 = ψ b + d * (t - b) := by
    intro t ht
    rw [min_eq_right ht, max_eq_left (by linarith)]
  refine convexOn_of_slope_mono_adjacent convex_univ ?_
  intro x y z _ _ hxy hyz
  rw [div_le_div_iff₀ (by linarith) (by linarith)]
  rcases le_or_gt z b with hzb | hzb
  · rw [hle x (by linarith), hle y (by linarith), hle z hzb]
    have := hc.slope_mono_adjacent (Set.mem_univ x) (Set.mem_univ z) hxy hyz
    rwa [div_le_div_iff₀ (by linarith) (by linarith)] at this
  rcases le_or_gt b x with hbx | hbx
  · rw [hge x hbx, hge y (by linarith), hge z (by linarith)]
    ring_nf; exact le_refl _
  rcases lt_trichotomy y b with hyb | rfl | hyb
  · rw [hle x (by linarith), hle y (by linarith), hge z (by linarith)]
    have h1 := hc.slope_mono_adjacent (Set.mem_univ x) (Set.mem_univ b) hxy hyb
    rw [div_le_div_iff₀ (by linarith) (by linarith)] at h1
    have h2 := hsub y
    have key : (ψ y - ψ x) * (z - y) * (b - y) ≤
        (ψ b + d * (z - b) - ψ y) * (y - x) * (b - y) := by
      nlinarith [mul_le_mul_of_nonneg_right h1 (show (0:ℝ) ≤ z - y by linarith),
        mul_le_mul_of_nonneg_right h2 (show (0:ℝ) ≤ (y - x) * (z - y) by nlinarith),
        mul_nonneg (show (0:ℝ) ≤ y - x by linarith) (show (0:ℝ) ≤ z - b by linarith)]
    exact le_of_mul_le_mul_right key (by linarith)
  · rw [hle x (by linarith), hle y le_rfl, hge z (by linarith)]
    have h2 := hsub x
    nlinarith [mul_le_mul_of_nonneg_right h2 (show (0:ℝ) ≤ z - y by linarith)]
  · rw [hle x (by linarith), hge y (by linarith), hge z (by linarith)]
    have h2 := hsub x
    nlinarith [mul_le_mul_of_nonneg_right h2 (show (0:ℝ) ≤ z - y by linarith)]

lemma aux_icc_mom_iff (P : Measure ℝ) :
    Integrable (fun x : ℝ => max x 0) P ↔ ∫⁻ x, ENNReal.ofReal x ∂P ≠ ⊤ := by
  have hmeas : AEStronglyMeasurable (fun x : ℝ => max x 0) P :=
    (continuous_id.max continuous_const).aestronglyMeasurable
  have heq : ∀ x : ℝ, ENNReal.ofReal (max x 0) = ENNReal.ofReal x := by
    intro x; rcases le_total x 0 with h | h
    · rw [max_eq_right h, ENNReal.ofReal_zero, ENNReal.ofReal_of_nonpos h]
    · rw [max_eq_left h]
  have hnn : 0 ≤ᵐ[P] (fun x : ℝ => max x 0) := ae_of_all _ (fun x => by simp)
  constructor
  · intro h
    have := (hasFiniteIntegral_iff_ofReal hnn).mp h.2
    simp only [heq] at this
    exact this.ne
  · intro h
    refine ⟨hmeas, (hasFiniteIntegral_iff_ofReal hnn).mpr ?_⟩
    simp only [heq]; exact lt_top_iff_ne_top.mpr h

lemma aux_icc_S {P Q : Measure ℝ} [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (h : aux_icc_MIcx P Q) (hmom : ∫⁻ x, ENNReal.ofReal x ∂P ≠ ⊤) : aux_icc_LIcx P Q := by
  intro ψ c hm hc hlow
  by_cases hQ : ∫⁻ x, ENNReal.ofReal (ψ x - c) ∂Q = ⊤
  · rw [hQ]; exact le_top
  have hψmeas : Measurable ψ := hm.measurable
  have hψcQ : Integrable (fun x => ψ x - c) Q := by
    refine ⟨(hψmeas.sub_const c).aestronglyMeasurable, ?_⟩
    rw [hasFiniteIntegral_iff_ofReal (ae_of_all _ (fun x => by simp [hlow x]))]
    exact lt_top_iff_ne_top.mpr hQ
  have hψQ : Integrable ψ Q := by
    exact (hψcQ.add (integrable_const c)).congr (ae_of_all _ (fun x => by simp))
  have hmaxP : Integrable (fun x : ℝ => max x 0) P := (aux_icc_mom_iff P).mpr hmom
  set R : ℕ → ℝ → ℝ := fun n x =>
    ψ (min x n) + derivWithin ψ (Set.Ioi (n:ℝ)) n * max (x - n) 0 with hR
  have hd0 : ∀ n : ℕ, 0 ≤ derivWithin ψ (Set.Ioi (n:ℝ)) n :=
    fun n => aux_icc_subgrad_nonneg hm hc n
  have hRmono : ∀ n, Monotone (R n) := by
    intro n a b hab
    simp only [hR]
    have h1 : ψ (min a n) ≤ ψ (min b n) := hm (min_le_min_right _ hab)
    have h2 : max (a - n) 0 ≤ max (b - n) 0 := max_le_max (by linarith) le_rfl
    nlinarith [mul_le_mul_of_nonneg_left h2 (hd0 n)]
  have hRconv : ∀ n, ConvexOn ℝ Set.univ (R n) := fun n =>
    aux_icc_trunc_convex hc n _ (aux_icc_subgrad hc n)
  have hRlow : ∀ n x, c ≤ R n x := by
    intro n x
    simp only [hR]
    have := hlow (min x n)
    nlinarith [mul_nonneg (hd0 n) (le_max_right (x - n) 0)]
  have hRle : ∀ n x, R n x ≤ ψ x := by
    intro n x
    simp only [hR]
    rcases le_total x n with hx | hx
    · rw [min_eq_left hx, max_eq_right (by linarith)]; simp
    · rw [min_eq_right hx, max_eq_left (by linarith)]
      exact aux_icc_subgrad hc n x
  have hRup : ∀ n x, R n x ≤ ψ n + derivWithin ψ (Set.Ioi (n:ℝ)) n * max x 0 := by
    intro n x
    simp only [hR]
    have h1 : ψ (min x n) ≤ ψ n := hm (min_le_right _ _)
    have hn0 : (0:ℝ) ≤ n := n.cast_nonneg
    have h2 : max (x - n) 0 ≤ max x 0 := max_le_max (by linarith) le_rfl
    nlinarith [mul_le_mul_of_nonneg_left h2 (hd0 n)]
  have hRP : ∀ n, Integrable (R n) P := by
    intro n
    refine Integrable.mono' ((hmaxP.const_mul (derivWithin ψ (Set.Ioi (n:ℝ)) n)).add
      (integrable_const (|c| + |ψ n|))) (hRmono n).measurable.aestronglyMeasurable
      (ae_of_all _ (fun x => ?_))
    show ‖R n x‖ ≤ derivWithin ψ (Set.Ioi (n:ℝ)) n * max x 0 + (|c| + |ψ n|)
    rw [Real.norm_eq_abs, abs_le]
    have := hRlow n x; have := hRup n x
    constructor
    · nlinarith [neg_abs_le c, abs_nonneg (ψ n), mul_nonneg (hd0 n) (le_max_right x 0)]
    · nlinarith [le_abs_self (ψ n), abs_nonneg c]
  have hRQ : ∀ n, Integrable (R n) Q := by
    intro n
    refine Integrable.mono' (hψQ.norm.add (integrable_const |c|))
      (hRmono n).measurable.aestronglyMeasurable (ae_of_all _ (fun x => ?_))
    show ‖R n x‖ ≤ ‖ψ x‖ + |c|
    rw [Real.norm_eq_abs, abs_le]
    have := hRlow n x; have := hRle n x
    have : ψ x ≤ ‖ψ x‖ := Real.le_norm_self _
    constructor
    · nlinarith [neg_abs_le c, norm_nonneg (ψ x)]
    · nlinarith [abs_nonneg c]
  have hstep : ∀ n, ∫⁻ x, ENNReal.ofReal (R n x - c) ∂P ≤
      ∫⁻ x, ENNReal.ofReal (ψ x - c) ∂Q := by
    intro n
    have h1 := h (R n) (hRmono n) (hRconv n) (hRP n) (hRQ n)
    have h2 : ∫ x, R n x ∂Q ≤ ∫ x, ψ x ∂Q := integral_mono (hRQ n) hψQ (hRle n)
    have hRPc : Integrable (fun x => R n x - c) P := (hRP n).sub (integrable_const c)
    rw [← ofReal_integral_eq_lintegral_ofReal hRPc
        (ae_of_all _ (fun x => by simp [hRlow n x])),
      ← ofReal_integral_eq_lintegral_ofReal hψcQ (ae_of_all _ (fun x => by simp [hlow x]))]
    apply ENNReal.ofReal_le_ofReal
    rw [integral_sub (hRP n) (integrable_const c), integral_sub hψQ (integrable_const c)]
    simp only [integral_const, probReal_univ, one_smul]
    linarith
  have hlim : ∀ x, liminf (fun n : ℕ => ENNReal.ofReal (R n x - c)) atTop =
      ENNReal.ofReal (ψ x - c) := by
    intro x
    apply Tendsto.liminf_eq
    apply tendsto_const_nhds.congr'
    filter_upwards [eventually_ge_atTop ⌈x⌉₊] with n hn
    have hxn : x ≤ n := (Nat.le_ceil x).trans (by exact_mod_cast hn)
    simp only [hR, min_eq_left hxn, max_eq_right (by linarith : x - n ≤ 0), mul_zero, add_zero]
  calc ∫⁻ x, ENNReal.ofReal (ψ x - c) ∂P
      = ∫⁻ x, liminf (fun n : ℕ => ENNReal.ofReal (R n x - c)) atTop ∂P := by simp_rw [hlim]
    _ ≤ liminf (fun n : ℕ => ∫⁻ x, ENNReal.ofReal (R n x - c) ∂P) atTop :=
        lintegral_liminf_le (fun n => ((hRmono n).measurable.sub_const c).ennreal_ofReal)
    _ ≤ ∫⁻ x, ENNReal.ofReal (ψ x - c) ∂Q :=
        liminf_le_of_frequently_le' (Frequently.of_forall hstep)

lemma aux_icc_shift {ψ : ℝ → ℝ} (hc : ConvexOn ℝ Set.univ ψ) (t : ℝ) :
    ConvexOn ℝ Set.univ (fun y => ψ (y + t)) := by
  refine ⟨convex_univ, fun x _ y _ a b ha hb hab => ?_⟩
  have := hc.2 (Set.mem_univ (x + t)) (Set.mem_univ (y + t)) ha hb hab
  simp only [smul_eq_mul] at this ⊢
  have e : a * x + b * y + t = a * (x + t) + b * (y + t) := by
    calc a * x + b * y + t = a * x + b * y + (a + b) * t := by rw [hab, one_mul]
      _ = a * (x + t) + b * (y + t) := by ring
  rw [e]; exact this

lemma aux_icc_max_const {φ : ℝ → ℝ} (hc : ConvexOn ℝ Set.univ φ) (c : ℝ) :
    ConvexOn ℝ Set.univ (fun x => max (φ x) c) := by
  refine ⟨convex_univ, fun x _ y _ a b ha hb hab => ?_⟩
  have h1 := hc.2 (Set.mem_univ x) (Set.mem_univ y) ha hb hab
  simp only [smul_eq_mul] at h1 ⊢
  have e : a * c + b * c = c := by rw [← add_mul, hab, one_mul]
  apply max_le
  · nlinarith [mul_le_mul_of_nonneg_left (le_max_left (φ x) c) ha,
      mul_le_mul_of_nonneg_left (le_max_left (φ y) c) hb]
  · nlinarith [mul_le_mul_of_nonneg_left (le_max_right (φ x) c) ha,
      mul_le_mul_of_nonneg_left (le_max_right (φ y) c) hb]

lemma aux_icc_conv {P1 Q1 P2 Q2 : Measure ℝ} [IsProbabilityMeasure P1] [IsProbabilityMeasure Q1]
    [IsProbabilityMeasure P2] [IsProbabilityMeasure Q2]
    (h1 : aux_icc_LIcx P1 Q1) (h2 : aux_icc_LIcx P2 Q2) :
    aux_icc_LIcx (P1 ∗ P2) (Q1 ∗ Q2) := by
  intro ψ c hm hc hlow
  have hg : Measurable (fun x => ENNReal.ofReal (ψ x - c)) :=
    (hm.measurable.sub_const c).ennreal_ofReal
  rw [Measure.lintegral_conv hg, Measure.lintegral_conv hg]
  have hmx : ∀ x : ℝ, Monotone (fun y => ψ (x + y)) := fun x a b hab => hm (by linarith)
  have hmy : ∀ y : ℝ, Monotone (fun x => ψ (x + y)) := fun y a b hab => hm (by linarith)
  have hcx : ∀ x : ℝ, ConvexOn ℝ Set.univ (fun y => ψ (x + y)) := fun x => by
    have := aux_icc_shift hc x
    convert this using 1
    funext y; rw [add_comm]
  have hcy : ∀ y : ℝ, ConvexOn ℝ Set.univ (fun x => ψ (x + y)) := fun y => aux_icc_shift hc y
  have hA : Measurable (Function.uncurry fun (x y : ℝ) => ENNReal.ofReal (ψ (x + y) - c)) :=
    hg.comp measurable_add
  have hB : Measurable (Function.uncurry fun (y x : ℝ) => ENNReal.ofReal (ψ (x + y) - c)) :=
    hg.comp (measurable_snd.add measurable_fst)
  calc ∫⁻ x, ∫⁻ y, ENNReal.ofReal (ψ (x + y) - c) ∂P2 ∂P1
      ≤ ∫⁻ x, ∫⁻ y, ENNReal.ofReal (ψ (x + y) - c) ∂Q2 ∂P1 :=
        lintegral_mono (fun x => h2 _ c (hmx x) (hcx x) (fun y => hlow _))
    _ = ∫⁻ y, ∫⁻ x, ENNReal.ofReal (ψ (x + y) - c) ∂P1 ∂Q2 :=
        lintegral_lintegral_swap hA.aemeasurable
    _ ≤ ∫⁻ y, ∫⁻ x, ENNReal.ofReal (ψ (x + y) - c) ∂Q1 ∂Q2 :=
        lintegral_mono (fun y => h1 _ c (hmy y) (hcy y) (fun x => hlow _))
    _ = ∫⁻ x, ∫⁻ y, ENNReal.ofReal (ψ (x + y) - c) ∂Q2 ∂Q1 :=
        lintegral_lintegral_swap hB.aemeasurable

lemma aux_icc_mom_right {P1 P2 : Measure ℝ} [IsProbabilityMeasure P1] [IsProbabilityMeasure P2]
    (h : ∫⁻ z, ENNReal.ofReal z ∂(P1 ∗ P2) ≠ ⊤) : ∫⁻ y, ENNReal.ofReal y ∂P2 ≠ ⊤ := by
  rw [Measure.lintegral_conv ENNReal.measurable_ofReal] at h
  have : ∃ x, ∫⁻ y, ENNReal.ofReal (x + y) ∂P2 ≠ ⊤ := by
    by_contra hne
    push Not at hne
    apply h
    simp [hne]
  obtain ⟨x, hx⟩ := this
  have hle : ∀ y, ENNReal.ofReal y ≤ ENNReal.ofReal (x + y) + ENNReal.ofReal (-x) := by
    intro y
    calc ENNReal.ofReal y = ENNReal.ofReal ((x + y) + -x) := by ring_nf
      _ ≤ _ := ENNReal.ofReal_add_le
  refine ne_top_of_le_ne_top ?_ (lintegral_mono hle)
  rw [lintegral_add_right _ measurable_const, lintegral_const]
  exact ENNReal.add_ne_top.mpr ⟨hx, by simp⟩

lemma aux_icc_mom_left {P1 P2 : Measure ℝ} [IsProbabilityMeasure P1] [IsProbabilityMeasure P2]
    (h : ∫⁻ z, ENNReal.ofReal z ∂(P1 ∗ P2) ≠ ⊤) : ∫⁻ y, ENNReal.ofReal y ∂P1 ≠ ⊤ := by
  rw [Measure.conv_comm] at h
  exact aux_icc_mom_right h

lemma aux_icc_final {P Q : Measure ℝ} [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (h : ∫⁻ x, ENNReal.ofReal x ∂P ≠ ⊤ → aux_icc_LIcx P Q) : aux_icc_MIcx P Q := by
  intro φ hm hc hP hQ
  by_cases hnc : ∃ u v, u < v ∧ φ u < φ v
  · obtain ⟨u, v, huv, hφ⟩ := hnc
    set k := (φ v - φ u) / (v - u) with hk
    have hkpos : 0 < k := div_pos (by linarith) (by linarith)
    have hbound : ∀ x, max x 0 ≤ |v| + (|φ x| + |φ v|) / k := by
      intro x
      have h0 : 0 ≤ (|φ x| + |φ v|) / k := div_nonneg (by positivity) hkpos.le
      rcases le_or_gt x v with hxv | hxv
      · have : max x 0 ≤ max v 0 := max_le_max hxv le_rfl
        have : max v 0 ≤ |v| := max_le (le_abs_self v) (abs_nonneg v)
        linarith
      · have hsl := hc.slope_mono_adjacent (Set.mem_univ u) (Set.mem_univ x) huv hxv
        rw [← hk, le_div_iff₀ (by linarith)] at hsl
        have h3 : x - v ≤ (|φ x| + |φ v|) / k := by
          rw [le_div_iff₀ hkpos]
          nlinarith [le_abs_self (φ x), neg_abs_le (φ v)]
        have : max x 0 ≤ x - v + |v| :=
          max_le (by linarith [le_abs_self v]) (by linarith [abs_nonneg v])
        linarith
    have hmaxP : Integrable (fun x : ℝ => max x 0) P := by
      refine Integrable.mono' ((integrable_const |v|).add
        ((hP.norm.add (integrable_const |φ v|)).div_const k))
        (continuous_id.max continuous_const).aestronglyMeasurable (ae_of_all _ (fun x => ?_))
      show ‖max x 0‖ ≤ |v| + (‖φ x‖ + |φ v|) / k
      rw [Real.norm_eq_abs, abs_of_nonneg (le_max_right x 0), Real.norm_eq_abs]
      exact hbound x
    have hL := h ((aux_icc_mom_iff P).mp hmaxP)
    set F : ℕ → ℝ → ℝ := fun n x => max (φ x) (φ (-(n:ℝ))) with hF
    have hFint : ∀ (μ : Measure ℝ) [IsProbabilityMeasure μ], Integrable φ μ →
        ∀ n, Integrable (F n) μ := by
      intro μ _ hμ n
      refine Integrable.mono' (hμ.norm.add (integrable_const |φ (-(n:ℝ))|))
        ((hm.measurable.max measurable_const).aestronglyMeasurable) (ae_of_all _ (fun x => ?_))
      show ‖max (φ x) (φ (-(n:ℝ)))‖ ≤ ‖φ x‖ + |φ (-(n:ℝ))|
      rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_le]
      constructor
      · nlinarith [neg_abs_le (φ x), abs_nonneg (φ (-(n:ℝ))), le_max_left (φ x) (φ (-(n:ℝ)))]
      · apply max_le <;> nlinarith [le_abs_self (φ x), abs_nonneg (φ x),
          le_abs_self (φ (-(n:ℝ))), abs_nonneg (φ (-(n:ℝ)))]
    have hstep : ∀ n, ∫ x, F n x ∂P ≤ ∫ x, F n x ∂Q := by
      intro n
      have hmn : Monotone (F n) := fun a b hab => max_le_max (hm hab) le_rfl
      have hcn : ConvexOn ℝ Set.univ (F n) := aux_icc_max_const hc _
      have hl := hL (F n) (φ (-(n:ℝ))) hmn hcn (fun x => le_max_right _ _)
      have hPi : Integrable (fun x => F n x - φ (-(n:ℝ))) P :=
        (hFint P hP n).sub (integrable_const _)
      have hQi : Integrable (fun x => F n x - φ (-(n:ℝ))) Q :=
        (hFint Q hQ n).sub (integrable_const _)
      rw [← ofReal_integral_eq_lintegral_ofReal hPi (ae_of_all _ (fun x => by simp [hF])),
        ← ofReal_integral_eq_lintegral_ofReal hQi (ae_of_all _ (fun x => by simp [hF]))] at hl
      rw [ENNReal.ofReal_le_ofReal_iff (integral_nonneg (fun x => by simp [hF]))] at hl
      rw [integral_sub (hFint P hP n) (integrable_const _),
        integral_sub (hFint Q hQ n) (integrable_const _)] at hl
      simp only [integral_const, probReal_univ, one_smul] at hl
      linarith
    have hlim : ∀ (μ : Measure ℝ) [IsProbabilityMeasure μ], Integrable φ μ →
        Tendsto (fun n => ∫ x, F n x ∂μ) atTop (𝓝 (∫ x, φ x ∂μ)) := by
      intro μ _ hμ
      refine tendsto_integral_of_dominated_convergence (fun x => ‖φ x‖ + |φ 0|)
        (fun n => (hFint μ hμ n).aestronglyMeasurable) (hμ.norm.add (integrable_const _)) ?_ ?_
      · intro n
        refine ae_of_all _ (fun x => ?_)
        have h0 : φ (-(n:ℝ)) ≤ φ 0 := hm (by simp)
        show ‖max (φ x) (φ (-(n:ℝ)))‖ ≤ ‖φ x‖ + |φ 0|
        rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_le]
        constructor
        · nlinarith [neg_abs_le (φ x), abs_nonneg (φ 0), le_max_left (φ x) (φ (-(n:ℝ)))]
        · apply max_le <;> nlinarith [le_abs_self (φ x), abs_nonneg (φ x), le_abs_self (φ 0),
            abs_nonneg (φ 0)]
      · refine ae_of_all _ (fun x => ?_)
        apply tendsto_const_nhds.congr'
        filter_upwards [eventually_ge_atTop ⌈-x⌉₊] with n hn
        have hxn : -(n:ℝ) ≤ x := by
          have := (Nat.le_ceil (-x)).trans (show ((⌈-x⌉₊ : ℕ) : ℝ) ≤ n by exact_mod_cast hn)
          linarith
        simp only [hF, max_eq_left (hm hxn)]
    exact le_of_tendsto_of_tendsto' (hlim P hP) (hlim Q hQ) hstep
  · push Not at hnc
    have hconst : ∀ x, φ x = φ 0 := by
      intro x
      rcases lt_trichotomy x 0 with hx | hx | hx
      · exact le_antisymm (hm hx.le) (hnc x 0 hx)
      · rw [hx]
      · exact le_antisymm (hnc 0 x hx) (hm hx.le)
    have key : ∀ (μ : Measure ℝ) [IsProbabilityMeasure μ], ∫ x, φ x ∂μ = φ 0 := by
      intro μ _
      calc ∫ x, φ x ∂μ = ∫ _, φ 0 ∂μ := integral_congr_ae (ae_of_all _ hconst)
        _ = φ 0 := by simp
    rw [key P, key Q]

lemma aux_icc_toM {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    {μ : Measure Ω} {ν : Measure Ω'} {X : Ω → ℝ} {Y : Ω' → ℝ} (hX : Measurable X)
    (hY : Measurable Y) (h : IcxOrder μ ν X Y) : aux_icc_MIcx (μ.map X) (ν.map Y) := by
  intro φ hm hc hP hQ
  have hφ := hm.measurable
  rw [integral_map hX.aemeasurable hφ.aestronglyMeasurable,
    integral_map hY.aemeasurable hφ.aestronglyMeasurable]
  exact h φ hm hc ((integrable_map_measure hφ.aestronglyMeasurable hX.aemeasurable).mp hP)
    ((integrable_map_measure hφ.aestronglyMeasurable hY.aemeasurable).mp hQ)

lemma aux_icc_ofM {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    {μ : Measure Ω} {ν : Measure Ω'} {X : Ω → ℝ} {Y : Ω' → ℝ} (hX : Measurable X)
    (hY : Measurable Y) (h : aux_icc_MIcx (μ.map X) (ν.map Y)) : IcxOrder μ ν X Y := by
  intro φ hm hc hP hQ
  have hφ := hm.measurable
  have := h φ hm hc ((integrable_map_measure hφ.aestronglyMeasurable hX.aemeasurable).mpr hP)
    ((integrable_map_measure hφ.aestronglyMeasurable hY.aemeasurable).mpr hQ)
  rwa [integral_map hX.aemeasurable hφ.aestronglyMeasurable,
    integral_map hY.aemeasurable hφ.aestronglyMeasurable] at this

lemma aux_icc_ind {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    (μ : Measure Ω) (ν : Measure Ω') [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {m : ℕ} (X : Fin m → Ω → ℝ) (Y : Fin m → Ω' → ℝ) (hX : ∀ i, Measurable (X i))
    (hY : ∀ i, Measurable (Y i)) (hXindep : iIndepFun X μ) (hYindep : iIndepFun Y ν)
    (hM : ∀ i, aux_icc_MIcx (μ.map (X i)) (ν.map (Y i))) (s : Finset (Fin m)) :
    ∫⁻ z, ENNReal.ofReal z ∂(μ.map (fun ω => ∑ i ∈ s, X i ω)) ≠ ⊤ →
      aux_icc_LIcx (μ.map (fun ω => ∑ i ∈ s, X i ω)) (ν.map (fun ω => ∑ i ∈ s, Y i ω)) := by
  induction s using Finset.induction_on with
  | empty =>
    intro _
    simp only [Finset.sum_empty, Measure.map_const, measure_univ, one_smul]
    intro ψ c _ _ _
    exact le_rfl
  | insert j s hj ih =>
    intro hmom
    have hXs : Measurable (fun ω => ∑ i ∈ s, X i ω) := Finset.measurable_sum s (fun i _ => hX i)
    have hYs : Measurable (fun ω => ∑ i ∈ s, Y i ω) := Finset.measurable_sum s (fun i _ => hY i)
    have hIX : IndepFun (X j) (fun ω => ∑ i ∈ s, X i ω) μ := by
      have := (hXindep.indepFun_finsetSum_of_notMem hX hj).symm
      convert this using 1
      funext ω; simp [Finset.sum_apply]
    have hIY : IndepFun (Y j) (fun ω => ∑ i ∈ s, Y i ω) ν := by
      have := (hYindep.indepFun_finsetSum_of_notMem hY hj).symm
      convert this using 1
      funext ω; simp [Finset.sum_apply]
    have eX : μ.map (fun ω => ∑ i ∈ insert j s, X i ω) =
        μ.map (X j) ∗ μ.map (fun ω => ∑ i ∈ s, X i ω) := by
      rw [← hIX.map_add_eq_map_conv_map (hX j) hXs]
      congr 1; funext ω; simp [Finset.sum_insert hj]
    have eY : ν.map (fun ω => ∑ i ∈ insert j s, Y i ω) =
        ν.map (Y j) ∗ ν.map (fun ω => ∑ i ∈ s, Y i ω) := by
      rw [← hIY.map_add_eq_map_conv_map (hY j) hYs]
      congr 1; funext ω; simp [Finset.sum_insert hj]
    have := Measure.isProbabilityMeasure_map (μ := μ) (hX j).aemeasurable
    have := Measure.isProbabilityMeasure_map (μ := μ) hXs.aemeasurable
    have := Measure.isProbabilityMeasure_map (μ := ν) (hY j).aemeasurable
    have := Measure.isProbabilityMeasure_map (μ := ν) hYs.aemeasurable
    rw [eX] at hmom ⊢
    rw [eY]
    exact aux_icc_conv (aux_icc_S (hM j) (aux_icc_mom_left hmom)) (ih (aux_icc_mom_right hmom))

lemma aux_icc_icx {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    (μ : Measure Ω) (ν : Measure Ω') [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {m : ℕ} (X : Fin m → Ω → ℝ) (Y : Fin m → Ω' → ℝ) (hX : ∀ i, Measurable (X i))
    (hY : ∀ i, Measurable (Y i)) (hXindep : iIndepFun X μ) (hYindep : iIndepFun Y ν)
    (h : ∀ i, IcxOrder μ ν (X i) (Y i)) :
    IcxOrder μ ν (fun ω => ∑ i, X i ω) (fun ω => ∑ i, Y i ω) := by
  have hXs : Measurable (fun ω => ∑ i, X i ω) := Finset.measurable_sum _ (fun i _ => hX i)
  have hYs : Measurable (fun ω => ∑ i, Y i ω) := Finset.measurable_sum _ (fun i _ => hY i)
  have := Measure.isProbabilityMeasure_map (μ := μ) hXs.aemeasurable
  have := Measure.isProbabilityMeasure_map (μ := ν) hYs.aemeasurable
  apply aux_icc_ofM hXs hYs
  exact aux_icc_final (aux_icc_ind μ ν X Y hX hY hXindep hYindep
    (fun i => aux_icc_toM (hX i) (hY i) (h i)) Finset.univ)

lemma aux_icc_neg_convex {φ : ℝ → ℝ} (hc : ConcaveOn ℝ Set.univ φ) :
    ConvexOn ℝ Set.univ (fun t => -φ (-t)) := by
  refine ⟨convex_univ, fun x _ y _ a b ha hb hab => ?_⟩
  have := hc.2 (Set.mem_univ (-x)) (Set.mem_univ (-y)) ha hb hab
  simp only [smul_eq_mul] at this ⊢
  have e : -(a * x + b * y) = a * -x + b * -y := by ring
  rw [e]; linarith

lemma aux_icc_neg_concave {ψ : ℝ → ℝ} (hc : ConvexOn ℝ Set.univ ψ) :
    ConcaveOn ℝ Set.univ (fun t => -ψ (-t)) := by
  refine ⟨convex_univ, fun x _ y _ a b ha hb hab => ?_⟩
  have := hc.2 (Set.mem_univ (-x)) (Set.mem_univ (-y)) ha hb hab
  simp only [smul_eq_mul] at this ⊢
  have e : -(a * x + b * y) = a * -x + b * -y := by ring
  rw [e]; linarith

lemma aux_icc_icv_of {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    {μ : Measure Ω} {ν : Measure Ω'} {X : Ω → ℝ} {Y : Ω' → ℝ}
    (h : IcxOrder ν μ (fun ω => -Y ω) (fun ω => -X ω)) : IcvOrder μ ν X Y := by
  intro φ hm hc hX hY
  have h1 := h (fun t => -φ (-t)) (fun a b hab => by simpa using hm (neg_le_neg hab))
    (aux_icc_neg_convex hc)
    (by simpa [Function.comp_def] using hY.neg)
    (by simpa [Function.comp_def] using hX.neg)
  simp only [neg_neg, integral_neg] at h1
  linarith

lemma aux_icc_icx_of {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    {μ : Measure Ω} {ν : Measure Ω'} {X : Ω → ℝ} {Y : Ω' → ℝ}
    (h : IcvOrder μ ν X Y) : IcxOrder ν μ (fun ω => -Y ω) (fun ω => -X ω) := by
  intro ψ hm hc hY hX
  have h1 := h (fun t => -ψ (-t)) (fun a b hab => by simpa using hm (neg_le_neg hab))
    (aux_icc_neg_concave hc)
    (by simpa [Function.comp_def] using hX.neg)
    (by simpa [Function.comp_def] using hY.neg)
  simp only [integral_neg] at h1
  show ∫ ω, ψ (-Y ω) ∂ν ≤ ∫ ω, ψ (-X ω) ∂μ
  linarith

end StochasticOrders.MonotoneConvex

open StochasticOrders.MonotoneConvex
open MeasureTheory ProbabilityTheory

theorem solution {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    (μ : Measure Ω) (ν : Measure Ω') [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {m : ℕ} (X : Fin m → Ω → ℝ) (Y : Fin m → Ω' → ℝ) (hX : ∀ i, Measurable (X i))
    (hY : ∀ i, Measurable (Y i)) (hXindep : iIndepFun X μ) (hYindep : iIndepFun Y ν) :
    ((∀ i, IcxOrder μ ν (X i) (Y i)) →
      IcxOrder μ ν (fun ω => ∑ i, X i ω) (fun ω => ∑ i, Y i ω))
    ∧
    ((∀ i, IcvOrder μ ν (X i) (Y i)) →
      IcvOrder μ ν (fun ω => ∑ i, X i ω) (fun ω => ∑ i, Y i ω)) := by
  refine ⟨aux_icc_icx μ ν X Y hX hY hXindep hYindep, fun h => ?_⟩
  apply aux_icc_icv_of
  have hnY : iIndepFun (fun i ω => -Y i ω) ν :=
    hYindep.comp (fun _ => Neg.neg) (fun _ => measurable_neg)
  have hnX : iIndepFun (fun i ω => -X i ω) μ :=
    hXindep.comp (fun _ => Neg.neg) (fun _ => measurable_neg)
  have := aux_icc_icx ν μ (fun i ω => -Y i ω) (fun i ω => -X i ω) (fun i => (hY i).neg)
    (fun i => (hX i).neg) hnY hnX (fun i => aux_icc_icx_of (h i))
  simpa [Finset.sum_neg_distrib] using this
