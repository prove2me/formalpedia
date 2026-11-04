-- Prove2me | solution 1 for TaoBR.restr_sparse_of_restr_uniform
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-03T16:26:59.341365+00:00
-- url     : https://prove2.me/submissions/5a768b3f-f1e9-4f8a-9b46-8d4a35058b47

import Definitions.Def_TaoBR
import Mathlib

section
section
/-!
# A Marcinkiewicz-type interpolation step between strong (1,1) and (2,2) bounds
-/

open MeasureTheory Set Filter
open scoped ENNReal NNReal

namespace TaoBR.RSU

noncomputable def truncHi {ι X : Type*} (G : ι → X → ℂ) (t : ℝ) : ι → X → ℂ :=
  fun i x => if t < ‖G i x‖ then G i x else 0

noncomputable def truncLo {ι X : Type*} (G : ι → X → ℂ) (t : ℝ) : ι → X → ℂ :=
  fun i x => if t < ‖G i x‖ then 0 else G i x

lemma truncHi_add_truncLo {ι X : Type*} (G : ι → X → ℂ) (t : ℝ) :
    truncHi G t + truncLo G t = G := by
  funext i x
  simp only [truncHi, truncLo, Pi.add_apply]
  split_ifs <;> simp

lemma enorm_truncHi {ι X : Type*} (G : ι → X → ℂ) (t : ℝ) (i : ι) (x : X) :
    ‖truncHi G t i x‖ₑ = if t < ‖G i x‖ then ENNReal.ofReal ‖G i x‖ else 0 := by
  simp only [truncHi]; split_ifs <;> simp

lemma enorm_truncLo_sq {ι X : Type*} (G : ι → X → ℂ) (t : ℝ) (i : ι) (x : X) :
    ‖truncLo G t i x‖ₑ ^ (2 : ℝ) = if t < ‖G i x‖ then 0 else ENNReal.ofReal (‖G i x‖ ^ 2) := by
  simp only [truncLo]; split_ifs
  · simp
  · rw [← ofReal_norm, ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) (by norm_num)]
    norm_num

/-- `∫_0^s t^(q-2) dt = s^(q-1)/(q-1)`. -/
lemma lint_low {q : ℝ} (hq1 : 1 < q) {s : ℝ} (hs : 0 ≤ s) :
    ∫⁻ t in Ioo 0 s, ENNReal.ofReal (t ^ (q - 2)) = ENNReal.ofReal (s ^ (q - 1) / (q - 1)) := by
  have hint : IntervalIntegrable (fun t : ℝ => t ^ (q - 2)) volume 0 s :=
    intervalIntegral.intervalIntegrable_rpow' (by linarith)
  have hio : IntegrableOn (fun t : ℝ => t ^ (q - 2)) (Ioo 0 s) :=
    ((intervalIntegrable_iff_integrableOn_Ioc_of_le hs).1 hint).mono_set Ioo_subset_Ioc_self
  rw [← ofReal_integral_eq_lintegral_ofReal hio]
  · congr 1
    rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le hs,
      integral_rpow (Or.inl (by linarith))]
    rw [show q - 2 + 1 = q - 1 by ring, Real.zero_rpow (by linarith)]
    ring
  · filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
    exact Real.rpow_nonneg ht.1.le _

/-- `∫_s^∞ t^(q-3) dt = s^(q-2)/(2-q)`. -/
lemma lint_high {q : ℝ} (hq2 : q < 2) {s : ℝ} (hs : 0 < s) :
    ∫⁻ t in Ioi s, ENNReal.ofReal (t ^ (q - 3)) = ENNReal.ofReal (s ^ (q - 2) / (2 - q)) := by
  have hio : IntegrableOn (fun t : ℝ => t ^ (q - 3)) (Ioi s) :=
    integrableOn_Ioi_rpow_of_lt (by linarith) hs
  rw [← ofReal_integral_eq_lintegral_ofReal hio]
  · congr 1
    rw [integral_Ioi_rpow_of_lt (by linarith) hs, show q - 3 + 1 = q - 2 by ring]
    rw [div_eq_div_iff (by linarith) (by linarith)]; ring
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    exact Real.rpow_nonneg (hs.trans ht).le _

/-- The per-point one-dimensional computation. -/
lemma lint_point {q : ℝ} (hq1 : 1 < q) (hq2 : q < 2) {s : ℝ} (hs : 0 ≤ s) :
    ∫⁻ t in Ioi 0, (ENNReal.ofReal (2 / t) * (if t < s then ENNReal.ofReal s else 0) +
        ENNReal.ofReal (4 / t ^ 2) * (if t < s then 0 else ENNReal.ofReal (s ^ 2))) *
        ENNReal.ofReal (t ^ (q - 1)) ≤
      ENNReal.ofReal ((2 / (q - 1) + 4 / (2 - q)) * s ^ q) := by
  rcases hs.eq_or_lt with hs0 | hs0
  · subst hs0
    have : ∀ t ∈ Ioi (0 : ℝ), (ENNReal.ofReal (2 / t) * (if t < 0 then ENNReal.ofReal 0 else 0) +
        ENNReal.ofReal (4 / t ^ 2) * (if t < 0 then 0 else ENNReal.ofReal (0 ^ 2))) *
        ENNReal.ofReal (t ^ (q - 1)) = 0 := by
      intro t ht; simp
    rw [setLIntegral_congr_fun measurableSet_Ioi this]; simp
  have e1 : ∀ t ∈ Ioi (0 : ℝ), (ENNReal.ofReal (2 / t) * (if t < s then ENNReal.ofReal s else 0) +
        ENNReal.ofReal (4 / t ^ 2) * (if t < s then 0 else ENNReal.ofReal (s ^ 2))) *
        ENNReal.ofReal (t ^ (q - 1)) =
      (Iio s).indicator (fun t => ENNReal.ofReal (2 * s) * ENNReal.ofReal (t ^ (q - 2))) t +
      (Ici s).indicator (fun t => ENNReal.ofReal (4 * s ^ 2) * ENNReal.ofReal (t ^ (q - 3))) t := by
    intro t ht
    have ht : 0 < t := ht
    have r1 : t ^ (q - 1) = t ^ (q - 2) * t := by
      rw [← Real.rpow_add_one ht.ne']; ring_nf
    have r2 : t ^ (q - 1) = t ^ (q - 3) * t ^ 2 := by
      rw [← Real.rpow_natCast, ← Real.rpow_add ht]; ring_nf
    by_cases h : t < s
    · have h' : t ∉ Ici s := by simpa using h
      rw [if_pos h, if_pos h, indicator_of_mem (show t ∈ Iio s from h), indicator_of_notMem h',
        mul_zero, add_zero, add_zero, ← ENNReal.ofReal_mul (by positivity),
        ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity)]
      congr 1; rw [r1]; field_simp
    · have h' : t ∈ Ici s := by simpa using h
      rw [if_neg h, if_neg h, indicator_of_notMem (show t ∉ Iio s from h), indicator_of_mem h',
        mul_zero, zero_add, zero_add, ← ENNReal.ofReal_mul (by positivity),
        ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity)]
      congr 1; rw [r2]; field_simp
  rw [setLIntegral_congr_fun measurableSet_Ioi e1]
  rw [lintegral_add_left]
  swap
  · exact Measurable.indicator (by fun_prop) measurableSet_Iio
  rw [lintegral_indicator measurableSet_Iio, lintegral_indicator measurableSet_Ici,
    Measure.restrict_restrict measurableSet_Iio, Measure.restrict_restrict measurableSet_Ici,
    lintegral_const_mul _ (by fun_prop), lintegral_const_mul _ (by fun_prop)]
  have i1 : Iio s ∩ Ioi 0 = Ioo 0 s := by ext; simp [and_comm]
  have i2 : Ici s ∩ Ioi (0 : ℝ) = Ici s := inter_eq_left.2 (fun t ht => hs0.trans_le ht)
  rw [i1, i2, setLIntegral_congr Ioi_ae_eq_Ici.symm, lint_low hq1 hs, lint_high hq2 hs0,
    ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity),
    ← ENNReal.ofReal_add (by positivity) (by positivity)]
  apply le_of_eq; congr 1
  have a1 : s * s ^ (q - 1) = s ^ q := by
    rw [← Real.rpow_one_add' hs0.le (by linarith)]; ring_nf
  have a2 : s ^ 2 * s ^ (q - 2) = s ^ q := by
    rw [← Real.rpow_natCast, ← Real.rpow_add hs0]; ring_nf
  have hq1' : q - 1 ≠ 0 := by linarith
  have hq2' : 2 - q ≠ 0 := by linarith
  calc 2 * s * (s ^ (q - 1) / (q - 1)) + 4 * s ^ 2 * (s ^ (q - 2) / (2 - q))
      = 2 * (s * s ^ (q - 1)) / (q - 1) + 4 * (s ^ 2 * s ^ (q - 2)) / (2 - q) := by ring
    _ = _ := by rw [a1, a2]; ring

section MarcSec

variable {ι : Type*} [Fintype ι] {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (μ : Measure X) (ν : Measure Y) [SFinite μ] [SFinite ν] (P : (ι → X → ℂ) → Prop)
    (T : (ι → X → ℂ) → Y → ℂ) (A : ℝ≥0∞)

omit [SFinite μ] [SFinite ν] in
include P in
lemma marc_step
    (hPhi : ∀ G t, P G → P (truncHi G t)) (hPlo : ∀ G t, P G → P (truncLo G t))
    (hlin : ∀ G G', P G → P G' → T (G + G') = T G + T G')
    (hmeasT : ∀ G, P G → Measurable (T G))
    (h1 : ∀ G, P G → ∫⁻ y, ‖T G y‖ₑ ∂ν ≤ A * ∑ i, ∫⁻ x, ‖G i x‖ₑ ∂μ)
    (h2 : ∀ G, P G → ∫⁻ y, ‖T G y‖ₑ ^ (2 : ℝ) ∂ν ≤ A * ∑ i, ∫⁻ x, ‖G i x‖ₑ ^ (2 : ℝ) ∂μ)
    (G : ι → X → ℂ) (hG : P G) (t : ℝ) (ht : 0 < t) :
    ν {y | t < ‖T G y‖} ≤
      A * (ENNReal.ofReal (2 / t) * (∑ i, ∫⁻ x, ‖truncHi G t i x‖ₑ ∂μ) +
        ENNReal.ofReal (4 / t ^ 2) * (∑ i, ∫⁻ x, ‖truncLo G t i x‖ₑ ^ (2 : ℝ) ∂μ)) := by
  have hsplit : T G = T (truncHi G t) + T (truncLo G t) := by
    rw [← hlin _ _ (hPhi G t hG) (hPlo G t hG), truncHi_add_truncLo]
  have hsub : {y | t < ‖T G y‖} ⊆ {y | t / 2 ≤ ‖T (truncHi G t) y‖} ∪
      {y | t / 2 ≤ ‖T (truncLo G t) y‖} := by
    intro y hy
    simp only [mem_setOf_eq, mem_union] at hy ⊢
    by_contra hc
    push Not at hc
    rw [hsplit, Pi.add_apply] at hy
    linarith [norm_add_le (T (truncHi G t) y) (T (truncLo G t) y)]
  have c1 : ν {y | t / 2 ≤ ‖T (truncHi G t) y‖} ≤ ENNReal.ofReal (2 / t) * (A * (∑ i, ∫⁻ x, ‖truncHi G t i x‖ₑ ∂μ)) := by
    have hm := (hmeasT _ (hPhi G t hG)).enorm.aemeasurable (μ := ν)
    have := mul_meas_ge_le_lintegral₀ hm (ENNReal.ofReal (t / 2))
    have hset : {y | ENNReal.ofReal (t / 2) ≤ ‖T (truncHi G t) y‖ₑ} =
        {y | t / 2 ≤ ‖T (truncHi G t) y‖} := by
      ext y; simp only [mem_setOf_eq, ← ofReal_norm]
      exact ENNReal.ofReal_le_ofReal_iff (norm_nonneg _)
    rw [hset] at this
    have hpos : ENNReal.ofReal (t / 2) ≠ 0 := by simpa using ht
    have e2 : ENNReal.ofReal (2 / t) = (ENNReal.ofReal (t / 2))⁻¹ := by
      rw [← ENNReal.ofReal_inv_of_pos (by positivity)]; congr 1; field_simp
    rw [e2, ← ENNReal.div_eq_inv_mul, ENNReal.le_div_iff_mul_le (Or.inl hpos)
      (Or.inl ENNReal.ofReal_ne_top), mul_comm]
    exact this.trans (h1 _ (hPhi G t hG))
  have c2 : ν {y | t / 2 ≤ ‖T (truncLo G t) y‖} ≤ ENNReal.ofReal (4 / t ^ 2) * (A * (∑ i, ∫⁻ x, ‖truncLo G t i x‖ₑ ^ (2 : ℝ) ∂μ)) := by
    have hm := ((hmeasT _ (hPlo G t hG)).enorm.pow_const (2 : ℝ)).aemeasurable (μ := ν)
    have := mul_meas_ge_le_lintegral₀ hm (ENNReal.ofReal ((t / 2) ^ 2))
    have hset : {y | ENNReal.ofReal ((t / 2) ^ 2) ≤ ‖T (truncLo G t) y‖ₑ ^ (2 : ℝ)} =
        {y | t / 2 ≤ ‖T (truncLo G t) y‖} := by
      ext y; simp only [mem_setOf_eq, ← ofReal_norm]
      rw [ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) (by norm_num),
        ENNReal.ofReal_le_ofReal_iff (by positivity), Real.rpow_two]
      exact pow_le_pow_iff_left₀ (by positivity) (norm_nonneg _) two_ne_zero
    rw [hset] at this
    have hpos : ENNReal.ofReal ((t / 2) ^ 2) ≠ 0 := by simpa using ht.ne'
    have e2 : ENNReal.ofReal (4 / t ^ 2) = (ENNReal.ofReal ((t / 2) ^ 2))⁻¹ := by
      rw [← ENNReal.ofReal_inv_of_pos (by positivity)]; congr 1; field_simp; ring
    rw [e2, ← ENNReal.div_eq_inv_mul, ENNReal.le_div_iff_mul_le (Or.inl hpos)
      (Or.inl ENNReal.ofReal_ne_top), mul_comm]
    exact this.trans (h2 _ (hPlo G t hG))
  calc ν {y | t < ‖T G y‖} ≤ _ := measure_mono hsub
    _ ≤ _ := measure_union_le _ _
    _ ≤ _ := add_le_add c1 c2
    _ = _ := by ring

/-- The integrand after the layer-cake step. -/
noncomputable def marcF (G : ι → X → ℂ) (q : ℝ) (i : ι) (t : ℝ) (x : X) : ℝ≥0∞ :=
  (ENNReal.ofReal (2 / t) * (if t < ‖G i x‖ then ENNReal.ofReal ‖G i x‖ else 0) +
    ENNReal.ofReal (4 / t ^ 2) * (if t < ‖G i x‖ then 0 else ENNReal.ofReal (‖G i x‖ ^ 2))) *
    ENNReal.ofReal (t ^ (q - 1))

omit [Fintype ι] in
lemma marcF_meas (G : ι → X → ℂ) (hG : ∀ i, Measurable (G i)) (q : ℝ) (i : ι) :
    Measurable (Function.uncurry (marcF G q i)) := by
  have hg : Measurable (fun p : ℝ × X => ‖G i p.2‖) := (hG i).norm.comp measurable_snd
  have hs : MeasurableSet {p : ℝ × X | p.1 < ‖G i p.2‖} := measurableSet_lt measurable_fst hg
  refine Measurable.mul (Measurable.add ?_ ?_) ?_
  · exact (by fun_prop : Measurable fun p : ℝ × X => ENNReal.ofReal (2 / p.1)).mul
      (Measurable.ite hs hg.ennreal_ofReal measurable_const)
  · exact (by fun_prop : Measurable fun p : ℝ × X => ENNReal.ofReal (4 / p.1 ^ 2)).mul
      (Measurable.ite hs measurable_const (hg.pow_const 2).ennreal_ofReal)
  · exact (measurable_fst.pow_const _).ennreal_ofReal

omit [SFinite μ] in
lemma marcF_sum (G : ι → X → ℂ) (hG : ∀ i, Measurable (G i)) (q t : ℝ) :
    ∑ i, ∫⁻ x, marcF G q i t x ∂μ =
      (ENNReal.ofReal (2 / t) * (∑ i, ∫⁻ x, ‖truncHi G t i x‖ₑ ∂μ) +
        ENNReal.ofReal (4 / t ^ 2) * (∑ i, ∫⁻ x, ‖truncLo G t i x‖ₑ ^ (2 : ℝ) ∂μ)) *
        ENNReal.ofReal (t ^ (q - 1)) := by
  simp only [enorm_truncHi, enorm_truncLo_sq, Finset.mul_sum, Finset.sum_mul,
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  have hs : MeasurableSet {x | t < ‖G i x‖} := measurableSet_lt measurable_const (hG i).norm
  have m1 : Measurable (fun x => if t < ‖G i x‖ then ENNReal.ofReal ‖G i x‖ else 0) :=
    Measurable.ite hs (hG i).norm.ennreal_ofReal measurable_const
  have m2 : Measurable (fun x => if t < ‖G i x‖ then 0 else ENNReal.ofReal (‖G i x‖ ^ 2)) :=
    Measurable.ite hs measurable_const ((hG i).norm.pow_const 2).ennreal_ofReal
  unfold marcF
  rw [lintegral_mul_const' _ _ ENNReal.ofReal_ne_top]
  congr 1
  rw [lintegral_add_left (m1.const_mul _), lintegral_const_mul _ m1,
    lintegral_const_mul _ m2]

omit [Fintype ι] [MeasurableSpace X] in
lemma marcF_point {q : ℝ} (hq1 : 1 < q) (hq2 : q < 2) (G : ι → X → ℂ) (i : ι) (x : X) :
    ∫⁻ t in Ioi 0, marcF G q i t x ≤
      ENNReal.ofReal (2 / (q - 1) + 4 / (2 - q)) * ‖G i x‖ₑ ^ q := by
  refine (lint_point hq1 hq2 (norm_nonneg (G i x))).trans (le_of_eq ?_)
  have : 0 < q - 1 := by linarith
  have : 0 < 2 - q := by linarith
  rw [ENNReal.ofReal_mul (by positivity), ← ofReal_norm,
    ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) (by linarith)]

include P in
/-- The interpolation step. -/
lemma marc
    (hPhi : ∀ G t, P G → P (truncHi G t)) (hPlo : ∀ G t, P G → P (truncLo G t))
    (hlin : ∀ G G', P G → P G' → T (G + G') = T G + T G')
    (hmeasT : ∀ G, P G → Measurable (T G))
    (hmeasG : ∀ G, P G → ∀ i, Measurable (G i))
    (h1 : ∀ G, P G → ∫⁻ y, ‖T G y‖ₑ ∂ν ≤ A * ∑ i, ∫⁻ x, ‖G i x‖ₑ ∂μ)
    (h2 : ∀ G, P G → ∫⁻ y, ‖T G y‖ₑ ^ (2 : ℝ) ∂ν ≤ A * ∑ i, ∫⁻ x, ‖G i x‖ₑ ^ (2 : ℝ) ∂μ)
    {q : ℝ} (hq1 : 1 < q) (hq2 : q < 2) (G : ι → X → ℂ) (hG : P G) :
    ∫⁻ y, ‖T G y‖ₑ ^ q ∂ν ≤
      ENNReal.ofReal (q * (2 / (q - 1) + 4 / (2 - q))) * A * ∑ i, ∫⁻ x, ‖G i x‖ₑ ^ q ∂μ := by
  have hq0 : 0 < q := by linarith
  have hlc := lintegral_rpow_eq_lintegral_meas_lt_mul ν (f := fun y => ‖T G y‖)
    (Eventually.of_forall (fun y => norm_nonneg _)) (hmeasT G hG).norm.aemeasurable hq0
  have e0 : ∫⁻ y, ‖T G y‖ₑ ^ q ∂ν = ∫⁻ y, ENNReal.ofReal (‖T G y‖ ^ q) ∂ν := by
    congr 1; ext y
    rw [← ofReal_norm, ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) hq0.le]
  rw [e0, hlc]
  have hFm := marcF_meas G (hmeasG G hG) q
  have key : ∀ t ∈ Ioi (0 : ℝ), ν {y | t < ‖T G y‖} * ENNReal.ofReal (t ^ (q - 1)) ≤
      A * ∑ i, ∫⁻ x, marcF G q i t x ∂μ := by
    intro t ht
    rw [marcF_sum μ G (hmeasG G hG), ← mul_assoc]
    gcongr
    exact marc_step μ ν P T A hPhi hPlo hlin hmeasT h1 h2 G hG t ht
  calc ENNReal.ofReal q * ∫⁻ t in Ioi 0, ν {y | t < ‖T G y‖} * ENNReal.ofReal (t ^ (q - 1))
      ≤ ENNReal.ofReal q * ∫⁻ t in Ioi 0, A * ∑ i, ∫⁻ x, marcF G q i t x ∂μ := by
        gcongr 1
        exact setLIntegral_mono' measurableSet_Ioi key
    _ = ENNReal.ofReal q * (A * ∑ i, ∫⁻ x, (∫⁻ t in Ioi 0, marcF G q i t x) ∂μ) := by
        congr 1
        have hmi : ∀ i ∈ (Finset.univ : Finset ι),
            Measurable (fun t => ∫⁻ x, marcF G q i t x ∂μ) :=
          fun i _ => (hFm i).lintegral_prod_right'
        have hm : Measurable (fun t => ∑ i, ∫⁻ x, marcF G q i t x ∂μ) :=
          Finset.measurable_sum _ hmi
        rw [lintegral_const_mul _ hm]
        congr 1
        rw [lintegral_finset_sum _ hmi]
        refine Finset.sum_congr rfl (fun i _ => ?_)
        exact lintegral_lintegral_swap (hFm i).aemeasurable
    _ ≤ ENNReal.ofReal q * (A * ∑ i, ∫⁻ x,
          ENNReal.ofReal (2 / (q - 1) + 4 / (2 - q)) * ‖G i x‖ₑ ^ q ∂μ) := by
        gcongr with i _ x
        exact marcF_point hq1 hq2 G i x
    _ = _ := by
        simp_rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
        rw [← Finset.mul_sum, ENNReal.ofReal_mul hq0.le]
        ring

end MarcSec

end TaoBR.RSU

end
end

section
section
/-!
# Lemma 3.2 of Tao 1999: basic objects (bump, polar coordinates, caps)
-/

open MeasureTheory Metric Set Filter Topology
open scoped FourierTransform ENNReal NNReal SchwartzMap RealInnerProductSpace ComplexConjugate
  Pointwise

namespace TaoBR.RSU

instance sphere_finite (n : ℕ) : IsFiniteMeasure (sphereMeasure n) := by
  unfold sphereMeasure; infer_instance

lemma nontrivial_E {n : ℕ} (hn : 1 ≤ n) : Nontrivial (E n) := by
  have : 0 < Module.finrank ℝ (E n) := by rw [finrank_euclideanSpace_fin]; omega
  exact Module.nontrivial_of_finrank_pos this

/-! ## Polar coordinates -/

lemma polar_prod_lintegral {n : ℕ} (hn : 1 ≤ n) (F : E n → ℝ≥0∞) (hF : Measurable F) :
    ∫⁻ x, F x = ∫⁻ p : sphere (0 : E n) 1 × Ioi (0 : ℝ), F ((p.2 : ℝ) • (p.1 : E n))
      ∂((sphereMeasure n).prod (Measure.volumeIoiPow (n - 1))) := by
  have := nontrivial_E hn
  have h1 : ∫⁻ x, F x = ∫⁻ x : ({(0 : E n)}ᶜ : Set (E n)), F x
      ∂((volume : Measure (E n)).comap Subtype.val) := by
    rw [lintegral_subtype_comap (measurableSet_singleton _).compl, restrict_compl_singleton]
  have h2 := MeasurePreserving.symm (homeomorphUnitSphereProd (E n)).toMeasurableEquiv
    ((volume : Measure (E n)).measurePreserving_homeomorphUnitSphereProd)
  rw [h1, ← h2.lintegral_comp_emb (MeasurableEquiv.measurableEmbedding _)]
  simp only [finrank_euclideanSpace_fin]
  rfl

lemma polar_lintegral {n : ℕ} (hn : 1 ≤ n) (F : E n → ℝ≥0∞) (hF : Measurable F) :
    ∫⁻ x, F x = ∫⁻ ω, (∫⁻ r in Ioi (0 : ℝ), ENNReal.ofReal (r ^ (n - 1)) * F (r • (ω : E n)))
      ∂(sphereMeasure n) := by
  rw [polar_prod_lintegral hn F hF, lintegral_prod]
  · congr 1; ext ω
    rw [Measure.volumeIoiPow, lintegral_withDensity_eq_lintegral_mul]
    · exact lintegral_subtype_comap (μ := volume) measurableSet_Ioi
        (fun r : ℝ => ENNReal.ofReal (r ^ (n - 1)) * F (r • (ω : E n)))
    · exact (measurable_subtype_coe.pow_const _).ennreal_ofReal
    · exact hF.comp (by fun_prop)
  · exact (hF.comp ((measurable_subtype_coe.comp measurable_snd).smul
      (measurable_subtype_coe.comp measurable_fst))).aemeasurable

lemma polar_prod_integral {n : ℕ} (hn : 1 ≤ n) (a : sphere (0 : E n) 1 → ℂ) (b : ℝ → ℂ)
    (F : E n → ℂ) (hF : ∀ ω : sphere (0 : E n) 1, ∀ r : ℝ, 0 < r → F (r • (ω : E n)) = a ω * b r) :
    ∫ x, F x = (∫ ω, a ω ∂(sphereMeasure n)) *
      ∫ r : Ioi (0 : ℝ), b r ∂(Measure.volumeIoiPow (n - 1)) := by
  have := nontrivial_E hn
  have h1 : ∫ x, F x = ∫ x : ({(0 : E n)}ᶜ : Set (E n)), F x
      ∂((volume : Measure (E n)).comap Subtype.val) := by
    rw [integral_subtype_comap (measurableSet_singleton _).compl, restrict_compl_singleton]
  have h2 := MeasurePreserving.symm (homeomorphUnitSphereProd (E n)).toMeasurableEquiv
    ((volume : Measure (E n)).measurePreserving_homeomorphUnitSphereProd)
  rw [h1, ← h2.integral_comp (MeasurableEquiv.measurableEmbedding _)]
  simp only [finrank_euclideanSpace_fin]
  rw [← integral_prod_mul]
  congr 1; ext p
  exact hF p.1 p.2 p.2.2

/-! ## Caps -/

lemma cap_le {n : ℕ} (hn : 1 ≤ n) (η : E n) {r : ℝ} (hr : 0 < r) :
    sphereMeasure n {ω | dist (ω : E n) η < r} ≤
      ENNReal.ofReal (2 ^ n * r ^ (n - 1)) * volume (ball (0 : E n) 1) := by
  have := nontrivial_E hn
  set cap := {ω : sphere (0 : E n) 1 | dist (ω : E n) η < r}
  have hcap : MeasurableSet cap :=
    measurableSet_lt (continuous_subtype_val.dist continuous_const).measurable measurable_const
  have hF : Measurable ((ball η (2 * r)).indicator (fun _ : E n => (1 : ℝ≥0∞))) :=
    measurable_const.indicator measurableSet_ball
  have key := polar_lintegral hn _ hF
  rw [lintegral_indicator_const measurableSet_ball, one_mul] at key
  have low : ∀ ω : sphere (0 : E n) 1,
      cap.indicator (fun _ => ENNReal.ofReal r) ω ≤
        ∫⁻ t in Ioi (0 : ℝ), ENNReal.ofReal (t ^ (n - 1)) *
          (ball η (2 * r)).indicator (fun _ : E n => (1 : ℝ≥0∞)) (t • (ω : E n)) := by
    intro ω
    by_cases hω : ω ∈ cap
    · rw [indicator_of_mem hω]
      have hsub : Ioo (1 : ℝ) (1 + r) ⊆ Ioi 0 := fun t ht => lt_trans one_pos ht.1
      calc ENNReal.ofReal r = ∫⁻ t in Ioo (1 : ℝ) (1 + r), 1 := by
            rw [setLIntegral_const, one_mul, Real.volume_Ioo]; ring_nf
        _ ≤ ∫⁻ t in Ioo (1 : ℝ) (1 + r), ENNReal.ofReal (t ^ (n - 1)) *
              (ball η (2 * r)).indicator (fun _ : E n => (1 : ℝ≥0∞)) (t • (ω : E n)) := by
            refine setLIntegral_mono' measurableSet_Ioo (fun t ht => ?_)
            have hω1 : ‖(ω : E n)‖ = 1 := by simp
            have hmem : t • (ω : E n) ∈ ball η (2 * r) := by
              rw [mem_ball]
              have hd : dist (ω : E n) η < r := hω
              calc dist (t • (ω : E n)) η ≤ dist (t • (ω : E n)) (ω : E n) + dist (ω : E n) η :=
                    dist_triangle _ _ _
                _ < r + r := by
                    gcongr
                    have e : t • (ω : E n) - (ω : E n) = (t - 1) • (ω : E n) := by
                      rw [sub_smul, one_smul]
                    rw [dist_eq_norm, e, norm_smul,
                      hω1, mul_one, Real.norm_eq_abs, abs_of_pos (by linarith [ht.1])]
                    linarith [ht.2]
                _ = 2 * r := by ring
            rw [indicator_of_mem hmem, mul_one]
            rw [← ENNReal.ofReal_one]
            exact ENNReal.ofReal_le_ofReal (one_le_pow₀ ht.1.le)
        _ ≤ _ := lintegral_mono_set hsub
    · rw [indicator_of_notMem hω]; exact bot_le
  have h2 : sphereMeasure n cap * ENNReal.ofReal r ≤ volume (ball η (2 * r)) := by
    rw [key, mul_comm, ← lintegral_indicator_const hcap]
    exact lintegral_mono low
  rw [Measure.addHaar_ball _ _ (by positivity), finrank_euclideanSpace_fin] at h2
  have hr' : ENNReal.ofReal r ≠ 0 := by simpa using hr
  calc sphereMeasure n cap = sphereMeasure n cap * ENNReal.ofReal r / ENNReal.ofReal r := by
        rw [ENNReal.mul_div_cancel_right hr' ENNReal.ofReal_ne_top]
    _ ≤ ENNReal.ofReal ((2 * r) ^ n) * volume (ball (0 : E n) 1) / ENNReal.ofReal r :=
        ENNReal.div_le_div_right h2 _
    _ = ENNReal.ofReal (2 ^ n * r ^ (n - 1)) * volume (ball (0 : E n) 1) := by
        rw [ENNReal.div_eq_inv_mul, ← mul_assoc,
          ← ENNReal.ofReal_inv_of_pos hr, ← ENNReal.ofReal_mul (by positivity)]
        congr 2
        have : r ^ n = r * r ^ (n - 1) := by rw [← pow_succ']; congr 1; omega
        rw [mul_pow, this]; field_simp

/-! ## The bump `Φ` and `φ = 𝓕⁻ Φ` -/

/-- The bump with `rIn = 1/32`, `rOut = 1/16`. -/
noncomputable def bump (n : ℕ) : ContDiffBump (0 : E n) := ⟨1 / 32, 1 / 16, by norm_num, by norm_num⟩

/-- `Φ`, normalized: `Φ ≥ 0`, `∫ Φ = 1`, supported in `ball 0 (1/16)`. -/
noncomputable def Phi (n : ℕ) (v : E n) : ℝ := (bump n).normed volume v

noncomputable def PhiC (n : ℕ) (v : E n) : ℂ := (Phi n v : ℂ)

noncomputable def MPhi (n : ℕ) : ℝ := 1 / (volume : Measure (E n)).real (closedBall 0 (1 / 32))

lemma Phi_nonneg (n : ℕ) (v : E n) : 0 ≤ Phi n v := (bump n).nonneg_normed v

lemma Phi_le (n : ℕ) (v : E n) : Phi n v ≤ MPhi n :=
  (bump n).normed_le_div_measure_closedBall_rIn volume v

lemma MPhi_nonneg (n : ℕ) : 0 ≤ MPhi n := (Phi_nonneg n 0).trans (Phi_le n 0)

lemma Phi_support (n : ℕ) {v : E n} (h : Phi n v ≠ 0) : ‖v‖ < 1 / 16 := by
  have : v ∈ Function.support ((bump n).normed volume) := h
  rw [(bump n).support_normed_eq, mem_ball_zero_iff] at this
  exact this

lemma Phi_integral (n : ℕ) : ∫ v, Phi n v = 1 := (bump n).integral_normed

lemma PhiC_contDiff (n : ℕ) : ContDiff ℝ (⊤ : ℕ∞) (PhiC n) :=
  Complex.ofRealCLM.contDiff.comp (bump n).contDiff_normed

lemma PhiC_hasCompactSupport (n : ℕ) : HasCompactSupport (PhiC n) :=
  (bump n).hasCompactSupport_normed.comp_left Complex.ofReal_zero

noncomputable def PhiS (n : ℕ) : 𝓢(E n, ℂ) :=
  (PhiC_hasCompactSupport n).toSchwartzMap (PhiC_contDiff n)

/-- `φ = 𝓕⁻ Φ` as a Schwartz map. -/
noncomputable def phiS (n : ℕ) : 𝓢(E n, ℂ) := 𝓕⁻ (PhiS n)

noncomputable def phi (n : ℕ) : E n → ℂ := phiS n

lemma phi_eq (n : ℕ) (y : E n) : phi n y = ∫ v, (𝐞 ⟪v, y⟫ : ℂ) * PhiC n v := by
  rw [phi, phiS, SchwartzMap.fourierInv_coe, Real.fourierInv_eq]
  rfl

lemma phi_integrable (n : ℕ) : Integrable (phi n) := (phiS n).integrable

lemma phi_moment_integrable (n : ℕ) : Integrable (fun u : E n => ‖u‖ * ‖phi n u‖) := by
  simpa [phi] using (phiS n).integrable_pow_mul volume 1

lemma phi_contDiff (n : ℕ) : ContDiff ℝ (⊤ : ℕ∞) (phi n) := (phiS n).smooth ⊤

lemma Phi_integrable (n : ℕ) : Integrable (Phi n) := (bump n).integrable_normed

lemma e_re (t : ℝ) : ((𝐞 t : ℂ)).re = Real.cos (2 * Real.pi * t) := by
  rw [Real.fourierChar_apply, Complex.exp_ofReal_mul_I_re]

lemma phi_lower (n : ℕ) {y : E n} (hy : ‖y‖ < 2) : 1 / 2 ≤ ‖phi n y‖ := by
  have hint : Integrable (fun v : E n => (𝐞 ⟪v, y⟫ : ℂ) * PhiC n v) := by
    refine ((Phi_integrable n).ofReal (𝕜 := ℂ)).bdd_mul (c := 1) ?_ ?_
    · exact (Real.continuous_fourierChar.comp (continuous_id.inner continuous_const)).subtype_val
        |>.aestronglyMeasurable
    · exact Eventually.of_forall (fun v => (Circle.norm_coe _).le)
  have hre : (phi n y).re = ∫ v, Real.cos (2 * Real.pi * ⟪v, y⟫) * Phi n v := by
    have := integral_re hint
    simp only [RCLike.re_to_complex] at this
    rw [phi_eq, ← this]
    congr 1; ext v
    simp only [PhiC, RCLike.re_to_complex, Complex.re_mul_ofReal, e_re]
  have hlow : ∫ v, (1 / 2 : ℝ) * Phi n v ≤ ∫ v, Real.cos (2 * Real.pi * ⟪v, y⟫) * Phi n v := by
    refine integral_mono ((Phi_integrable n).const_mul _) ?_ (fun v => ?_)
    · refine (Phi_integrable n).bdd_mul (c := 1) ?_ ?_
      · exact (Real.continuous_cos.comp (continuous_const.mul
          (continuous_id.inner continuous_const))).aestronglyMeasurable
      · exact Eventually.of_forall (fun v => by simpa using Real.abs_cos_le_one _)
    · by_cases h0 : Phi n v = 0
      · simp [h0]
      · have hv := Phi_support n h0
        refine mul_le_mul_of_nonneg_right ?_ (Phi_nonneg n v)
        have h1 : |⟪v, y⟫| ≤ 1 / 8 := by
          refine (abs_real_inner_le_norm v y).trans ?_
          nlinarith [norm_nonneg v, norm_nonneg y]
        have h2 := Real.one_sub_sq_div_two_le_cos (x := 2 * Real.pi * ⟪v, y⟫)
        have h3 : (2 * Real.pi * ⟪v, y⟫) ^ 2 ≤ 1 := by
          rw [mul_pow]
          have : ⟪v, y⟫ ^ 2 ≤ (1 / 8) ^ 2 := by
            rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) h1 2
          have hpi : (2 * Real.pi) ^ 2 ≤ 64 := by nlinarith [Real.pi_lt_four, Real.pi_pos]
          nlinarith [sq_nonneg (2 * Real.pi)]
        linarith
  rw [integral_const_mul, Phi_integral, mul_one] at hlow
  calc (1 / 2 : ℝ) ≤ (phi n y).re := by rw [hre]; exact hlow
    _ ≤ ‖phi n y‖ := Complex.re_le_norm _

end TaoBR.RSU

end
end

section
section
/-!
# The kernels `K_i` and the localizers `φ_i`
-/

open MeasureTheory Metric Set Filter Topology
open scoped FourierTransform ENNReal NNReal SchwartzMap RealInnerProductSpace ComplexConjugate
  Pointwise

namespace TaoBR.RSU

/-- `K(v) = R^n Φ(R v) e(-⟨v, c⟩)`. -/
noncomputable def K (n : ℕ) (R : ℝ) (c : E n) (v : E n) : ℂ :=
  ((R ^ n : ℝ) : ℂ) * PhiC n (R • v) * (𝐞 (-⟪v, c⟫) : ℂ)

/-- `φ_c(x) = φ((x - c)/R)`. -/
noncomputable def phiLoc (n : ℕ) (R : ℝ) (c : E n) (x : E n) : ℂ := phi n (R⁻¹ • (x - c))

variable {n : ℕ} {R : ℝ} {c : E n}

lemma K_support (hR : 0 < R) {v : E n} (h : K n R c v ≠ 0) : ‖v‖ < 1 / (16 * R) := by
  have h1 : PhiC n (R • v) ≠ 0 := by
    intro h0; apply h; simp only [K, h0, mul_zero, zero_mul]
  have h2 : Phi n (R • v) ≠ 0 := by simpa [PhiC] using h1
  have h3 := Phi_support n h2
  rw [norm_smul, Real.norm_of_nonneg hR.le] at h3
  rw [lt_div_iff₀ (by positivity)]; linarith

lemma K_norm_le (hR : 0 < R) (v : E n) : ‖K n R c v‖ ≤ R ^ n * MPhi n := by
  simp only [K, PhiC, norm_mul, Complex.norm_real, Circle.norm_coe, mul_one]
  rw [Real.norm_of_nonneg (by positivity), Real.norm_of_nonneg (Phi_nonneg n _)]
  exact mul_le_mul_of_nonneg_left (Phi_le n _) (by positivity)

lemma K_continuous : Continuous (K n R c) := by
  have h1 : Continuous (PhiC n) := (PhiC_contDiff n).continuous
  have h2 : Continuous (fun v : E n => (𝐞 (-⟪v, c⟫) : ℂ)) :=
    (Real.continuous_fourierChar.comp (continuous_id.inner continuous_const).neg).subtype_val
  have h3 : Continuous (fun v : E n => PhiC n (R • v)) := h1.comp (continuous_const_smul R)
  exact (continuous_const.mul h3).mul h2

lemma K_integrable (hR : 0 < R) : Integrable (K n R c) := by
  refine K_continuous.integrable_of_hasCompactSupport ?_
  refine HasCompactSupport.intro (isCompact_closedBall (0 : E n) (1 / (16 * R))) (fun v hv => ?_)
  by_contra h
  exact hv (mem_closedBall_zero_iff.2 (K_support hR h).le)

lemma fourierInv_K (hR : 0 < R) : 𝓕⁻ (K n R c) = phiLoc n R c := by
  funext y
  rw [Real.fourierInv_eq, phiLoc, phi_eq]
  have hcv := MeasureTheory.Measure.integral_comp_smul (volume : Measure (E n))
    (fun u : E n => (𝐞 ⟪u, R⁻¹ • (y - c)⟫ : ℂ) * PhiC n u) R
  rw [finrank_euclideanSpace_fin] at hcv
  have e1 : ∀ v : E n, 𝐞 ⟪v, y⟫ • K n R c v =
      ((R ^ n : ℝ) : ℂ) * ((𝐞 ⟪R • v, R⁻¹ • (y - c)⟫ : ℂ) * PhiC n (R • v)) := by
    intro v
    rw [Circle.smul_def, K, smul_eq_mul]
    have : ⟪R • v, R⁻¹ • (y - c)⟫ = ⟪v, y⟫ + -⟪v, c⟫ := by
      rw [real_inner_smul_left, real_inner_smul_right, ← mul_assoc, mul_inv_cancel₀ hR.ne',
        one_mul, inner_sub_right]; ring
    rw [this, AddChar.map_add_eq_mul, Circle.coe_mul]; ring
  simp_rw [e1]
  rw [integral_const_mul, hcv, Complex.real_smul, abs_of_pos (by positivity)]
  rw [← mul_assoc, ← Complex.ofReal_mul, mul_inv_cancel₀ (by positivity),
    Complex.ofReal_one, one_mul]

lemma phiLoc_integrable (hR : 0 < R) : Integrable (phiLoc n R c) := by
  have h1 : Integrable (fun y : E n => phi n (R⁻¹ • y)) :=
    (phi_integrable n).comp_smul (inv_ne_zero hR.ne')
  have h2 := h1.comp_sub_right c
  exact h2

lemma fourier_phiLoc (hR : 0 < R) : 𝓕 (phiLoc n R c) = K n R c := by
  have hF : 𝓕 (K n R c) = fun w => phiLoc n R c (-w) := by
    funext w
    rw [← fourierInv_K hR, Real.fourierInv_eq_fourier_neg, neg_neg]
  have hFi : Integrable (𝓕 (K n R c)) := by
    rw [hF]
    have := (phiLoc_integrable (c := c) hR).comp_smul (show (-1 : ℝ) ≠ 0 by norm_num)
    simpa using this
  rw [← fourierInv_K hR]
  exact K_continuous.fourier_fourierInv_eq (K_integrable hR) hFi

lemma fourier_mul_phiLoc (hR : 0 < R) (g : E n → ℂ) (hg : Integrable g) (ω : E n) :
    𝓕 (fun y => g y * phiLoc n R c y) ω = ∫ η, K n R c (ω - η) * 𝓕 g η := by
  have hK := K_integrable (c := c) hR
  have hphi : ∀ y, phiLoc n R c y = ∫ v, (𝐞 ⟪v, y⟫ : ℂ) * K n R c v := by
    intro y; rw [← fourierInv_K hR, Real.fourierInv_eq]; rfl
  rw [Real.fourier_eq]
  have e1 : ∀ y, 𝐞 (-⟪y, ω⟫) • (g y * phiLoc n R c y) =
      ∫ v, K n R c v * ((𝐞 (-⟪y, ω - v⟫) : ℂ) * g y) := by
    intro y
    rw [hphi, Circle.smul_def, smul_eq_mul, ← integral_const_mul, ← integral_const_mul]
    congr 1; ext v
    have : -⟪y, ω - v⟫ = -⟪y, ω⟫ + ⟪v, y⟫ := by rw [inner_sub_right, real_inner_comm y v]; ring
    rw [this, AddChar.map_add_eq_mul, Circle.coe_mul]; ring
  simp_rw [e1]
  have hint : Integrable (Function.uncurry fun (y v : E n) =>
      K n R c v * ((𝐞 (-⟪y, ω - v⟫) : ℂ) * g y)) (volume.prod volume) := by
    have hp : Integrable (fun p : E n × E n => K n R c p.2 * g p.1) (volume.prod volume) := by
      have := hg.mul_prod hK
      refine this.congr (Eventually.of_forall (fun p => ?_))
      simp [mul_comm]
    refine hp.mono ?_ (Eventually.of_forall (fun p => ?_))
    · refine (K_continuous.comp continuous_snd).aestronglyMeasurable.mul ?_
      refine AEStronglyMeasurable.mul ?_ (hg.aestronglyMeasurable.comp_fst)
      exact (Real.continuous_fourierChar.comp ((continuous_fst.inner
        (continuous_const.sub continuous_snd)).neg)).subtype_val.aestronglyMeasurable
    · simp [Function.uncurry, norm_mul, Circle.norm_coe]
  rw [integral_integral_swap hint]
  have e2 : ∀ v, ∫ y, K n R c v * ((𝐞 (-⟪y, ω - v⟫) : ℂ) * g y) =
      K n R c v * 𝓕 g (ω - v) := by
    intro v; rw [integral_const_mul, Real.fourier_eq]; rfl
  simp_rw [e2]
  have := integral_sub_left_eq_self (fun v => K n R c v * 𝓕 g (ω - v)) (volume : Measure (E n)) ω
  rw [← this]
  simp only [sub_sub_cancel]

lemma phiLoc_lower (hR : 0 < R) {y : E n} (hy : dist y c < 2 * R) :
    1 / 2 ≤ ‖phiLoc n R c y‖ := by
  apply phi_lower
  rw [norm_smul, norm_inv, Real.norm_of_nonneg hR.le, ← dist_eq_norm, inv_mul_lt_iff₀ hR]
  linarith

lemma phiLoc_contDiff : ContDiff ℝ (⊤ : ℕ∞) (phiLoc n R c) := by
  exact (phi_contDiff n).comp (by fun_prop)

lemma phiLoc_L1 (hR : 0 < R) : ∫ x, ‖phiLoc n R c x‖ = R ^ n * ∫ u, ‖phi n u‖ := by
  have h1 := integral_sub_right_eq_self (fun y : E n => ‖phi n (R⁻¹ • y)‖) (μ := volume) c
  have h2 := MeasureTheory.Measure.integral_comp_inv_smul_of_nonneg (volume : Measure (E n))
    (fun y : E n => ‖phi n y‖) hR.le
  rw [finrank_euclideanSpace_fin] at h2
  simp only [phiLoc]
  rw [h1, h2, smul_eq_mul]

lemma phiLoc_moment_integrable (hR : 0 < R) :
    Integrable (fun x => ‖x - c‖ * ‖phiLoc n R c x‖) := by
  have h0 : Integrable (fun u : E n => R * (‖u‖ * ‖phi n u‖)) :=
    (phi_moment_integrable n).const_mul R
  have h1 : Integrable (fun y : E n => R * (‖R⁻¹ • y‖ * ‖phi n (R⁻¹ • y)‖)) :=
    h0.comp_smul (inv_ne_zero hR.ne')
  have h2 := h1.comp_sub_right c
  refine h2.congr (Eventually.of_forall (fun y => ?_))
  simp only [phiLoc, norm_smul, norm_inv, Real.norm_of_nonneg hR.le]
  field_simp

lemma phiLoc_moment (hR : 0 < R) :
    ∫ x, ‖x - c‖ * ‖phiLoc n R c x‖ = R ^ (n + 1) * ∫ u, ‖u‖ * ‖phi n u‖ := by
  have h1 := integral_sub_right_eq_self
    (fun y : E n => ‖y‖ * ‖phi n (R⁻¹ • y)‖) (μ := volume) c
  have h2 := MeasureTheory.Measure.integral_comp_inv_smul_of_nonneg (volume : Measure (E n))
    (fun u : E n => R * (‖u‖ * ‖phi n u‖)) hR.le
  rw [finrank_euclideanSpace_fin] at h2
  have e : ∀ y : E n, R * (‖R⁻¹ • y‖ * ‖phi n (R⁻¹ • y)‖) = ‖y‖ * ‖phi n (R⁻¹ • y)‖ := by
    intro y
    rw [norm_smul, norm_inv, Real.norm_of_nonneg hR.le]; field_simp
  simp_rw [e] at h2
  simp only [phiLoc]
  rw [h1, h2, smul_eq_mul, integral_const_mul]; ring

end TaoBR.RSU

end
end

section
section
/-!
# The Fourier transform of surface measure
-/

open MeasureTheory Metric Set Filter Topology
open scoped FourierTransform ENNReal NNReal SchwartzMap RealInnerProductSpace ComplexConjugate
  Pointwise

namespace TaoBR.RSU

/-- `σ̂(z) = ∫_S e(-⟨ω, z⟩) dσ(ω)`. -/
noncomputable def sig (n : ℕ) (z : E n) : ℂ :=
  ∫ ω, (𝐞 (-⟪(ω : E n), z⟫) : ℂ) ∂(sphereMeasure n)

lemma sig_norm_le (n : ℕ) (z : E n) : ‖sig n z‖ ≤ (sphereMeasure n).real univ := by
  have := norm_integral_le_of_norm_le_const (μ := sphereMeasure n)
    (f := fun ω : sphere (0 : E n) 1 => (𝐞 (-⟪(ω : E n), z⟫) : ℂ)) (C := 1)
    (Eventually.of_forall (fun ω => (Circle.norm_coe _).le))
  simpa [sig] using this

end TaoBR.RSU

end
end

section
section
/-!
# Auxiliary lemmas for the `L²` bound of the operator `T`
-/

open MeasureTheory Metric Set Filter Topology
open scoped FourierTransform ENNReal NNReal SchwartzMap RealInnerProductSpace ComplexConjugate
  Pointwise

namespace TaoBR.RSU

/-- Weighted Cauchy–Schwarz for lower integrals. -/
lemma lintegral_cs {α : Type*} [MeasurableSpace α] (μ : Measure α) {a b : α → ℝ≥0∞}
    (ha : AEMeasurable a μ) (hb : AEMeasurable b μ) :
    (∫⁻ t, a t * b t ∂μ) ^ 2 ≤ (∫⁻ t, a t ∂μ) * ∫⁻ t, a t * b t ^ 2 ∂μ := by
  have hf : AEMeasurable (fun t => a t ^ (1 / 2 : ℝ)) μ := ha.pow_const _
  have hg : AEMeasurable (fun t => a t ^ (1 / 2 : ℝ) * b t) μ := hf.mul hb
  have h := ENNReal.lintegral_mul_le_Lp_mul_Lq μ Real.HolderConjugate.two_two hf hg
  have e1 : ∀ t, a t ^ (1 / 2 : ℝ) * (a t ^ (1 / 2 : ℝ) * b t) = a t * b t := by
    intro t
    rw [← mul_assoc, ← ENNReal.rpow_add_of_nonneg _ _ (by norm_num) (by norm_num)]
    norm_num
  have e2 : ∀ t, (a t ^ (1 / 2 : ℝ)) ^ (2 : ℝ) = a t := by
    intro t; rw [← ENNReal.rpow_mul]; norm_num
  have e3 : ∀ t, (a t ^ (1 / 2 : ℝ) * b t) ^ (2 : ℝ) = a t * b t ^ 2 := by
    intro t; rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num), e2, ← ENNReal.rpow_natCast]
    norm_num
  simp only [Pi.mul_apply, e1, e2, e3] at h
  calc (∫⁻ t, a t * b t ∂μ) ^ 2
      ≤ ((∫⁻ t, a t ∂μ) ^ (1 / 2 : ℝ) * (∫⁻ t, a t * b t ^ 2 ∂μ) ^ (1 / 2 : ℝ)) ^ 2 := by
        gcongr
    _ = (∫⁻ t, a t ∂μ) * ∫⁻ t, a t * b t ^ 2 ∂μ := by
        rw [mul_pow, ← ENNReal.rpow_natCast, ← ENNReal.rpow_natCast, ← ENNReal.rpow_mul,
          ← ENNReal.rpow_mul]
        norm_num

variable {n : ℕ} {R : ℝ}

lemma K_lintegral (hR : 0 < R) (c : E n) : ∫⁻ v, ‖K n R c v‖ₑ = 1 := by
  rw [← ofReal_integral_norm_eq_lintegral_enorm (K_integrable hR)]
  have e : ∀ v : E n, ‖K n R c v‖ = R ^ n * Phi n (R • v) := by
    intro v
    simp only [K, PhiC, norm_mul, Complex.norm_real, Circle.norm_coe, mul_one]
    rw [Real.norm_of_nonneg (by positivity), Real.norm_of_nonneg (Phi_nonneg n _)]
  simp_rw [e]
  rw [integral_const_mul, Measure.integral_comp_smul, finrank_euclideanSpace_fin, Phi_integral,
    smul_eq_mul, mul_one, abs_of_pos (by positivity), mul_inv_cancel₀ (by positivity),
    ENNReal.ofReal_one]

/-- `F(ω) = ∫ K(ω - η) G(η) dη`. -/
noncomputable def Fop (n : ℕ) (R : ℝ) (c : E n) (G : E n → ℂ) (ω : E n) : ℂ :=
  ∫ η, K n R c (ω - η) * G η

/-- `g(y) = ∫ e(⟪y, η⟫) G(η) dη`. -/
noncomputable def gG (G : E n → ℂ) (y : E n) : ℂ := ∫ η, (𝐞 ⟪y, η⟫ : ℂ) * G η

lemma gG_enorm_le (G : E n → ℂ) (y : E n) : ‖gG G y‖ₑ ≤ ∫⁻ η, ‖G η‖ₑ := by
  refine (enorm_integral_le_lintegral_enorm _).trans (le_of_eq ?_)
  congr 1; ext η
  rw [enorm_mul, ← ofReal_norm (𝐞 ⟪y, η⟫ : ℂ), Circle.norm_coe, ENNReal.ofReal_one, one_mul]

lemma gG_norm_le (G : E n → ℂ) (y : E n) : ‖gG G y‖ ≤ ∫ η, ‖G η‖ := by
  refine (norm_integral_le_integral_norm _).trans (le_of_eq ?_)
  congr 1; ext η; rw [norm_mul, Circle.norm_coe, one_mul]

lemma gG_meas {G : E n → ℂ} (hG : StronglyMeasurable G) : StronglyMeasurable (gG G) := by
  refine StronglyMeasurable.integral_prod_right (f := fun (y η : E n) => (𝐞 ⟪y, η⟫ : ℂ) * G η) ?_
  refine StronglyMeasurable.mul ?_ (hG.comp_measurable measurable_snd)
  exact (Real.continuous_fourierChar.comp (continuous_fst.inner continuous_snd)).subtype_val
    |>.stronglyMeasurable

lemma sig_meas : StronglyMeasurable (sig n) := by
  refine StronglyMeasurable.integral_prod_left'
    (f := fun p : sphere (0 : E n) 1 × E n => (𝐞 (-⟪(p.1 : E n), p.2⟫) : ℂ)) ?_
  exact (Real.continuous_fourierChar.comp ((continuous_subtype_val.comp continuous_fst).inner
    continuous_snd).neg).subtype_val.stronglyMeasurable

lemma conj_e (t : ℝ) : conj (𝐞 t : ℂ) = (𝐞 (-t) : ℂ) := by
  rw [← Circle.coe_inv_eq_conj, AddChar.map_neg_eq_inv]

lemma Fop_repr (hR : 0 < R) (c : E n) {G : E n → ℂ} (hG : Integrable G) (ω : E n) :
    Fop n R c G ω = ∫ y, phiLoc n R c y * gG G y * (𝐞 (-⟪y, ω⟫) : ℂ) := by
  have hK : ∀ v, K n R c v = ∫ y, (𝐞 (-⟪y, v⟫) : ℂ) * phiLoc n R c y := by
    intro v; rw [← fourier_phiLoc hR, Real.fourier_eq]; rfl
  have e1 : ∀ η, K n R c (ω - η) * G η =
      ∫ y, phiLoc n R c y * ((𝐞 ⟪y, η⟫ : ℂ) * G η) * (𝐞 (-⟪y, ω⟫) : ℂ) := by
    intro η
    rw [hK, ← integral_mul_const]
    congr 1; ext y
    have : -⟪y, ω - η⟫ = ⟪y, η⟫ + -⟪y, ω⟫ := by rw [inner_sub_right]; ring
    rw [this, AddChar.map_add_eq_mul, Circle.coe_mul]; ring
  unfold Fop
  simp_rw [e1]
  have hint : Integrable (Function.uncurry fun (η y : E n) =>
      phiLoc n R c y * ((𝐞 ⟪y, η⟫ : ℂ) * G η) * (𝐞 (-⟪y, ω⟫) : ℂ)) (volume.prod volume) := by
    have hp : Integrable (fun p : E n × E n => G p.1 * phiLoc n R c p.2) (volume.prod volume) :=
      hG.mul_prod (phiLoc_integrable hR)
    refine hp.mono ?_ (Eventually.of_forall (fun p => ?_))
    · refine AEStronglyMeasurable.mul (AEStronglyMeasurable.mul ?_ (AEStronglyMeasurable.mul ?_
        hG.aestronglyMeasurable.comp_fst)) ?_
      · exact (phiLoc_contDiff.continuous.comp continuous_snd).aestronglyMeasurable
      · exact (Real.continuous_fourierChar.comp (continuous_snd.inner continuous_fst)).subtype_val
          |>.aestronglyMeasurable
      · exact (Real.continuous_fourierChar.comp (continuous_snd.inner
          continuous_const).neg).subtype_val.aestronglyMeasurable
    · simp [Function.uncurry, Circle.norm_coe, mul_comm]
  rw [integral_integral_swap hint]
  congr 1; ext y
  rw [integral_mul_const, integral_const_mul]; rfl

lemma Fop_offdiag (hR : 0 < R) (c c' : E n) {G G' : E n → ℂ} (hG : Integrable G)
    (hG' : Integrable G') (hGm : StronglyMeasurable G) (hGm' : StronglyMeasurable G') :
    ‖∫ ω, Fop n R c G (ω : E n) * conj (Fop n R c' G' (ω : E n)) ∂(sphereMeasure n)‖ₑ ≤
      (∫⁻ η, ‖G η‖ₑ) * (∫⁻ η, ‖G' η‖ₑ) *
        ∫⁻ y, ∫⁻ y', ‖phiLoc n R c y‖ₑ * ‖phiLoc n R c' y'‖ₑ * ‖sig n (y - y')‖ₑ := by
  set h : E n → ℂ := fun y => phiLoc n R c y * gG G y with hh_def
  set h' : E n → ℂ := fun y => phiLoc n R c' y * gG G' y with hh'_def
  have hhm : StronglyMeasurable h :=
    phiLoc_contDiff.continuous.stronglyMeasurable.mul (gG_meas hGm)
  have hhm' : StronglyMeasurable h' :=
    phiLoc_contDiff.continuous.stronglyMeasurable.mul (gG_meas hGm')
  have hh : Integrable h :=
    (phiLoc_integrable hR).mul_bdd (gG_meas hGm).aestronglyMeasurable
      (Eventually.of_forall (fun y => gG_norm_le G y))
  have hh' : Integrable h' :=
    (phiLoc_integrable hR).mul_bdd (gG_meas hGm').aestronglyMeasurable
      (Eventually.of_forall (fun y => gG_norm_le G' y))
  have hF : ∀ ω : E n, Fop n R c G ω = ∫ y, h y * (𝐞 (-⟪y, ω⟫) : ℂ) :=
    fun ω => Fop_repr hR c hG ω
  have hF' : ∀ ω : E n, Fop n R c' G' ω = ∫ y, h' y * (𝐞 (-⟪y, ω⟫) : ℂ) :=
    fun ω => Fop_repr hR c' hG' ω
  have hprod : ∀ ω : E n, Fop n R c G ω * conj (Fop n R c' G' ω) =
      ∫ p : E n × E n, h p.1 * conj (h' p.2) * (𝐞 (-⟪ω, p.1 - p.2⟫) : ℂ) := by
    intro ω
    rw [hF, hF', ← integral_conj, ← integral_prod_mul]
    congr 1; ext p
    rw [map_mul, conj_e, inner_sub_right, real_inner_comm ω p.1, real_inner_comm ω p.2]
    have : -(⟪ω, p.1⟫ - ⟪ω, p.2⟫) = -⟪ω, p.1⟫ + -(-⟪ω, p.2⟫) := by ring
    rw [this, AddChar.map_add_eq_mul, Circle.coe_mul]; ring
  simp_rw [hprod]
  have hint : Integrable (Function.uncurry fun (ω : sphere (0 : E n) 1) (p : E n × E n) =>
      h p.1 * conj (h' p.2) * (𝐞 (-⟪(ω : E n), p.1 - p.2⟫) : ℂ))
      ((sphereMeasure n).prod volume) := by
    have h1 : Integrable (fun p : E n × E n => ‖h p.1‖ * ‖h' p.2‖) volume :=
      hh.norm.mul_prod hh'.norm
    have h2 : Integrable (fun q : sphere (0 : E n) 1 × (E n × E n) =>
        (1 : ℝ) * (‖h q.2.1‖ * ‖h' q.2.2‖)) ((sphereMeasure n).prod volume) :=
      (integrable_const (1 : ℝ)).mul_prod h1
    refine h2.mono ?_ (Eventually.of_forall (fun q => ?_))
    · refine StronglyMeasurable.aestronglyMeasurable ?_
      refine StronglyMeasurable.mul (StronglyMeasurable.mul ?_ ?_) ?_
      · exact hhm.comp_measurable (measurable_fst.comp measurable_snd)
      · exact (Complex.continuous_conj.comp_stronglyMeasurable
          (hhm'.comp_measurable (measurable_snd.comp measurable_snd)))
      · exact (Real.continuous_fourierChar.comp ((continuous_subtype_val.comp
          continuous_fst).inner ((continuous_fst.comp continuous_snd).sub
          (continuous_snd.comp continuous_snd))).neg).subtype_val.stronglyMeasurable
    · simp [Function.uncurry, Circle.norm_coe]
  rw [integral_integral_swap hint]
  have hsig : ∀ p : E n × E n, ∫ ω : sphere (0 : E n) 1,
      h p.1 * conj (h' p.2) * (𝐞 (-⟪(ω : E n), p.1 - p.2⟫) : ℂ) ∂(sphereMeasure n) =
      h p.1 * conj (h' p.2) * sig n (p.1 - p.2) := by
    intro p; rw [integral_const_mul]; rfl
  simp_rw [hsig]
  set A := ∫⁻ η, ‖G η‖ₑ
  set A' := ∫⁻ η, ‖G' η‖ₑ
  have hA : A ≠ ⊤ := hG.2.ne
  have hA' : A' ≠ ⊤ := hG'.2.ne
  refine (enorm_integral_le_lintegral_enorm _).trans ?_
  have hmeas : AEMeasurable (fun p : E n × E n =>
      ‖phiLoc n R c p.1‖ₑ * ‖phiLoc n R c' p.2‖ₑ * ‖sig n (p.1 - p.2)‖ₑ) volume := by
    refine Measurable.aemeasurable ?_
    have m1 : Measurable (fun p : E n × E n => ‖phiLoc n R c p.1‖ₑ) :=
      ((phiLoc_contDiff (c := c) (R := R)).continuous.comp continuous_fst).measurable.enorm
    have m2 : Measurable (fun p : E n × E n => ‖phiLoc n R c' p.2‖ₑ) :=
      ((phiLoc_contDiff (c := c') (R := R)).continuous.comp continuous_snd).measurable.enorm
    have m3 : Measurable (fun p : E n × E n => ‖sig n (p.1 - p.2)‖ₑ) :=
      ((sig_meas (n := n)).measurable.comp (measurable_fst.sub measurable_snd)).enorm
    exact (m1.mul m2).mul m3
  calc ∫⁻ p : E n × E n, ‖h p.1 * conj (h' p.2) * sig n (p.1 - p.2)‖ₑ
      ≤ ∫⁻ p : E n × E n, A * A' * (‖phiLoc n R c p.1‖ₑ * ‖phiLoc n R c' p.2‖ₑ * ‖sig n (p.1 - p.2)‖ₑ) := by
        refine lintegral_mono (fun p => ?_)
        simp only [hh_def, hh'_def, enorm_mul, RCLike.enorm_conj, map_mul]
        have e1 := gG_enorm_le G p.1
        have e2 := gG_enorm_le G' p.2
        calc ‖phiLoc n R c p.1‖ₑ * ‖gG G p.1‖ₑ * (‖phiLoc n R c' p.2‖ₑ * ‖gG G' p.2‖ₑ) *
              ‖sig n (p.1 - p.2)‖ₑ
            ≤ ‖phiLoc n R c p.1‖ₑ * A * (‖phiLoc n R c' p.2‖ₑ * A') * ‖sig n (p.1 - p.2)‖ₑ := by
              gcongr
          _ = _ := by ring
    _ = A * A' * ∫⁻ y, ∫⁻ y', ‖phiLoc n R c y‖ₑ * ‖phiLoc n R c' y'‖ₑ * ‖sig n (y - y')‖ₑ := by
        rw [lintegral_const_mul' _ _ (ENNReal.mul_ne_top hA hA'), Measure.volume_eq_prod,
          lintegral_prod _ hmeas]

/-- `∫ ‖φ‖`. -/
noncomputable def M0 (n : ℕ) : ℝ := ∫ u, ‖phi n u‖

/-- `∫ ‖u‖ ‖φ(u)‖`. -/
noncomputable def M1 (n : ℕ) : ℝ := ∫ u : E n, ‖u‖ * ‖phi n u‖

lemma M0_nonneg : 0 ≤ M0 n := integral_nonneg (fun _ => norm_nonneg _)

lemma M1_nonneg : 0 ≤ M1 n := integral_nonneg (fun _ => by positivity)

lemma phiLoc_lint (hR : 0 < R) (c : E n) :
    ∫⁻ y, ‖phiLoc n R c y‖ₑ = ENNReal.ofReal (R ^ n * M0 n) := by
  rw [← ofReal_integral_norm_eq_lintegral_enorm (phiLoc_integrable hR), phiLoc_L1 hR, M0]

lemma phiLoc_mom_lint (hR : 0 < R) (c : E n) :
    ∫⁻ y, ENNReal.ofReal ‖y - c‖ * ‖phiLoc n R c y‖ₑ = ENNReal.ofReal (R ^ (n + 1) * M1 n) := by
  rw [M1, ← phiLoc_moment (c := c) hR, ofReal_integral_eq_lintegral_ofReal (phiLoc_moment_integrable hR)
    (Eventually.of_forall (fun _ => by positivity))]
  congr 1; ext y
  rw [ENNReal.ofReal_mul (norm_nonneg _)]; simp only [ofReal_norm]

lemma kern_le (hR : 0 < R) (c c' : E n) (B T : ℝ) (hB : 0 ≤ B) (hT : 0 ≤ T)
    (hpt : ∀ y y' : E n, ‖sig n (y - y')‖ ≤ B + T * (‖y - c‖ + ‖y' - c'‖)) :
    ∫⁻ y, ∫⁻ y', ‖phiLoc n R c y‖ₑ * ‖phiLoc n R c' y'‖ₑ * ‖sig n (y - y')‖ₑ ≤
      ENNReal.ofReal (B * (R ^ n * M0 n) ^ 2 + T * (2 * R ^ (2 * n + 1) * M0 n * M1 n)) := by
  set a : E n → ℝ≥0∞ := fun y => ‖phiLoc n R c y‖ₑ
  set a' : E n → ℝ≥0∞ := fun y => ‖phiLoc n R c' y‖ₑ
  set b : E n → ℝ≥0∞ := fun y => ENNReal.ofReal ‖y - c‖ * ‖phiLoc n R c y‖ₑ
  set b' : E n → ℝ≥0∞ := fun y => ENNReal.ofReal ‖y - c'‖ * ‖phiLoc n R c' y‖ₑ
  have ha : Measurable a := (phiLoc_contDiff (c := c) (R := R)).continuous.measurable.enorm
  have ha' : Measurable a' := (phiLoc_contDiff (c := c') (R := R)).continuous.measurable.enorm
  have hb : Measurable b :=
    ((continuous_id.sub continuous_const).norm.measurable.ennreal_ofReal).mul ha
  have hb' : Measurable b' :=
    ((continuous_id.sub continuous_const).norm.measurable.ennreal_ofReal).mul ha'
  set β := ENNReal.ofReal B
  set τ := ENNReal.ofReal T
  have hpt' : ∀ y y', a y * a' y' * ‖sig n (y - y')‖ₑ ≤
      β * a y * a' y' + (τ * b y * a' y' + τ * a y * b' y') := by
    intro y y'
    have h1 : ‖sig n (y - y')‖ₑ ≤ β + τ * (ENNReal.ofReal ‖y - c‖ + ENNReal.ofReal ‖y' - c'‖) := by
      rw [← ofReal_norm, ← ENNReal.ofReal_add (norm_nonneg _) (norm_nonneg _),
        ← ENNReal.ofReal_mul hT, ← ENNReal.ofReal_add hB (by positivity)]
      exact ENNReal.ofReal_le_ofReal (hpt y y')
    calc a y * a' y' * ‖sig n (y - y')‖ₑ
        ≤ a y * a' y' * (β + τ * (ENNReal.ofReal ‖y - c‖ + ENNReal.ofReal ‖y' - c'‖)) := by
          gcongr
      _ = _ := by simp only [a, a', b, b']; ring
  calc ∫⁻ y, ∫⁻ y', a y * a' y' * ‖sig n (y - y')‖ₑ
      ≤ ∫⁻ y, ∫⁻ y', β * a y * a' y' + (τ * b y * a' y' + τ * a y * b' y') :=
        lintegral_mono (fun y => lintegral_mono (fun y' => hpt' y y'))
    _ = β * (∫⁻ y, a y) * (∫⁻ y, a' y) +
          (τ * (∫⁻ y, b y) * (∫⁻ y, a' y) + τ * (∫⁻ y, a y) * (∫⁻ y, b' y)) := by
        have e : ∀ y, ∫⁻ y', β * a y * a' y' + (τ * b y * a' y' + τ * a y * b' y') =
            β * a y * (∫⁻ y', a' y') + (τ * b y * (∫⁻ y', a' y') + τ * a y * ∫⁻ y', b' y') := by
          intro y
          rw [lintegral_add_left (ha'.const_mul _), lintegral_add_left (ha'.const_mul _),
            lintegral_const_mul _ ha', lintegral_const_mul _ ha', lintegral_const_mul _ hb']
        simp_rw [e]
        rw [lintegral_add_left ((ha.const_mul _).mul_const _),
          lintegral_add_left (((hb.const_mul _)).mul_const _),
          lintegral_mul_const _ (ha.const_mul _), lintegral_mul_const _ (hb.const_mul _),
          lintegral_mul_const _ (ha.const_mul _), lintegral_const_mul _ ha,
          lintegral_const_mul _ hb, lintegral_const_mul _ ha]
    _ = _ := by
        simp only [a, a', b, b']
        rw [phiLoc_lint hR, phiLoc_lint hR, phiLoc_mom_lint hR, phiLoc_mom_lint hR]
        have h0 := M0_nonneg (n := n)
        have h1 := M1_nonneg (n := n)
        simp only [β, τ]
        rw [← ENNReal.ofReal_mul hB, ← ENNReal.ofReal_mul (by positivity),
          ← ENNReal.ofReal_mul hT, ← ENNReal.ofReal_mul (by positivity),
          ← ENNReal.ofReal_mul hT, ← ENNReal.ofReal_mul (by positivity),
          ← ENNReal.ofReal_add (by positivity) (by positivity),
          ← ENNReal.ofReal_add (by positivity) (by positivity)]
        congr 1
        ring

lemma sig_pt (m : ℕ) (hm : 0 < m) (Cs : ℝ)
    (hdec : ∀ z : E n, 1 ≤ ‖z‖ → ‖sig n z‖ ^ m * ‖z‖ ≤ Cs) (c c' : E n) (Q : ℝ) (hQ : 1 ≤ Q)
    (hw2 : 2 ≤ ‖c - c'‖) (hQw : Q ^ m ≤ ‖c - c'‖) (y y' : E n) :
    ‖sig n (y - y')‖ ≤ max 1 (2 * Cs) / Q +
      4 * (sphereMeasure n).real univ / ‖c - c'‖ * (‖y - c‖ + ‖y' - c'‖) := by
  set w := c - c'
  set d := ‖y - c‖ + ‖y' - c'‖
  set D := max 1 (2 * Cs)
  set s := (sphereMeasure n).real univ
  have hs : 0 ≤ s := measureReal_nonneg
  have hw0 : 0 < ‖w‖ := by linarith
  have hd0 : 0 ≤ d := by positivity
  have hD1 : 1 ≤ D := le_max_left _ _
  have hDQ : 0 ≤ D / Q := by positivity
  have hsig := sig_norm_le n (y - y')
  by_cases hd : d * 2 ≤ ‖w‖
  · have hz : ‖w‖ / 2 ≤ ‖y - y'‖ := by
      have e : y - y' = w + (y - c) - (y' - c') := by simp only [w]; abel
      have := norm_sub_norm_le w (-(y - c) + (y' - c'))
      have h2 : ‖-(y - c) + (y' - c')‖ ≤ d := (norm_add_le _ _).trans (by rw [norm_neg])
      have e2 : w - (-(y - c) + (y' - c')) = y - y' := by rw [e]; abel
      rw [e2] at this
      linarith
    have hz1 : 1 ≤ ‖y - y'‖ := by linarith
    have hk := hdec (y - y') hz1
    set a := ‖sig n (y - y')‖
    have ha : 0 ≤ a := norm_nonneg _
    have hCs : 0 ≤ Cs := le_trans (by positivity) hk
    have h1 : a ^ m * ‖w‖ ≤ 2 * Cs := by
      have : a ^ m * (‖w‖ / 2) ≤ Cs :=
        le_trans (mul_le_mul_of_nonneg_left hz (by positivity)) hk
      linarith
    have h2 : (a * Q) ^ m ≤ D ^ m := by
      rw [mul_pow]
      calc a ^ m * Q ^ m ≤ a ^ m * ‖w‖ := mul_le_mul_of_nonneg_left hQw (by positivity)
        _ ≤ 2 * Cs := h1
        _ ≤ D := le_max_right _ _
        _ ≤ D ^ m := le_self_pow₀ hD1 hm.ne'
    have h3 : a * Q ≤ D :=
      (pow_le_pow_iff_left₀ (by positivity) (by positivity) hm.ne').1 h2
    have h4 : a ≤ D / Q := by rw [le_div_iff₀ (by linarith)]; exact h3
    have : 0 ≤ 4 * s / ‖w‖ * d := by positivity
    linarith
  · rw [not_le] at hd
    have : s ≤ 4 * s / ‖w‖ * d := by
      rw [div_mul_eq_mul_div, le_div_iff₀ hw0]
      nlinarith
    linarith

end TaoBR.RSU

end
end

section
section
/-!
# The operator `T`
-/

open MeasureTheory Metric Set Filter Topology
open scoped FourierTransform ENNReal NNReal SchwartzMap RealInnerProductSpace ComplexConjugate
  Pointwise

namespace TaoBR.RSU

/-- `T G (ω) = Σ_i ∫ K_i(ω - η) G_i(η) dη` on the sphere. -/
noncomputable def Top (n : ℕ) {N : ℕ} (R : ℝ) (x : Fin N → E n) (G : Fin N → E n → ℂ)
    (ω : sphere (0 : E n) 1) : ℂ :=
  ∑ i, ∫ η, K n R (x i) ((ω : E n) - η) * G i η

/-- The `L¹` constant. -/
noncomputable def A1 (n : ℕ) : ℝ :=
  MPhi n * 2 ^ n * (1 / 16) ^ (n - 1) * (volume : Measure (E n)).real (ball 0 1)

variable {n : ℕ} {N : ℕ} {R : ℝ} {x : Fin N → E n}

lemma Top_add (hR : 0 < R) (G G' : Fin N → E n → ℂ) (hG : ∀ i, Integrable (G i))
    (hG' : ∀ i, Integrable (G' i)) : Top n R x (G + G') = Top n R x G + Top n R x G' := by
  funext ω
  simp only [Top, Pi.add_apply, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  have hb : ∀ (H : E n → ℂ), Integrable H →
      Integrable (fun η => K n R (x i) ((ω : E n) - η) * H η) := by
    intro H hH
    refine hH.bdd_mul (c := R ^ n * MPhi n) ?_ (Eventually.of_forall (fun η => K_norm_le hR _))
    exact (K_continuous.comp (continuous_const.sub continuous_id)).aestronglyMeasurable
  rw [← integral_add (hb _ (hG i)) (hb _ (hG' i))]
  congr 1; ext η; ring

lemma Top_meas (G : Fin N → E n → ℂ) (hG : ∀ i, Measurable (G i)) :
    Measurable (Top n R x G) := by
  unfold Top
  refine Finset.measurable_sum _ (fun i _ => ?_)
  refine StronglyMeasurable.measurable ?_
  refine StronglyMeasurable.integral_prod_right (f := fun (ω : sphere (0 : E n) 1) (η : E n) =>
    K n R (x i) ((ω : E n) - η) * G i η) ?_
  refine Measurable.stronglyMeasurable ?_
  exact (K_continuous.measurable.comp ((measurable_subtype_coe.comp measurable_fst).sub
    measurable_snd)).mul ((hG i).comp measurable_snd)

lemma K_cap (hn : 1 ≤ n) (hR : 1 ≤ R) (c η : E n) :
    ∫⁻ ω, ‖K n R c ((ω : E n) - η)‖ₑ ∂(sphereMeasure n) ≤ ENNReal.ofReal (A1 n * R) := by
  have hR0 : 0 < R := by linarith
  set r := 1 / (16 * R)
  set cap := {ω : sphere (0 : E n) 1 | dist (ω : E n) η < r}
  have hcap : MeasurableSet cap :=
    measurableSet_lt (continuous_subtype_val.dist continuous_const).measurable measurable_const
  have hpt : ∀ ω : sphere (0 : E n) 1, ‖K n R c ((ω : E n) - η)‖ₑ ≤
      cap.indicator (fun _ => ENNReal.ofReal (R ^ n * MPhi n)) ω := by
    intro ω
    by_cases hK : K n R c ((ω : E n) - η) = 0
    · rw [hK, enorm_zero]; exact bot_le
    · have hmem : ω ∈ cap := by
        have := K_support hR0 hK
        show dist (ω : E n) η < r
        rw [dist_eq_norm]; exact this
      rw [indicator_of_mem hmem, ← ofReal_norm]
      exact ENNReal.ofReal_le_ofReal (K_norm_le hR0 _)
  refine (lintegral_mono hpt).trans ?_
  rw [lintegral_indicator_const hcap]
  have hc := cap_le hn η (by positivity : 0 < r)
  calc ENNReal.ofReal (R ^ n * MPhi n) * sphereMeasure n cap
      ≤ ENNReal.ofReal (R ^ n * MPhi n) *
          (ENNReal.ofReal (2 ^ n * r ^ (n - 1)) * volume (ball (0 : E n) 1)) := by gcongr
    _ = ENNReal.ofReal (A1 n * R) := ?_
  rw [← ofReal_measureReal measure_ball_lt_top.ne, ← ENNReal.ofReal_mul (by positivity),
    ← ENNReal.ofReal_mul (by have := MPhi_nonneg n; positivity)]
  congr 1
  simp only [A1, r]
  have hn1 : R ^ n = R * R ^ (n - 1) := by rw [← pow_succ']; congr 1; omega
  rw [hn1, div_pow, mul_pow, one_pow]
  field_simp
  have h16 : (16 : ℝ) ^ (n - 1) * (1 / 16) ^ (n - 1) = 1 := by rw [← mul_pow]; norm_num
  linear_combination (-(MPhi n * (volume : Measure (E n)).real (ball 0 1))) * h16

lemma Top_L1 (hn : 1 ≤ n) (hR : 1 ≤ R) (G : Fin N → E n → ℂ) (hG : ∀ i, Measurable (G i)) :
    ∫⁻ ω, ‖Top n R x G ω‖ₑ ∂(sphereMeasure n) ≤
      ENNReal.ofReal (A1 n * R) * ∑ i, ∫⁻ η, ‖G i η‖ₑ := by
  have hpt : ∀ ω, ‖Top n R x G ω‖ₑ ≤ ∑ i, ∫⁻ η, ‖K n R (x i) ((ω : E n) - η)‖ₑ * ‖G i η‖ₑ := by
    intro ω
    refine (enorm_sum_le _ _).trans (Finset.sum_le_sum (fun i _ => ?_))
    refine (enorm_integral_le_lintegral_enorm _).trans (le_of_eq ?_)
    simp_rw [enorm_mul]
  have hm : ∀ i, Measurable (Function.uncurry fun (ω : sphere (0 : E n) 1) (η : E n) =>
      ‖K n R (x i) ((ω : E n) - η)‖ₑ * ‖G i η‖ₑ) := by
    intro i
    exact (K_continuous.measurable.comp ((measurable_subtype_coe.comp measurable_fst).sub
      measurable_snd)).enorm.mul ((hG i).comp measurable_snd).enorm
  refine (lintegral_mono hpt).trans ?_
  have hmi : ∀ i ∈ (Finset.univ : Finset (Fin N)), Measurable (fun ω : sphere (0 : E n) 1 =>
      ∫⁻ η, ‖K n R (x i) ((ω : E n) - η)‖ₑ * ‖G i η‖ₑ) := fun i _ => (hm i).lintegral_prod_right'
  rw [lintegral_finsetSum _ hmi, Finset.mul_sum]
  refine Finset.sum_le_sum (fun i _ => ?_)
  rw [lintegral_lintegral_swap (hm i).aemeasurable, ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  refine lintegral_mono (fun η => ?_)
  rw [lintegral_mul_const' _ _ enorm_ne_top]
  gcongr
  exact K_cap hn hR (x i) η

lemma Fop_diag (hn : 1 ≤ n) (hR : 1 ≤ R) (c : E n) {G : E n → ℂ} (hGm : Measurable G) :
    ∫⁻ ω, ‖Fop n R c G (ω : E n)‖ₑ ^ 2 ∂(sphereMeasure n) ≤
      ENNReal.ofReal (A1 n * R) * ∫⁻ η, ‖G η‖ₑ ^ 2 := by
  have hR0 : 0 < R := by linarith
  have hKm : Measurable (fun p : sphere (0 : E n) 1 × E n => ‖K n R c ((p.1 : E n) - p.2)‖ₑ) :=
    (K_continuous.measurable.comp ((measurable_subtype_coe.comp measurable_fst).sub
      measurable_snd)).enorm
  have hpt : ∀ ω : sphere (0 : E n) 1, ‖Fop n R c G (ω : E n)‖ₑ ^ 2 ≤
      ∫⁻ η, ‖K n R c ((ω : E n) - η)‖ₑ * ‖G η‖ₑ ^ 2 := by
    intro ω
    have h1 : ‖Fop n R c G (ω : E n)‖ₑ ≤ ∫⁻ η, ‖K n R c ((ω : E n) - η)‖ₑ * ‖G η‖ₑ := by
      refine (enorm_integral_le_lintegral_enorm _).trans (le_of_eq ?_)
      simp_rw [enorm_mul]
    have hK1 : ∫⁻ η, ‖K n R c ((ω : E n) - η)‖ₑ = 1 := by
      rw [lintegral_sub_left_eq_self (fun v => ‖K n R c v‖ₑ) (ω : E n)]
      exact K_lintegral hR0 c
    have hKm1 : Measurable (fun η : E n => ‖K n R c ((ω : E n) - η)‖ₑ) :=
      (K_continuous.measurable.comp (measurable_const.sub measurable_id)).enorm
    calc ‖Fop n R c G (ω : E n)‖ₑ ^ 2
        ≤ (∫⁻ η, ‖K n R c ((ω : E n) - η)‖ₑ * ‖G η‖ₑ) ^ 2 := by gcongr
      _ ≤ (∫⁻ η, ‖K n R c ((ω : E n) - η)‖ₑ) * ∫⁻ η, ‖K n R c ((ω : E n) - η)‖ₑ * ‖G η‖ₑ ^ 2 :=
          lintegral_cs _ hKm1.aemeasurable hGm.enorm.aemeasurable
      _ = _ := by rw [hK1, one_mul]
  refine (lintegral_mono hpt).trans ?_
  rw [lintegral_lintegral_swap (hKm.mul ((hGm.comp measurable_snd).enorm.pow_const 2)).aemeasurable,
    ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  refine lintegral_mono (fun η => ?_)
  rw [lintegral_mul_const' _ _ (by simp)]
  gcongr
  exact K_cap hn hR c η

/-- The off-diagonal constant. -/
noncomputable def Cst (n : ℕ) (Cs : ℝ) : ℝ :=
  max 1 (2 * Cs) * M0 n ^ 2 + 8 * (sphereMeasure n).real univ * M0 n * M1 n

lemma kern_sparse (hn : 1 ≤ n) (m : ℕ) (hm : 0 < m) (Cs : ℝ)
    (hdec : ∀ z : E n, 1 ≤ ‖z‖ → ‖sig n z‖ ^ m * ‖z‖ ≤ Cs) (hR : 1 ≤ R) (N : ℕ) (hN : 2 ≤ N)
    (c c' : E n) (hw : (R * N) ^ (2 * n * m + 3 * n + 3) ≤ ‖c - c'‖) :
    ∫⁻ y, ∫⁻ y', ‖phiLoc n R c y‖ₑ * ‖phiLoc n R c' y'‖ₑ * ‖sig n (y - y')‖ₑ ≤
      ENNReal.ofReal (Cst n Cs / N) := by
  have hR0 : 0 < R := by linarith
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast (by omega : 1 ≤ N)
  have hN2 : (2 : ℝ) ≤ N := by exact_mod_cast hN
  set X := R * (N : ℝ) with hX
  have hX2 : 2 ≤ X := by nlinarith
  have hX1 : 1 ≤ X := by linarith
  set C0 := 2 * n * m + 3 * n + 3
  set w := c - c'
  set Q := R ^ (2 * n) * (N : ℝ) with hQ
  have hQ1 : 1 ≤ Q := one_le_mul_of_one_le_of_one_le (one_le_pow₀ hR) hN1
  have hw2 : 2 ≤ ‖w‖ := le_trans (le_trans hX2 (le_self_pow₀ hX1 (by omega))) hw
  have hw0 : 0 < ‖w‖ := by linarith
  have hQw : Q ^ m ≤ ‖w‖ := by
    calc Q ^ m = R ^ (2 * n * m) * (N : ℝ) ^ m := by rw [hQ, mul_pow, ← pow_mul]
      _ ≤ R ^ (2 * n * m) * (N : ℝ) ^ (2 * n * m) := by
          gcongr
          nlinarith
      _ = X ^ (2 * n * m) := by rw [hX, mul_pow]
      _ ≤ X ^ C0 := pow_le_pow_right₀ hX1 (by omega)
      _ ≤ ‖w‖ := hw
  have hRw : R ^ (2 * n + 1) * N ≤ ‖w‖ := by
    calc R ^ (2 * n + 1) * (N : ℝ) ≤ R ^ (2 * n + 1) * (N : ℝ) ^ (2 * n + 1) := by
          gcongr; exact le_self_pow₀ hN1 (by omega)
      _ = X ^ (2 * n + 1) := by rw [hX, mul_pow]
      _ ≤ X ^ C0 := pow_le_pow_right₀ hX1 (by omega)
      _ ≤ ‖w‖ := hw
  set D := max 1 (2 * Cs)
  set s := (sphereMeasure n).real univ
  have hs : 0 ≤ s := measureReal_nonneg
  have hD : 0 ≤ D := le_trans zero_le_one (le_max_left _ _)
  have hk := kern_le hR0 c c' (D / Q) (4 * s / ‖w‖) (by positivity) (by positivity)
    (sig_pt m hm Cs hdec c c' Q hQ1 hw2 hQw)
  refine hk.trans (ENNReal.ofReal_le_ofReal ?_)
  have h0 := M0_nonneg (n := n)
  have h1 := M1_nonneg (n := n)
  have hN0 : (0 : ℝ) < N := by linarith
  have t1 : D / Q * (R ^ n * M0 n) ^ 2 = D * M0 n ^ 2 / N := by
    rw [hQ, mul_pow, ← pow_mul]; field_simp; ring
  have t2 : 4 * s / ‖w‖ * (2 * R ^ (2 * n + 1) * M0 n * M1 n) ≤
      8 * s * M0 n * M1 n / N := by
    rw [div_mul_eq_mul_div, div_le_div_iff₀ hw0 hN0]
    have := mul_le_mul_of_nonneg_left hRw (by positivity : 0 ≤ 8 * s * M0 n * M1 n)
    nlinarith
  rw [t1, Cst, add_div]
  linarith

lemma A1_nonneg (n : ℕ) : 0 ≤ A1 n := by
  unfold A1; have := MPhi_nonneg n; positivity

lemma Cst_nonneg (n : ℕ) (Cs : ℝ) : 0 ≤ Cst n Cs := by
  unfold Cst
  have := M0_nonneg (n := n)
  have := M1_nonneg (n := n)
  have : 0 ≤ (sphereMeasure n).real univ := measureReal_nonneg
  have : 0 ≤ max 1 (2 * Cs) := le_trans zero_le_one (le_max_left _ _)
  positivity

lemma Top_L2_core (hn : 1 ≤ n) (m : ℕ) (hm : 0 < m) (Cs : ℝ)
    (hdec : ∀ z : E n, 1 ≤ ‖z‖ → ‖sig n z‖ ^ m * ‖z‖ ≤ Cs) (hR : 1 ≤ R) (V : ℝ) (hV : 0 ≤ V)
    (hsp : ∀ i j, i ≠ j → (R * N) ^ (2 * n * m + 3 * n + 3) ≤ ‖x i - x j‖)
    (G : Fin N → E n → ℂ) (hGi : ∀ i, Integrable (G i)) (hGs : ∀ i, StronglyMeasurable (G i))
    (hL2 : ∀ i, ∫⁻ η, ‖G i η‖ₑ ^ 2 ≠ ⊤)
    (hL1 : ∀ i, (∫⁻ η, ‖G i η‖ₑ) ^ 2 ≤ ENNReal.ofReal V * ∫⁻ η, ‖G i η‖ₑ ^ 2) :
    ∫⁻ ω, ‖Top n R x G ω‖ₑ ^ 2 ∂(sphereMeasure n) ≤
      ENNReal.ofReal ((A1 n + Cst n Cs * V) * R) * ∑ i, ∫⁻ η, ‖G i η‖ₑ ^ 2 := by
  have hR0 : 0 < R := by linarith
  set σ := sphereMeasure n
  set F : Fin N → sphere (0 : E n) 1 → ℂ := fun i ω => Fop n R (x i) (G i) (ω : E n) with hF
  have hTop : ∀ ω, Top n R x G ω = ∑ i, F i ω := fun ω => rfl
  have hFm : ∀ i, StronglyMeasurable (F i) := by
    intro i
    refine StronglyMeasurable.integral_prod_right (f := fun (ω : sphere (0 : E n) 1) (η : E n) =>
      K n R (x i) ((ω : E n) - η) * G i η) ?_
    exact (K_continuous.comp ((continuous_subtype_val.comp continuous_fst).sub
      continuous_snd)).stronglyMeasurable.mul ((hGs i).comp_measurable measurable_snd)
  set Mb : Fin N → ℝ := fun i => R ^ n * MPhi n * ∫ η, ‖G i η‖
  have hFb : ∀ i ω, ‖F i ω‖ ≤ Mb i := by
    intro i ω
    refine (norm_integral_le_of_norm_le ((hGi i).norm.const_mul (R ^ n * MPhi n))
      (Eventually.of_forall (fun η => ?_))).trans (le_of_eq (integral_const_mul _ _))
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_right (K_norm_le hR0 _) (norm_nonneg _)
  have hPint : ∀ i j, Integrable (fun ω => F i ω * conj (F j ω)) σ := by
    intro i j
    refine Integrable.of_bound ((hFm i).mul (Complex.continuous_conj.comp_stronglyMeasurable
      (hFm j))).aestronglyMeasurable (Mb i * Mb j) (Eventually.of_forall (fun ω => ?_))
    rw [norm_mul, RCLike.norm_conj]
    exact mul_le_mul (hFb i ω) (hFb j ω) (norm_nonneg _) ((norm_nonneg _).trans (hFb i ω))
  have hsq : ∀ ω, ‖Top n R x G ω‖ ^ 2 = ∑ i, ∑ j, (F i ω * conj (F j ω)).re := by
    intro ω
    rw [hTop]
    have h1 : ((‖∑ i, F i ω‖ ^ 2 : ℝ) : ℂ) = ∑ i, ∑ j, F i ω * conj (F j ω) := by
      rw [Complex.ofReal_pow, ← Complex.mul_conj', map_sum, Finset.sum_mul_sum]
    have := congrArg Complex.re h1
    simpa only [Complex.ofReal_re, Complex.re_sum] using this
  have hint : ∀ i j, Integrable (fun ω => (F i ω * conj (F j ω)).re) σ := fun i j => (hPint i j).re
  have hLHS : ∫⁻ ω, ‖Top n R x G ω‖ₑ ^ 2 ∂σ =
      ENNReal.ofReal (∑ i, ∑ j, (∫ ω, F i ω * conj (F j ω) ∂σ).re) := by
    have e : ∀ ω, ‖Top n R x G ω‖ₑ ^ 2 =
        ENNReal.ofReal (∑ i, ∑ j, (F i ω * conj (F j ω)).re) := by
      intro ω; rw [← hsq, ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm]
    simp_rw [e]
    rw [← ofReal_integral_eq_lintegral_ofReal]
    · congr 1
      rw [integral_finsetSum _ (fun i _ => integrable_finsetSum _ (fun j _ => hint i j))]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      rw [integral_finsetSum _ (fun j _ => hint i j)]
      refine Finset.sum_congr rfl (fun j _ => ?_)
      exact integral_re (hPint i j)
    · exact integrable_finsetSum _ (fun i _ => integrable_finsetSum _ (fun j _ => hint i j))
    · exact Eventually.of_forall (fun ω => by simp only [Pi.zero_apply]; rw [← hsq]; positivity)
  set a : Fin N → ℝ := fun i => (∫⁻ η, ‖G i η‖ₑ).toReal
  set b : Fin N → ℝ := fun i => (∫⁻ η, ‖G i η‖ₑ ^ 2).toReal
  have hA : ∀ i, ∫⁻ η, ‖G i η‖ₑ = ENNReal.ofReal (a i) :=
    fun i => (ENNReal.ofReal_toReal (hGi i).2.ne).symm
  have hB : ∀ i, ∫⁻ η, ‖G i η‖ₑ ^ 2 = ENNReal.ofReal (b i) :=
    fun i => (ENNReal.ofReal_toReal (hL2 i)).symm
  have ha0 : ∀ i, 0 ≤ a i := fun i => ENNReal.toReal_nonneg
  have hb0 : ∀ i, 0 ≤ b i := fun i => ENNReal.toReal_nonneg
  have hab : ∀ i, a i ^ 2 ≤ V * b i := by
    intro i
    have := hL1 i
    rw [hA, hB, ← ENNReal.ofReal_pow (ha0 i), ← ENNReal.ofReal_mul hV] at this
    exact (ENNReal.ofReal_le_ofReal_iff (mul_nonneg hV (hb0 i))).1 this
  have hdiag : ∀ i, (∫ ω, F i ω * conj (F i ω) ∂σ).re ≤ A1 n * R * b i := by
    intro i
    have hre : ∫ ω, (F i ω * conj (F i ω)).re ∂σ = (∫ ω, F i ω * conj (F i ω) ∂σ).re :=
      integral_re (hPint i i)
    rw [← hre]
    have e : ∀ ω, (F i ω * conj (F i ω)).re = ‖F i ω‖ ^ 2 := by
      intro ω; rw [Complex.mul_conj']; norm_cast
    simp_rw [e]
    rw [integral_eq_lintegral_of_nonneg_ae (f := fun ω => ‖F i ω‖ ^ 2)
      (Eventually.of_forall (fun _ => by positivity))
      ((hFm i).measurable.norm.pow_const 2).aestronglyMeasurable]
    have e2 : ∀ ω, ENNReal.ofReal (‖F i ω‖ ^ 2) = ‖F i ω‖ₑ ^ 2 := by
      intro ω; rw [ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm]
    simp_rw [e2]
    have hd := Fop_diag hn hR (x i) (hGs i).measurable
    rw [hB i, ← ENNReal.ofReal_mul (by have := A1_nonneg n; positivity)] at hd
    calc _ ≤ (ENNReal.ofReal (A1 n * R * b i)).toReal := ENNReal.toReal_mono ENNReal.ofReal_ne_top hd
      _ = _ := ENNReal.toReal_ofReal (by have := A1_nonneg n; have := hb0 i; positivity)
  have hC := Cst_nonneg n Cs
  have hoff : ∀ i j, i ≠ j →
      (∫ ω, F i ω * conj (F j ω) ∂σ).re ≤ Cst n Cs / N * (a i * a j) := by
    intro i j hij
    have hN : 2 ≤ N := by
      have := i.2; have := j.2; have : (i : ℕ) ≠ j := Fin.val_ne_of_ne hij; omega
    have hk := kern_sparse hn m hm Cs hdec hR N hN (x i) (x j) (hsp i j hij)
    have ho := Fop_offdiag hR0 (x i) (x j) (hGi i) (hGi j) (hGs i) (hGs j)
    rw [hA, hA] at ho
    have h2 := ho.trans (mul_le_mul_of_nonneg_left hk (by positivity))
    have hai := ha0 i
    have haj := ha0 j
    have hNn : (0 : ℝ) ≤ N := Nat.cast_nonneg N
    rw [← ENNReal.ofReal_mul hai, ← ENNReal.ofReal_mul (by positivity), ← ofReal_norm] at h2
    have h3 := (ENNReal.ofReal_le_ofReal_iff (by positivity)).1 h2
    calc _ ≤ ‖∫ ω, F i ω * conj (F j ω) ∂σ‖ := Complex.re_le_norm _
      _ ≤ _ := h3.trans (le_of_eq (by ring))
  have hsum : ∑ i, ∑ j, (∫ ω, F i ω * conj (F j ω) ∂σ).re ≤
      ∑ i, ∑ j, ((if i = j then A1 n * R * b i else 0) + Cst n Cs / N * (a i * a j)) := by
    refine Finset.sum_le_sum (fun i _ => Finset.sum_le_sum (fun j _ => ?_))
    by_cases hij : i = j
    · subst hij
      simp only [if_true]
      have := hdiag i
      have : 0 ≤ Cst n Cs / N * (a i * a i) := by
        have := ha0 i; have : (0 : ℝ) ≤ N := Nat.cast_nonneg N; positivity
      linarith
    · simp only [hij, if_false, zero_add]
      exact hoff i j hij
  have hcomb : ∑ i, ∑ j, ((if i = j then A1 n * R * b i else 0) + Cst n Cs / N * (a i * a j)) =
      A1 n * R * ∑ i, b i + Cst n Cs / N * (∑ i, a i) ^ 2 := by
    simp only [Finset.sum_add_distrib, Finset.sum_ite_eq, Finset.mem_univ, if_true,
      ← Finset.mul_sum, sq, Finset.sum_mul_sum]
  have hCS : Cst n Cs / N * (∑ i, a i) ^ 2 ≤ Cst n Cs * V * ∑ i, b i := by
    have h1 : (∑ i, a i) ^ 2 ≤ N * ∑ i, a i ^ 2 := by
      simpa using sq_sum_le_card_mul_sum_sq (s := Finset.univ) (f := a)
    have h2 : ∑ i, a i ^ 2 ≤ V * ∑ i, b i := by
      rw [Finset.mul_sum]; exact Finset.sum_le_sum (fun i _ => hab i)
    rcases Nat.eq_zero_or_pos N with hN | hN
    · subst hN; simp
    · have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
      rw [div_mul_eq_mul_div, div_le_iff₀ hN0]
      calc Cst n Cs * (∑ i, a i) ^ 2 ≤ Cst n Cs * (N * (V * ∑ i, b i)) := by
            gcongr; exact h1.trans (by gcongr)
        _ = _ := by ring
  have hbn : 0 ≤ ∑ i, b i := Finset.sum_nonneg (fun i _ => hb0 i)
  rw [hLHS]
  calc ENNReal.ofReal (∑ i, ∑ j, (∫ ω, F i ω * conj (F j ω) ∂σ).re)
      ≤ ENNReal.ofReal ((A1 n + Cst n Cs * V) * R * ∑ i, b i) := by
        apply ENNReal.ofReal_le_ofReal
        have hcv : 0 ≤ Cst n Cs * V * ∑ i, b i := by positivity
        have : Cst n Cs * V * ∑ i, b i ≤ Cst n Cs * V * R * ∑ i, b i := by nlinarith
        nlinarith [hsum, hcomb, hCS]
    _ = _ := by
        rw [ENNReal.ofReal_mul (by have := A1_nonneg n; positivity),
          ENNReal.ofReal_sum_of_nonneg (fun i _ => hb0 i)]
        congr 1
        exact Finset.sum_congr rfl (fun i _ => (hB i).symm)

lemma l1_l2_ball (g : E n → ℂ) (hgm : Measurable g)
    (hg : ∀ η, η ∉ closedBall (0 : E n) 2 → g η = 0) :
    (∫⁻ η, ‖g η‖ₑ) ^ 2 ≤
      ENNReal.ofReal ((volume : Measure (E n)).real (closedBall 0 2)) * ∫⁻ η, ‖g η‖ₑ ^ 2 := by
  set a : E n → ℝ≥0∞ := (closedBall (0 : E n) 2).indicator 1
  have ha : Measurable a := measurable_one.indicator measurableSet_closedBall
  have hab : ∀ η, a η * ‖g η‖ₑ = ‖g η‖ₑ := by
    intro η
    by_cases h : η ∈ closedBall (0 : E n) 2
    · simp [a, indicator_of_mem h]
    · simp [hg η h]
  have hb : ∀ η, a η * ‖g η‖ₑ ^ 2 ≤ ‖g η‖ₑ ^ 2 := by
    intro η
    by_cases h : η ∈ closedBall (0 : E n) 2
    · simp [a, indicator_of_mem h]
    · simp [hg η h]
  have h := lintegral_cs (volume : Measure (E n)) (a := a) (b := fun η => ‖g η‖ₑ)
    ha.aemeasurable hgm.enorm.aemeasurable
  simp only [hab] at h
  have h1 : ∫⁻ η, a η = ENNReal.ofReal ((volume : Measure (E n)).real (closedBall 0 2)) := by
    rw [lintegral_indicator_one measurableSet_closedBall,
      ofReal_measureReal (isCompact_closedBall _ _).measure_lt_top.ne]
  rw [h1] at h
  exact h.trans (by gcongr; exact hb _)

lemma Top_eq_restrict (hR : 1 ≤ R) (G : Fin N → E n → ℂ) (hG : ∀ i, Integrable (G i)) :
    Top n R x G = Top n R x (fun i => (closedBall (0 : E n) 2).indicator
      ((hG i).aestronglyMeasurable.mk (G i))) := by
  have hR0 : 0 < R := by linarith
  funext ω
  unfold Top
  refine Finset.sum_congr rfl (fun i _ => integral_congr_ae ?_)
  filter_upwards [(hG i).aestronglyMeasurable.ae_eq_mk] with η hη
  by_cases hK : K n R (x i) ((ω : E n) - η) = 0
  · simp [hK]
  · have h1 := K_support hR0 hK
    have hω : ‖(ω : E n)‖ = 1 := mem_sphere_zero_iff_norm.1 ω.2
    have h2 : 1 / (16 * R) ≤ 1 := by rw [div_le_one (by positivity)]; linarith
    have hmem : η ∈ closedBall (0 : E n) 2 := by
      rw [mem_closedBall_zero_iff]
      have := norm_sub_le (ω : E n) ((ω : E n) - η)
      rw [sub_sub_cancel] at this
      linarith
    simp only [indicator_of_mem hmem, hη]

lemma Top_L2 (hn : 2 ≤ n) (m : ℕ) (hm : 0 < m) (Cs : ℝ)
    (hdec : ∀ z : E n, 1 ≤ ‖z‖ → ‖sig n z‖ ^ m * ‖z‖ ≤ Cs) : ∃ C0 : ℕ, 3 * n + 3 ≤ C0 ∧ ∃ A2 : ℝ, 0 ≤ A2 ∧
    ∀ R : ℝ, 1 ≤ R → ∀ (N : ℕ) (x : Fin N → E n), IsSparse (C0 : ℝ) R x → ∀ G : Fin N → E n → ℂ, (∀ i, Integrable (G i)) →
      (∀ i, MemLp (G i) 2) →
      ∫⁻ ω, ‖Top n R x G ω‖ₑ ^ (2 : ℝ) ∂(sphereMeasure n) ≤
        ENNReal.ofReal (A2 * R) * ∑ i, ∫⁻ η, ‖G i η‖ₑ ^ (2 : ℝ) := by
  set V := (volume : Measure (E n)).real (closedBall 0 2)
  have hV : 0 ≤ V := measureReal_nonneg
  refine ⟨2 * n * m + 3 * n + 3, by omega, A1 n + Cst n Cs * V,
    by have := A1_nonneg n; have := Cst_nonneg n Cs; positivity, ?_⟩
  intro R hR N x hsp G hGi hGL2
  set G' : Fin N → E n → ℂ := fun i => (closedBall (0 : E n) 2).indicator
    ((hGi i).aestronglyMeasurable.mk (G i)) with hG'
  have hGs' : ∀ i, StronglyMeasurable (G' i) := fun i =>
    (hGi i).aestronglyMeasurable.stronglyMeasurable_mk.indicator measurableSet_closedBall
  have hGi' : ∀ i, Integrable (G' i) := fun i =>
    ((hGi i).congr (hGi i).aestronglyMeasurable.ae_eq_mk).indicator measurableSet_closedBall
  have hG'le : ∀ i, ∫⁻ η, ‖G' i η‖ₑ ^ 2 ≤ ∫⁻ η, ‖G i η‖ₑ ^ 2 := by
    intro i
    refine lintegral_mono_ae ?_
    filter_upwards [(hGi i).aestronglyMeasurable.ae_eq_mk] with η hη
    by_cases h : η ∈ closedBall (0 : E n) 2
    · simp only [G', indicator_of_mem h, ← hη, le_refl]
    · simp [G', indicator_of_notMem h]
  have hfin : ∀ i, ∫⁻ η, ‖G i η‖ₑ ^ 2 ≠ ⊤ := by
    intro i
    have := lintegral_rpow_enorm_lt_top_of_eLpNorm_lt_top two_ne_zero ENNReal.ofNat_ne_top
      (hGL2 i).eLpNorm_lt_top
    simp only [ENNReal.toReal_ofNat, ENNReal.rpow_two] at this
    exact this.ne
  have hL1 : ∀ i, (∫⁻ η, ‖G' i η‖ₑ) ^ 2 ≤ ENNReal.ofReal V * ∫⁻ η, ‖G' i η‖ₑ ^ 2 := by
    intro i
    refine l1_l2_ball (G' i) (hGs' i).measurable (fun η h => ?_)
    simp [G', indicator_of_notMem h]
  have hsp' : ∀ i j, i ≠ j → (R * N) ^ (2 * n * m + 3 * n + 3) ≤ ‖x i - x j‖ := by
    intro i j h
    have := hsp i j h
    rwa [Real.rpow_natCast, Real.rpow_natCast, ← mul_pow, dist_eq_norm] at this
  rw [Top_eq_restrict hR G hGi]
  simp only [ENNReal.rpow_two]
  refine (Top_L2_core (by omega) m hm Cs hdec hR V hV hsp' G' hGi' hGs'
    (fun i => ne_top_of_le_ne_top (hfin i) (hG'le i)) hL1).trans ?_
  exact mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun i _ => hG'le i)) (by positivity)

end TaoBR.RSU

end
end

section
section
/-!
# Auxiliary 1D estimate for the decay of `sig`
-/

open MeasureTheory Metric Set Filter Topology Complex
open Real (pi)
local notation "π" => Real.pi
open scoped FourierTransform ENNReal NNReal RealInnerProductSpace ComplexConjugate

namespace TaoBR.RSU.SigAux

noncomputable def bb : ContDiffBump (1 : ℝ) := ⟨1 / 4, 1 / 2, by norm_num, by norm_num⟩

noncomputable def bf (r : ℝ) : ℝ := bb r

lemma bf_nonneg (r : ℝ) : 0 ≤ bf r := bb.nonneg

lemma bf_le_one (r : ℝ) : bf r ≤ 1 := bb.le_one

lemma bf_one : bf 1 = 1 := bb.one_of_mem_closedBall (by simp [bb])

lemma bf_eq_zero {r : ℝ} (hr : 3 / 2 ≤ r) : bf r = 0 := by
  have : r ∉ Function.support bb := by
    rw [bb.support_eq]
    simp only [bb, mem_ball, Real.dist_eq, not_lt]
    rw [abs_of_nonneg (by linarith)]; linarith
  simpa [bf] using this

lemma bf_contDiff : ContDiff ℝ 1 bf := bb.contDiff

lemma bf_continuous : Continuous bf := bb.continuous

lemma bf_hasCompactSupport : HasCompactSupport bf := bb.hasCompactSupport

noncomputable def βf (r : ℝ) : ℝ := bf r * r ^ 3

lemma βf_contDiff : ContDiff ℝ 1 βf := bf_contDiff.mul (contDiff_id.pow 3)

lemma βf_hasCompactSupport : HasCompactSupport βf := bf_hasCompactSupport.mul_right

lemma deriv_βf_bound : ∃ M, 0 ≤ M ∧ ∀ r, |deriv βf r| ≤ M := by
  obtain ⟨C, hC⟩ := (βf_contDiff.continuous_deriv le_rfl).bounded_above_of_compact_support
    βf_hasCompactSupport.deriv
  exact ⟨max C 0, le_max_right _ _, fun r => by
    have := hC r; rw [Real.norm_eq_abs] at this; exact this.trans (le_max_left _ _)⟩

/-- The fibre integrand. -/
noncomputable def fib (lam q t : ℝ) : ℂ :=
  (𝐞 (-(lam * t) / √(t ^ 2 + q)) : ℂ) * (bf (√(t ^ 2 + q)) : ℂ)

lemma fib_eq_zero {lam q t : ℝ} (hq : 0 ≤ q) (ht : 2 < |t|) : fib lam q t = 0 := by
  have h4 : 4 < t ^ 2 := by rw [← sq_abs]; nlinarith [abs_nonneg t]
  have : 3 / 2 ≤ √(t ^ 2 + q) := by
    rw [show (3 / 2 : ℝ) = √((3 / 2) ^ 2) by rw [Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_le_sqrt (by nlinarith)
  simp [fib, bf_eq_zero this]

lemma norm_fib_le (lam q t : ℝ) : ‖fib lam q t‖ ≤ 1 := by
  rw [fib, norm_mul, Circle.norm_coe, one_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (bf_nonneg _)]
  exact bf_le_one _

lemma integral_fib_eq (lam : ℝ) {q : ℝ} (hq : 0 ≤ q) :
    ∫ t, fib lam q t = ∫ t in (-2 : ℝ)..2, fib lam q t := by
  rw [intervalIntegral.integral_of_le (by norm_num), ← integral_Icc_eq_integral_Ioc,
    setIntegral_eq_integral_of_forall_compl_eq_zero]
  intro t ht
  refine fib_eq_zero hq ?_
  by_contra h
  push Not at h
  exact ht (abs_le.mp h)

lemma norm_integral_fib_le_four (lam : ℝ) {q : ℝ} (hq : 0 ≤ q) :
    ‖∫ t, fib lam q t‖ ≤ 4 := by
  rw [integral_fib_eq lam hq]
  have := intervalIntegral.norm_integral_le_of_norm_le_const (a := -2) (b := 2) (C := 1)
    (f := fib lam q) (fun t _ => norm_fib_le lam q t)
  norm_num at this
  linarith

lemma norm_integral_fib_le {M : ℝ} (hM : ∀ r, |deriv βf r| ≤ M) {lam q : ℝ} (hlam : 0 < lam)
    (hq : 0 < q) : ‖∫ t, fib lam q t‖ ≤ 4 * M / (2 * π * lam * q) := by
  set r : ℝ → ℝ := fun t => √(t ^ 2 + q) with hr_def
  have hpos : ∀ t, 0 < t ^ 2 + q := fun t => by positivity
  have hr_pos : ∀ t, 0 < r t := fun t => Real.sqrt_pos.mpr (hpos t)
  have hr_sq : ∀ t, r t ^ 2 = t ^ 2 + q := fun t => Real.sq_sqrt (hpos t).le
  have hr_cont : Continuous r := by fun_prop
  have hr_der : ∀ t, HasDerivAt r (2 * t / (2 * r t)) t := fun t => by
    have hf : HasDerivAt (fun x => x ^ 2 + q) (2 * t) t := by
      simpa using (hasDerivAt_pow 2 t).add_const q
    exact hf.sqrt (hpos t).ne'
  set φ : ℝ → ℝ := fun t => -(lam * t) / r t with hφ_def
  set φ' : ℝ → ℝ := fun t => (-lam * r t - -(lam * t) * (2 * t / (2 * r t))) / r t ^ 2
    with hφ'_def
  have hφ : ∀ t, HasDerivAt φ (φ' t) t := fun t => by
    have h1 : HasDerivAt (fun t => -(lam * t)) (-lam) t := by
      have := ((hasDerivAt_id t).const_mul lam).neg
      simp only [id, mul_one] at this
      exact this
    exact h1.div (hr_der t) (hr_pos t).ne'
  set v : ℝ → ℂ := fun t => (𝐞 (φ t) : ℂ) with hv_def
  set v' : ℝ → ℂ := fun t => φ' t • (2 * π * I * 𝐞 (φ t)) with hv'_def
  have hv : ∀ t, HasDerivAt v (v' t) t := fun t =>
    (Real.hasDerivAt_fourierChar (φ t)).scomp t (hφ t)
  set u : ℝ → ℂ := fun t => ((βf (r t) / q : ℝ) : ℂ) with hu_def
  set u' : ℝ → ℂ := fun t => ((deriv βf (r t) * (2 * t / (2 * r t)) / q : ℝ) : ℂ) with hu'_def
  have hu : ∀ t, HasDerivAt u (u' t) t := fun t => by
    have hβ : HasDerivAt βf (deriv βf (r t)) (r t) :=
      ((βf_contDiff.differentiable one_ne_zero) (r t)).hasDerivAt
    exact ((hβ.comp t (hr_der t)).div_const q).ofReal_comp
  have hφ_cont : Continuous φ :=
    Continuous.div (by fun_prop) hr_cont (fun t => (hr_pos t).ne')
  have hφ'_cont : Continuous φ' := by
    refine Continuous.div ?_ (hr_cont.pow 2) (fun t => by have := hr_pos t; positivity)
    refine (continuous_const.mul hr_cont).sub (continuous_neg.comp (continuous_const.mul
      continuous_id) |>.mul ?_)
    exact Continuous.div (by fun_prop) (continuous_const.mul hr_cont)
      (fun t => by have := hr_pos t; positivity)
  have he_cont : Continuous fun t => (𝐞 (φ t) : ℂ) :=
    continuous_subtype_val.comp (Real.continuous_fourierChar.comp hφ_cont)
  have hv'_cont : Continuous v' :=
    (Complex.continuous_ofReal.comp hφ'_cont).smul (continuous_const.mul he_cont)
  have hu'_cont : Continuous u' := by
    refine Complex.continuous_ofReal.comp ?_
    refine Continuous.div_const (Continuous.mul ((βf_contDiff.continuous_deriv le_rfl).comp
      hr_cont) ?_) q
    exact Continuous.div (by fun_prop) (continuous_const.mul hr_cont)
      (fun t => by have := hr_pos t; positivity)
  have hibp := intervalIntegral.integral_mul_deriv_eq_deriv_mul (a := -2) (b := 2)
    (fun t _ => hu t) (fun t _ => hv t) (hu'_cont.intervalIntegrable _ _)
    (hv'_cont.intervalIntegrable _ _)
  have hr2 : ∀ t : ℝ, 2 ≤ |t| → 3 / 2 ≤ r t := fun t ht => by
    have h4 : 4 ≤ t ^ 2 := by rw [← sq_abs]; nlinarith [abs_nonneg t]
    rw [show (3 / 2 : ℝ) = √((3 / 2) ^ 2) by rw [Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_le_sqrt (by nlinarith)
  have hu2 : u 2 = 0 := by
    simp [hu_def, βf, bf_eq_zero (hr2 2 (by norm_num))]
  have hum2 : u (-2) = 0 := by
    simp [hu_def, βf, bf_eq_zero (hr2 (-2) (by norm_num))]
  rw [hu2, hum2, zero_mul, zero_mul, sub_zero, zero_sub] at hibp
  -- pointwise identity
  have hkey : ∀ t, u t * v' t = (-(2 * π * I * lam)) * fib lam q t := fun t => by
    have hreal : βf (r t) / q * φ' t = -lam * bf (r t) := by
      have h1 := hr_pos t
      have h2 := hr_sq t
      simp only [hφ'_def, βf]
      field_simp
      linear_combination (-bf (r t)) * h2
    simp only [hu_def, hv'_def, fib, Complex.real_smul]
    have : (((βf (r t) / q : ℝ) : ℂ) * (φ' t : ℂ)) = ((-lam * bf (r t) : ℝ) : ℂ) := by
      rw [← hreal]; push_cast; ring
    calc ((βf (r t) / q : ℝ) : ℂ) * ((φ' t : ℂ) * (2 * π * I * 𝐞 (φ t)))
        = ((βf (r t) / q : ℝ) : ℂ) * (φ' t : ℂ) * (2 * π * I * 𝐞 (φ t)) := by ring
      _ = _ := by rw [this]; push_cast; simp only [hφ_def, hr_def]; ring
  have hc : (-(2 * π * I * lam) : ℂ) ≠ 0 := by
    have : (2 * π * lam : ℂ) ≠ 0 := by exact_mod_cast (by positivity : (2 * π * lam : ℝ) ≠ 0)
    intro h; apply this; linear_combination I * h + (2 * π * lam : ℂ) * Complex.I_sq
  have hint : ∫ t in (-2 : ℝ)..2, fib lam q t =
      (-(2 * π * I * lam))⁻¹ * ∫ t in (-2 : ℝ)..2, u t * v' t := by
    rw [← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr (fun t _ => ?_)
    rw [hkey t, ← mul_assoc, inv_mul_cancel₀ hc, one_mul]
  rw [integral_fib_eq lam hq.le, hint, hibp, norm_mul, norm_inv, norm_neg]
  have hn : ‖(2 * π * I * lam : ℂ)‖ = 2 * π * lam := by
    rw [norm_mul, norm_mul, norm_mul, Complex.norm_I, Complex.norm_real, Complex.norm_ofNat,
      Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos Real.pi_pos,
      abs_of_pos hlam]; ring
  rw [hn, norm_neg]
  have hbound : ‖∫ t in (-2 : ℝ)..2, u' t * v t‖ ≤ M / q * |2 - -2| := by
    refine intervalIntegral.norm_integral_le_of_norm_le_const (fun t _ => ?_)
    rw [norm_mul, hv_def]
    simp only [Circle.norm_coe, mul_one, hu'_def, Complex.norm_real, Real.norm_eq_abs]
    rw [abs_div, abs_mul, abs_of_pos hq]
    gcongr
    have hle : |2 * t / (2 * r t)| ≤ 1 := by
      rw [abs_div, abs_of_pos (mul_pos two_pos (hr_pos t)), div_le_one
        (mul_pos two_pos (hr_pos t)), abs_mul, abs_two]
      have : |t| ≤ r t := Real.abs_le_sqrt (by nlinarith)
      linarith
    calc |deriv βf (r t)| * |2 * t / (2 * r t)| ≤ M * 1 :=
          mul_le_mul (hM _) hle (abs_nonneg _) ((abs_nonneg _).trans (hM 0))
      _ = M := mul_one M
  have hpi : 0 < 2 * π * lam := by positivity
  calc (2 * π * lam)⁻¹ * ‖∫ t in (-2 : ℝ)..2, u' t * v t‖
      ≤ (2 * π * lam)⁻¹ * (M / q * |2 - -2|) := by gcongr
    _ = 4 * M / (2 * π * lam * q) := by
        norm_num; field_simp

end TaoBR.RSU.SigAux

end
end

section
section
/-!
# Decay of the Fourier transform of surface measure
-/

open MeasureTheory Metric Set Filter Topology
open scoped FourierTransform ENNReal NNReal SchwartzMap RealInnerProductSpace ComplexConjugate
  Pointwise

local notation "π" => Real.pi

namespace TaoBR.RSU

namespace SigAux

/-- The rotated integrand on `E (k+1)`. -/
noncomputable def Gr {k : ℕ} (lam : ℝ) (x : E (k + 1)) : ℂ :=
  (𝐞 (-(lam * x 0) / ‖x‖) : ℂ) * (bf ‖x‖ : ℂ)

/-- The polar integrand. -/
noncomputable def Fz {n : ℕ} (z : E n) (x : E n) : ℂ :=
  (𝐞 (-⟪x, z⟫ / ‖x‖) : ℂ) * (bf ‖x‖ : ℂ)

lemma fib_eq_zero_of {lam q t : ℝ} (h : 9 / 4 ≤ t ^ 2 + q) : fib lam q t = 0 := by
  have : 3 / 2 ≤ √(t ^ 2 + q) := by
    rw [show (3 / 2 : ℝ) = √((3 / 2) ^ 2) by rw [Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_le_sqrt (by linarith)
  simp [fib, bf_eq_zero this]

lemma integral_Gr_eq (k : ℕ) (lam : ℝ) :
    ∫ x : E (k + 1), Gr lam x = ∫ w : ℝ × (Fin k → ℝ), fib lam (∑ j, w.2 j ^ 2) w.1 := by
  set H : (Fin (k + 1) → ℝ) → ℂ := fun p =>
    (𝐞 (-(lam * p 0) / √(∑ i, p i ^ 2)) : ℂ) * (bf (√(∑ i, p i ^ 2)) : ℂ) with hH
  have h0 := EuclideanSpace.volume_preserving_symm_measurableEquiv_toLp (Fin (k + 1))
  have e1 : ∀ x : E (k + 1), Gr lam x = H ((MeasurableEquiv.toLp 2 (Fin (k + 1) → ℝ)).symm x) := by
    intro x
    have hx : ‖x‖ = √(∑ i, x i ^ 2) := by
      rw [EuclideanSpace.norm_eq]; simp [Real.norm_eq_abs, sq_abs]
    simp only [Gr, hH, hx]
    rfl
  simp_rw [e1]
  rw [h0.integral_comp' H]
  have h1 := (volume_preserving_piFinSuccAbove (fun _ : Fin (k + 1) => ℝ) 0).symm
  rw [← h1.integral_comp' H]
  congr 1; ext w
  simp [hH, fib, MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv,
    Fin.insertNth_zero', Fin.sum_univ_succ]

lemma sq_gt_of_not_mem {k : ℕ} {a : ℝ} (ha : 0 ≤ a) {y : Fin k → ℝ}
    (h : y ∉ Icc (fun _ => -a) (fun _ => a)) : a ^ 2 < ∑ j, y j ^ 2 := by
  simp only [mem_Icc, Pi.le_def, not_and_or, not_forall, not_le] at h
  have hsum : ∀ j, y j ^ 2 ≤ ∑ j, y j ^ 2 := fun j =>
    Finset.single_le_sum (f := fun j => y j ^ 2) (fun j _ => sq_nonneg _) (Finset.mem_univ j)
  rcases h with ⟨j, hj⟩ | ⟨j, hj⟩
  · have := hsum j; nlinarith
  · have := hsum j; nlinarith

lemma integrable_fib (k : ℕ) (lam : ℝ) :
    Integrable (fun w : ℝ × (Fin k → ℝ) => fib lam (∑ j, w.2 j ^ 2) w.1) := by
  set S : Set (ℝ × (Fin k → ℝ)) := Icc (-2 : ℝ) 2 ×ˢ Icc (fun _ => -2) (fun _ => 2) with hS_def
  have hS : IsCompact S := isCompact_Icc.prod isCompact_Icc
  have hg : Integrable (S.indicator fun _ => (1 : ℝ)) :=
    (integrableOn_const hS.measure_lt_top.ne).integrable_indicator hS.measurableSet
  refine hg.mono' ?_ (Eventually.of_forall fun w => ?_)
  · have h2 : Continuous fun w : ℝ × (Fin k → ℝ) => √(w.1 ^ 2 + ∑ j, w.2 j ^ 2) := by fun_prop
    have h1 : Measurable fun w : ℝ × (Fin k → ℝ) =>
        -(lam * w.1) / √(w.1 ^ 2 + ∑ j, w.2 j ^ 2) := by
      exact (measurable_const.mul measurable_fst).neg.div h2.measurable
    simp only [fib]
    exact (((continuous_subtype_val.comp Real.continuous_fourierChar).measurable.comp h1).mul
      (Complex.continuous_ofReal.comp (bf_continuous.comp h2)).measurable).aestronglyMeasurable
  · by_cases hw : w ∈ S
    · rw [indicator_of_mem hw]; exact norm_fib_le _ _ _
    · rw [indicator_of_notMem hw, fib_eq_zero_of ?_, norm_zero]
      have hq : 0 ≤ ∑ j, w.2 j ^ 2 := Finset.sum_nonneg (fun j _ => sq_nonneg _)
      rw [hS_def, mem_prod, not_and_or] at hw
      rcases hw with hw | hw
      · rw [mem_Icc, ← abs_le, not_le] at hw
        nlinarith [abs_nonneg w.1, sq_abs w.1]
      · have := sq_gt_of_not_mem (by norm_num) hw
        nlinarith [sq_nonneg w.1]

lemma vol_cube (k : ℕ) {a : ℝ} (ha : 0 ≤ a) :
    (volume : Measure (Fin k → ℝ)).real (Icc (fun _ => -a) (fun _ => a)) = (2 * a) ^ k := by
  rw [measureReal_def, Real.volume_Icc_pi, ENNReal.toReal_prod]
  simp only [ENNReal.toReal_ofReal (by linarith : (0 : ℝ) ≤ a - -a), Finset.prod_const,
    Finset.card_univ, Fintype.card_fin]
  ring

lemma norm_integral_fib_prod_le (k : ℕ) (hk : 1 ≤ k) : ∃ D, 0 ≤ D ∧ ∀ lam : ℝ, 0 < lam →
    ∀ ε : ℝ, 0 < ε → ε ≤ 1 →
    ‖∫ w : ℝ × (Fin k → ℝ), fib lam (∑ j, w.2 j ^ 2) w.1‖ ≤ D * (ε + 1 / (lam * ε ^ 2)) := by
  obtain ⟨M, hM0, hM⟩ := deriv_βf_bound
  refine ⟨4 * 2 ^ k + 4 ^ k * (4 * M / (2 * π)), by positivity, fun lam hlam ε hε hε1 => ?_⟩
  rw [Measure.volume_eq_prod, integral_prod_symm _ (integrable_fib k lam)]
  set K := 4 * M / (2 * π * lam * ε ^ 2) with hK
  have hK0 : 0 ≤ K := by positivity
  set C1 : Set (Fin k → ℝ) := Icc (fun _ => -ε) (fun _ => ε) with hC1
  set C2 : Set (Fin k → ℝ) := Icc (fun _ => -2) (fun _ => 2) with hC2
  have hbd : ∀ y : Fin k → ℝ, ‖∫ t, fib lam (∑ j, y j ^ 2) t‖ ≤
      C1.indicator (fun _ => (4 : ℝ)) y + C2.indicator (fun _ => K) y := by
    intro y
    have hq0 : 0 ≤ ∑ j, y j ^ 2 := Finset.sum_nonneg (fun j _ => sq_nonneg _)
    have hi2 : 0 ≤ C2.indicator (fun _ => K) y := indicator_nonneg (fun _ _ => hK0) _
    by_cases h1 : y ∈ C1
    · rw [indicator_of_mem h1]
      have := norm_integral_fib_le_four lam hq0
      linarith
    · have hq1 := sq_gt_of_not_mem hε.le h1
      rw [indicator_of_notMem h1, zero_add]
      by_cases h2 : y ∈ C2
      · rw [indicator_of_mem h2]
        have hqpos : 0 < ∑ j, y j ^ 2 := lt_of_le_of_lt (sq_nonneg ε) hq1
        refine (norm_integral_fib_le hM hlam hqpos).trans ?_
        rw [hK]
        gcongr
      · have hq2 := sq_gt_of_not_mem (by norm_num) h2
        have : ∀ t, fib lam (∑ j, y j ^ 2) t = 0 := fun t =>
          fib_eq_zero_of (by nlinarith [sq_nonneg t])
        simp only [this, integral_zero, norm_zero]
        exact hi2
  have hint : Integrable (fun y => C1.indicator (fun _ => (4 : ℝ)) y +
      C2.indicator (fun _ => K) y) :=
    ((integrableOn_const isCompact_Icc.measure_lt_top.ne).integrable_indicator
      measurableSet_Icc).add
      ((integrableOn_const isCompact_Icc.measure_lt_top.ne).integrable_indicator
        measurableSet_Icc)
  have hval : ∫ y, (C1.indicator (fun _ => (4 : ℝ)) y + C2.indicator (fun _ => K) y) =
      (2 * ε) ^ k * 4 + (2 * 2) ^ k * K := by
    rw [integral_add, integral_indicator_const _ measurableSet_Icc,
      integral_indicator_const _ measurableSet_Icc, vol_cube k hε.le, vol_cube k (by norm_num)]
    · simp [smul_eq_mul]
    · exact (integrableOn_const isCompact_Icc.measure_lt_top.ne).integrable_indicator
        measurableSet_Icc
    · exact (integrableOn_const isCompact_Icc.measure_lt_top.ne).integrable_indicator
        measurableSet_Icc
  have hεk : ε ^ k ≤ ε := pow_le_of_le_one hε.le hε1 (by omega)
  dsimp only
  refine (norm_integral_le_integral_norm _).trans ?_
  refine (integral_mono_of_nonneg (Eventually.of_forall fun _ => norm_nonneg _) hint
    (Eventually.of_forall hbd)).trans ?_
  rw [hval]
  have hX : 0 ≤ 1 / (lam * ε ^ 2) := by positivity
  have hKe : K = 4 * M / (2 * π) * (1 / (lam * ε ^ 2)) := by
    rw [hK]; field_simp
  rw [hKe, mul_pow, show (2 * 2 : ℝ) = 4 by norm_num]
  have h2k : (0 : ℝ) ≤ 2 ^ k := by positivity
  have hc : 0 ≤ 4 ^ k * (4 * M / (2 * π)) := by positivity
  nlinarith [mul_le_mul_of_nonneg_left hεk h2k]

end SigAux

open SigAux

lemma sig_decay (n : ℕ) (hn : 2 ≤ n) : ∃ m : ℕ, 0 < m ∧ ∃ C : ℝ, 0 ≤ C ∧
    ∀ z : E n, 1 ≤ ‖z‖ → ‖sig n z‖ ^ m * ‖z‖ ≤ C := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  have hk : 1 ≤ k := by omega
  obtain ⟨D, hD0, hD⟩ := norm_integral_fib_prod_le k hk
  set cb : ℂ := ∫ r : Ioi (0 : ℝ), (bf r : ℂ) ∂(Measure.volumeIoiPow (k + 1 - 1)) with hcb_def
  have hpolar : ∀ z : E (k + 1), ∫ x, Fz z x = sig (k + 1) z * cb := by
    intro z
    have key := polar_prod_integral (n := k + 1) (by omega)
      (fun ω => (𝐞 (-⟪(ω : E (k + 1)), z⟫) : ℂ)) (fun r => (bf r : ℂ)) (Fz z) ?_
    · rw [key]; rfl
    intro ω r hr
    have hω : ‖(ω : E (k + 1))‖ = 1 := by simp
    have hn' : ‖r • (ω : E (k + 1))‖ = r := by
      rw [norm_smul, hω, mul_one, Real.norm_eq_abs, abs_of_pos hr]
    have he : -(r * ⟪(ω : E (k + 1)), z⟫) / r = -⟪(ω : E (k + 1)), z⟫ := by
      field_simp
    simp only [Fz, hn', real_inner_smul_left, he]
  have hcb : cb ≠ 0 := by
    intro h0
    have h := hpolar 0
    rw [h0, mul_zero] at h
    have hF0 : ∀ x : E (k + 1), Fz 0 x = ((bf ‖x‖ : ℝ) : ℂ) := fun x => by simp [Fz]
    simp_rw [hF0] at h
    rw [integral_complex_ofReal] at h
    have hcs : HasCompactSupport (fun x : E (k + 1) => bf ‖x‖) := by
      refine HasCompactSupport.intro (isCompact_closedBall (0 : E (k + 1)) (3 / 2))
        (fun x hx => bf_eq_zero ?_)
      simp only [mem_closedBall, dist_zero_right, not_le] at hx
      exact hx.le
    have hpos : 0 < ∫ x : E (k + 1), bf ‖x‖ :=
      Continuous.integral_pos_of_hasCompactSupport_nonneg_nonzero
        (x := EuclideanSpace.single 0 1) (bf_continuous.comp continuous_norm) hcs
        (fun x => bf_nonneg _) (by simp [bf_one])
    exact hpos.ne' (by exact_mod_cast h)
  have hrot : ∀ z : E (k + 1), ∫ x, Fz z x = ∫ x, Gr (k := k) ‖z‖ x := by
    intro z
    set w : E (k + 1) := EuclideanSpace.single 0 ‖z‖ with hw_def
    have hw : ‖z‖ = ‖w‖ := by simp [w]
    set Q := Submodule.reflection (ℝ ∙ (z - w))ᗮ with hQ_def
    have hQ : Q z = w := Submodule.reflection_sub hw
    have hmp := Q.symm.measurePreserving
    rw [← hmp.integral_comp Q.symm.toHomeomorph.measurableEmbedding (Fz z)]
    congr 1; ext x
    have h1 : ‖Q.symm x‖ = ‖x‖ := Q.symm.norm_map x
    have h2 : ⟪Q.symm x, z⟫ = ‖z‖ * x 0 := by
      rw [← Q.inner_map_map, Q.apply_symm_apply, hQ, hw_def,
        EuclideanSpace.inner_single_right]
      simp
    simp only [Fz, Gr, h1, h2]
  set Sg := (sphereMeasure (k + 1)).real univ with hSg
  set D' := max (D / ‖cb‖) (max Sg 1) with hD'
  have hcbn : 0 < ‖cb‖ := norm_pos_iff.mpr hcb
  have hD'1 : 1 ≤ D' := le_trans (le_max_right _ _) (le_max_right _ _)
  have hD'S : Sg ≤ D' := le_trans (le_max_left _ _) (le_max_right _ _)
  have hD'D : D / ‖cb‖ ≤ D' := le_max_left _ _
  refine ⟨3, by norm_num, 8 * D' ^ 3, by positivity, fun z hz => ?_⟩
  set lam := ‖z‖ with hlam
  have hlam0 : 0 < lam := by linarith
  have hmain : ∀ ε : ℝ, 0 < ε → ε ≤ 1 → ‖sig (k + 1) z‖ ≤ D' * (ε + 1 / (lam * ε ^ 2)) := by
    intro ε hε hε1
    have h := hD lam hlam0 ε hε hε1
    rw [← integral_Gr_eq, ← hrot, hpolar, norm_mul] at h
    have hX : 0 ≤ ε + 1 / (lam * ε ^ 2) := by positivity
    calc ‖sig (k + 1) z‖ ≤ D / ‖cb‖ * (ε + 1 / (lam * ε ^ 2)) := by
          rw [div_mul_eq_mul_div, le_div_iff₀ hcbn]; linarith
      _ ≤ D' * (ε + 1 / (lam * ε ^ 2)) := by gcongr
  set S0 := ‖sig (k + 1) z‖ with hS0
  have hS0le : S0 ≤ Sg := sig_norm_le _ _
  rcases (norm_nonneg (sig (k + 1) z)).eq_or_lt with h0 | h0
  · rw [← hS0] at h0
    rw [← h0]; simp; positivity
  · have hD'pos : 0 < D' := by linarith
    set ε := S0 / (2 * D') with hε
    have hεpos : 0 < ε := by positivity
    have hε1 : ε ≤ 1 := by
      rw [hε, div_le_one (by positivity)]; linarith
    have h := hmain ε hεpos hε1
    have h' : S0 / 2 ≤ D' * (1 / (lam * ε ^ 2)) := by
      have : D' * ε = S0 / 2 := by rw [hε]; field_simp
      nlinarith
    rw [mul_one_div, le_div_iff₀ (by positivity), hε] at h'
    have : S0 ^ 3 * lam = 8 * D' ^ 2 * (S0 / 2 * (lam * (S0 / (2 * D')) ^ 2)) := by
      field_simp; ring
    rw [this]
    calc 8 * D' ^ 2 * (S0 / 2 * (lam * (S0 / (2 * D')) ^ 2)) ≤ 8 * D' ^ 2 * D' := by gcongr
      _ = 8 * D' ^ 3 := by ring

end TaoBR.RSU

end
end

section
section
/-!
# Estimate (2): the restriction hypothesis averaged over the annulus
-/

open MeasureTheory Metric Set Filter Topology
open scoped FourierTransform ENNReal NNReal SchwartzMap RealInnerProductSpace ComplexConjugate
  Pointwise

namespace TaoBR.RSU

/-- The annulus `|‖η‖ - 1| < 1/(16R)`. -/
def Ann (n : ℕ) (R : ℝ) : Set (E n) := {η | 1 - 1 / (16 * R) < ‖η‖ ∧ ‖η‖ < 1 + 1 / (16 * R)}

/-- The affine map `y ↦ r⁻¹ • y + c`. -/
noncomputable def affE {n : ℕ} (r : ℝ) (c : E n) (y : E n) : E n := r⁻¹ • y + c

lemma affE_temperate {n : ℕ} (r : ℝ) (c : E n) : (affE r c).HasTemperateGrowth := by
  have h1 : (fun y : E n => r⁻¹ • y).HasTemperateGrowth :=
    (r⁻¹ • ContinuousLinearMap.id ℝ (E n)).hasTemperateGrowth
  exact h1.add (Function.HasTemperateGrowth.const c)

lemma affE_upper {n : ℕ} {r : ℝ} (hr : 0 < r) (c : E n) :
    ∃ (k : ℕ) (C : ℝ), ∀ x, ‖x‖ ≤ C * (1 + ‖affE r c x‖) ^ k := by
  refine ⟨1, r * (1 + ‖c‖), fun x => ?_⟩
  have hx : x = r • (affE r c x - c) := by
    simp only [affE, add_sub_cancel_right, smul_smul, mul_inv_cancel₀ hr.ne', one_smul]
  have h2 : ‖x‖ ≤ r * (‖affE r c x‖ + ‖c‖) := by
    conv_lhs => rw [hx]
    rw [norm_smul, Real.norm_of_nonneg hr.le]
    gcongr
    exact norm_sub_le _ _
  calc ‖x‖ ≤ r * (‖affE r c x‖ + ‖c‖) := h2
    _ ≤ r * (1 + ‖c‖) * (1 + ‖affE r c x‖) ^ 1 := by
      rw [pow_one]
      have := mul_nonneg hr.le (mul_nonneg (norm_nonneg (affE r c x)) (norm_nonneg c))
      nlinarith

/-- `h ∘ affE r c` as a Schwartz map. -/
noncomputable def hAff {n : ℕ} (h : 𝓢(E n, ℂ)) {r : ℝ} (hr : 0 < r) (c : E n) : 𝓢(E n, ℂ) :=
  SchwartzMap.compCLM ℂ (affE_temperate r c) (affE_upper hr c) h

lemma fourier_hAff {n : ℕ} (h : E n → ℂ) {r : ℝ} (hr : 0 < r) (c ω : E n) :
    ‖𝓕 (fun y => h (r⁻¹ • y + c)) ω‖ = r ^ n * ‖𝓕 h (r • ω)‖ := by
  set G : E n → ℂ := fun x => 𝐞 (-⟪r • (x - c), ω⟫) • h x with hG
  have h1 : 𝓕 (fun y => h (r⁻¹ • y + c)) ω = ∫ y, G (r⁻¹ • y + c) := by
    rw [Real.fourier_eq]
    congr 1; ext y
    simp only [hG, add_sub_cancel_right, smul_smul, mul_inv_cancel₀ hr.ne', one_smul]
  have h2 : ∫ y, G (r⁻¹ • y + c) = r ^ n • ∫ x, G x := by
    rw [Measure.integral_comp_inv_smul_of_nonneg volume (fun x => G (x + c)) hr.le,
      integral_add_right_eq_self (fun x => G x) c, finrank_euclideanSpace_fin]
  have h3 : ∫ x, G x = 𝐞 (⟪r • c, ω⟫) • 𝓕 h (r • ω) := by
    rw [Real.fourier_eq, Circle.smul_def, smul_eq_mul, ← integral_const_mul]
    congr 1; ext x
    have e : -⟪r • (x - c), ω⟫ = ⟪r • c, ω⟫ + -⟪x, r • ω⟫ := by
      simp only [inner_smul_left, inner_smul_right, inner_sub_left, RCLike.conj_to_real]; ring
    simp only [hG, Circle.smul_def, smul_eq_mul, e, AddChar.map_add_eq_mul, Circle.coe_mul, mul_assoc]
  rw [h1, h2, h3, norm_smul, Circle.norm_smul (𝐞 _) , Real.norm_of_nonneg (by positivity)]

lemma lint_scale {n : ℕ} (F : E n → ℝ≥0∞) (hF : Measurable F) {r : ℝ} (hr : 0 < r) (c : E n) :
    ∫⁻ y, F (r⁻¹ • y + c) = ENNReal.ofReal (r ^ n) * ∫⁻ x, F x := by
  have hm : Measurable (fun y : E n => r⁻¹ • y) := measurable_const_smul _
  have hF' : Measurable (fun x : E n => F (x + c)) := hF.comp (measurable_add_const c)
  have := lintegral_map hF' hm (μ := (volume : Measure (E n)))
  rw [Measure.map_addHaar_smul volume (inv_ne_zero hr.ne'), lintegral_smul_measure,
    lintegral_add_right_eq_self F c, finrank_euclideanSpace_fin] at this
  rw [← this, inv_pow, inv_inv, abs_of_pos (by positivity), smul_eq_mul]

lemma tsupport_hAff {n : ℕ} (h : 𝓢(E n, ℂ)) {r : ℝ} (hr : 0 < r) {c : E n} {R : ℝ}
    (hsupp : tsupport h ⊆ closedBall c R) :
    tsupport (hAff h hr c) ⊆ closedBall 0 (r * R) := by
  have hcont : Continuous (affE (n := n) r c) := by unfold affE; fun_prop
  have hcl : IsClosed (affE r c ⁻¹' tsupport h) := (isClosed_tsupport _).preimage hcont
  have h1 : tsupport (hAff h hr c) ⊆ affE r c ⁻¹' tsupport h := by
    refine closure_minimal (fun y hy => ?_) hcl
    exact subset_tsupport _ hy
  refine h1.trans (fun y hy => ?_)
  have := hsupp hy
  rw [mem_closedBall, dist_eq_norm, affE, add_sub_cancel_right, norm_smul,
    Real.norm_of_nonneg (inv_nonneg.mpr hr.le)] at this
  rw [mem_closedBall, dist_zero_right]
  have := mul_le_mul_of_nonneg_left this hr.le
  rwa [← mul_assoc, mul_inv_cancel₀ hr.ne', one_mul] at this

lemma lp_pow {α : Type*} [MeasurableSpace α] {μ : Measure α} {q : ℝ} (hq : 1 ≤ q)
    (f : α → ℂ) :
    eLpNorm f (ENNReal.ofReal q) μ ^ q = ∫⁻ x, ‖f x‖ₑ ^ q ∂μ := by
  have hq0 : (0 : ℝ) < q := by linarith
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by simpa using hq0) ENNReal.ofReal_ne_top,
    ENNReal.toReal_ofReal hq0.le, ← ENNReal.rpow_mul, one_div, inv_mul_cancel₀ hq0.ne',
    ENNReal.rpow_one]

lemma per_r (n : ℕ) {q : ℝ} (hq : 1 ≤ q) {α : ℝ} (Cr : ℝ≥0)
    (hCr : ∀ R : ℝ, 1 ≤ R → ∀ f : 𝓢(E n, ℂ), tsupport f ⊆ closedBall 0 R →
      eLpNorm (restriction f) (ENNReal.ofReal q) (sphereMeasure n) ≤
        Cr * ENNReal.ofReal (R ^ α) *
          eLpNorm f (ENNReal.ofReal q) (volume.restrict (closedBall 0 R)))
    {R : ℝ} (hR : 1 ≤ R) (c : E n) (h : 𝓢(E n, ℂ)) (hsupp : tsupport h ⊆ closedBall c R)
    {r : ℝ} (hr1 : 1 / 2 < r) (hr2 : r ≤ 2) :
    ∫⁻ ω, ‖𝓕 (h : E n → ℂ) (r • (ω : E n))‖ₑ ^ q ∂(sphereMeasure n) ≤
      ENNReal.ofReal (2 ^ ((n : ℝ) * q)) *
        ((Cr * ENNReal.ofReal ((2 * R) ^ α)) ^ q * ∫⁻ y, ‖h y‖ₑ ^ q) := by
  have hr : 0 < r := by linarith
  have hq0 : (0 : ℝ) ≤ q := by linarith
  set g := hAff h hr c
  have hg : tsupport g ⊆ closedBall 0 (2 * R) :=
    (tsupport_hAff h hr hsupp).trans (closedBall_subset_closedBall (by nlinarith))
  have key := hCr (2 * R) (by linarith) g hg
  have key2 := ENNReal.rpow_le_rpow key hq0
  rw [ENNReal.mul_rpow_of_nonneg _ _ hq0, lp_pow hq, lp_pow hq] at key2
  -- left side
  have hA : ∫⁻ ω, ‖restriction (g : E n → ℂ) ω‖ₑ ^ q ∂(sphereMeasure n) =
      ENNReal.ofReal (r ^ n) ^ q *
        ∫⁻ ω, ‖𝓕 (h : E n → ℂ) (r • (ω : E n))‖ₑ ^ q ∂(sphereMeasure n) := by
    rw [← lintegral_const_mul' _ _ (ENNReal.rpow_ne_top_of_nonneg hq0 ENNReal.ofReal_ne_top)]
    congr 1; ext ω
    have e := fourier_hAff (h : E n → ℂ) hr c (ω : E n)
    have : ‖restriction (g : E n → ℂ) ω‖ₑ = ENNReal.ofReal (r ^ n) * ‖𝓕 (h : E n → ℂ) (r • (ω : E n))‖ₑ := by
      rw [← ofReal_norm, ← ofReal_norm, ← ENNReal.ofReal_mul (by positivity)]
      exact congrArg ENNReal.ofReal e
    rw [this, ENNReal.mul_rpow_of_nonneg _ _ hq0]
  -- right side
  have hB : ∫⁻ y, ‖g y‖ₑ ^ q ∂(volume.restrict (closedBall 0 (2 * R))) ≤
      ENNReal.ofReal (r ^ n) * ∫⁻ y, ‖h y‖ₑ ^ q := by
    refine (lintegral_mono' Measure.restrict_le_self le_rfl).trans (le_of_eq ?_)
    exact lint_scale (fun x => ‖h x‖ₑ ^ q)
      (h.continuous.measurable.enorm.pow_const q) hr c
  rw [hA] at key2
  have key3 := key2.trans (mul_le_mul' le_rfl hB)
  set X := ∫⁻ ω, ‖𝓕 (h : E n → ℂ) (r • (ω : E n))‖ₑ ^ q ∂(sphereMeasure n)
  set H := ∫⁻ y, ‖h y‖ₑ ^ q
  set K := (Cr * ENNReal.ofReal ((2 * R) ^ α)) ^ q
  have hrn0 : ENNReal.ofReal (r ^ n) ^ q ≠ 0 := by
    have : 0 < r ^ n := by positivity
    exact (ENNReal.rpow_pos (by simpa using this) (by simp)).ne'
  have hrnT : ENNReal.ofReal (r ^ n) ^ q ≠ ⊤ := ENNReal.rpow_ne_top_of_nonneg hq0 (by simp)
  have hreal : r ^ n ≤ (r ^ n) ^ q * 2 ^ ((n : ℝ) * q) := by
    rw [Real.rpow_mul (by norm_num), Real.rpow_natCast, ← Real.mul_rpow (by positivity)
      (by positivity), ← mul_pow]
    have h1 : 1 ≤ (r * 2) ^ n := one_le_pow₀ (by linarith)
    calc r ^ n ≤ (r * 2) ^ n := pow_le_pow_left₀ hr.le (by linarith) n
      _ ≤ ((r * 2) ^ n) ^ q := Real.self_le_rpow_of_one_le h1 hq
  have hE : ENNReal.ofReal (r ^ n) ≤ ENNReal.ofReal (r ^ n) ^ q * ENNReal.ofReal (2 ^ ((n : ℝ) * q)) := by
    rw [ENNReal.ofReal_rpow_of_nonneg (by positivity) hq0, ← ENNReal.ofReal_mul (by positivity)]
    exact ENNReal.ofReal_le_ofReal hreal
  refine (ENNReal.mul_le_mul_iff_right hrn0 hrnT).mp ?_
  calc ENNReal.ofReal (r ^ n) ^ q * X ≤ K * (ENNReal.ofReal (r ^ n) * H) := key3
    _ ≤ K * (ENNReal.ofReal (r ^ n) ^ q * ENNReal.ofReal (2 ^ ((n : ℝ) * q)) * H) := by gcongr
    _ = _ := by ring

lemma est2 (n : ℕ) (hn : 2 ≤ n) {q : ℝ} (hq : 1 ≤ q) {α : ℝ} (hα : 0 ≤ α) (Cr : ℝ≥0)
    (hCr : ∀ R : ℝ, 1 ≤ R → ∀ f : 𝓢(E n, ℂ), tsupport f ⊆ closedBall 0 R →
      eLpNorm (restriction f) (ENNReal.ofReal q) (sphereMeasure n) ≤
        Cr * ENNReal.ofReal (R ^ α) *
          eLpNorm f (ENNReal.ofReal q) (volume.restrict (closedBall 0 R))) :
    ∃ C2 : ℝ≥0, ∀ R : ℝ, 1 ≤ R → ∀ (c : E n) (h : 𝓢(E n, ℂ)), tsupport h ⊆ closedBall c R →
      ∫⁻ η in Ann n R, ‖𝓕 (h : E n → ℂ) η‖ₑ ^ q ≤
        C2 * ENNReal.ofReal (R ^ α) ^ q * ENNReal.ofReal (1 / R) * ∫⁻ y, ‖h y‖ₑ ^ q := by
  have hn1 : 1 ≤ n := by omega
  have hq0 : (0 : ℝ) ≤ q := by linarith
  refine ⟨Real.toNNReal (2 ^ (n - 1) * 2 ^ ((n : ℝ) * q) * (2 ^ α) ^ q) * Cr ^ q, ?_⟩
  intro R hR c h hsupp
  set δ : ℝ := 1 / (16 * R) with hδdef
  have hδ0 : 0 < δ := by positivity
  have hδ : δ ≤ 1 / 16 := by
    rw [hδdef]; exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) (by linarith)
  set F : E n → ℝ≥0∞ := fun η => ‖𝓕 (h : E n → ℂ) η‖ₑ ^ q with hFdef
  have hFc : Continuous (𝓕 (h : E n → ℂ)) := by
    rw [← SchwartzMap.fourier_coe]; exact (𝓕 h).continuous
  have hFm : Measurable F := hFc.measurable.enorm.pow_const q
  have hAnn : MeasurableSet (Ann n R) :=
    (measurableSet_lt measurable_const measurable_norm).inter
      (measurableSet_lt measurable_norm measurable_const)
  set H := ∫⁻ y, ‖h y‖ₑ ^ q
  set K := (Cr * ENNReal.ofReal ((2 * R) ^ α)) ^ q
  set C : ℝ≥0∞ := ENNReal.ofReal (2 ^ (n - 1))
  set M : ℝ≥0∞ := ENNReal.ofReal (2 ^ ((n : ℝ) * q)) * (K * H)
  set I : Set ℝ := Ioo (1 - δ) (1 + δ)
  have step1 : ∫⁻ η in Ann n R, F η ≤ ∫⁻ ω, (∫⁻ r in Ioi (0 : ℝ),
      I.indicator (fun r => C * F (r • (ω : E n))) r) ∂(sphereMeasure n) := by
    rw [← lintegral_indicator hAnn, polar_lintegral hn1 _ (hFm.indicator hAnn)]
    refine lintegral_mono fun ω => setLIntegral_mono' measurableSet_Ioi fun r hr => ?_
    have hr0 : (0 : ℝ) < r := hr
    by_cases hm : r • (ω : E n) ∈ Ann n R
    · have hnorm : ‖r • (ω : E n)‖ = r := by
        rw [norm_smul, Real.norm_of_nonneg hr0.le]; simp
      have hI : r ∈ I := by
        have := hm; simp only [Ann, mem_ofPred_eq, hnorm] at this; exact this
      rw [indicator_of_mem hm, indicator_of_mem hI]
      gcongr
      exact ENNReal.ofReal_le_ofReal (pow_le_pow_left₀ hr0.le (by linarith [hI.2]) _)
    · rw [indicator_of_notMem hm, mul_zero]; exact bot_le
  have hmeas : Measurable (Function.uncurry fun (ω : sphere (0 : E n) 1) (r : ℝ) =>
      I.indicator (fun r => C * F (r • (ω : E n))) r) := by
    have e : (Function.uncurry fun (ω : sphere (0 : E n) 1) (r : ℝ) =>
        I.indicator (fun r => C * F (r • (ω : E n))) r) =
        (Prod.snd ⁻¹' I).indicator (fun p : sphere (0 : E n) 1 × ℝ => C * F (p.2 • (p.1 : E n))) := by
      ext p; simp [Function.uncurry, indicator]
    rw [e]
    refine Measurable.indicator ?_ (measurable_snd measurableSet_Ioo)
    exact measurable_const.mul (hFm.comp (measurable_snd.smul
      (measurable_subtype_coe.comp measurable_fst)))
  have step2 := lintegral_lintegral_swap (μ := sphereMeasure n)
    (ν := volume.restrict (Ioi (0 : ℝ))) hmeas.aemeasurable
  rw [step2] at step1
  have step3 : ∫⁻ r in Ioi (0 : ℝ), (∫⁻ ω, I.indicator (fun r => C * F (r • (ω : E n))) r
      ∂(sphereMeasure n)) ≤ ∫⁻ r, I.indicator (fun _ => C * M) r := by
    refine (lintegral_mono fun r => ?_).trans (setLIntegral_le_lintegral _ _)
    by_cases hI : r ∈ I
    · simp only [indicator_of_mem hI]
      rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      gcongr
      exact per_r n hq Cr hCr hR c h hsupp (by linarith [hI.1]) (by linarith [hI.2])
    · simp [indicator_of_notMem hI]
  rw [lintegral_indicator_const measurableSet_Ioo, Real.volume_Ioo] at step3
  refine step1.trans (step3.trans ?_)
  have h2δ : ENNReal.ofReal (1 + δ - (1 - δ)) ≤ ENNReal.ofReal (1 / R) := by
    apply ENNReal.ofReal_le_ofReal
    rw [hδdef]
    have : 0 < R := by linarith
    rw [show 1 + 1 / (16 * R) - (1 - 1 / (16 * R)) = (1 / 8) * (1 / R) by field_simp; ring]
    have : 0 < 1 / R := by positivity
    linarith
  have hK : K = (Cr : ℝ≥0∞) ^ q * ENNReal.ofReal ((2 ^ α) ^ q) * ENNReal.ofReal (R ^ α) ^ q := by
    simp only [K]
    rw [Real.mul_rpow (by norm_num) (by linarith), ENNReal.ofReal_mul (by positivity),
      ENNReal.mul_rpow_of_nonneg _ _ hq0, ENNReal.mul_rpow_of_nonneg _ _ hq0,
      ENNReal.ofReal_rpow_of_nonneg (by positivity) hq0]
    ring
  have hC2 : ((Real.toNNReal (2 ^ (n - 1) * 2 ^ ((n : ℝ) * q) * (2 ^ α) ^ q) * Cr ^ q : ℝ≥0) :
      ℝ≥0∞) = C * ENNReal.ofReal (2 ^ ((n : ℝ) * q)) * ENNReal.ofReal ((2 ^ α) ^ q) *
        (Cr : ℝ≥0∞) ^ q := by
    rw [ENNReal.coe_mul, ENNReal.coe_rpow_of_nonneg _ hq0]
    change ENNReal.ofReal _ * _ = _
    rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by positivity)]
  rw [hC2]
  simp only [M, hK]
  calc C * (ENNReal.ofReal (2 ^ ((n : ℝ) * q)) * ((Cr : ℝ≥0∞) ^ q *
        ENNReal.ofReal ((2 ^ α) ^ q) * ENNReal.ofReal (R ^ α) ^ q * H)) *
        ENNReal.ofReal (1 + δ - (1 - δ))
      ≤ C * (ENNReal.ofReal (2 ^ ((n : ℝ) * q)) * ((Cr : ℝ≥0∞) ^ q *
        ENNReal.ofReal ((2 ^ α) ^ q) * ENNReal.ofReal (R ^ α) ^ q * H)) *
        ENNReal.ofReal (1 / R) := by gcongr
    _ = _ := by ring

end TaoBR.RSU

end
end

section
section
/-!
# Decomposition `f = Σ g_i φ_i`
-/

open MeasureTheory Metric Set Filter Topology
open scoped FourierTransform ENNReal NNReal SchwartzMap RealInnerProductSpace ComplexConjugate
  Pointwise

namespace TaoBR.RSU

lemma sparse_far {n : ℕ} {R : ℝ} (hR : 1 ≤ R) {N : ℕ} {x : Fin N → E n}
    (hx : IsSparse ((3 * n + 3 : ℕ) : ℝ) R x) {i j : Fin N} (hij : i ≠ j) :
    8 * R ≤ dist (x i) (x j) := by
  have h := hx i j hij
  rw [Real.rpow_natCast, Real.rpow_natCast] at h
  have hN : (2 : ℝ) ≤ N := by
    have : 2 ≤ N := by
      by_contra hc
      push Not at hc
      interval_cases N
      · exact i.elim0
      · exact hij (Subsingleton.elim _ _)
    exact_mod_cast this
  have h1 : R ≤ R ^ (3 * n + 3) := le_self_pow₀ hR (by omega)
  have h2 : (8 : ℝ) ≤ (N : ℝ) ^ (3 * n + 3) := by
    calc (8 : ℝ) = 2 ^ 3 := by norm_num
      _ ≤ 2 ^ (3 * n + 3) := pow_le_pow_right₀ (by norm_num) (by omega)
      _ ≤ _ := pow_le_pow_left₀ (by norm_num) hN _
  have : 8 * R ≤ R ^ (3 * n + 3) * (N : ℝ) ^ (3 * n + 3) := by nlinarith
  linarith

/-- The pieces `g_i = f / φ_i` near `x_i`. -/
noncomputable def gfun (n : ℕ) (R : ℝ) (c : E n) (f : E n → ℂ) (y : E n) : ℂ :=
  if dist y c < 2 * R then f y / phiLoc n R c y else 0

lemma decomp (n : ℕ) (hn : 2 ≤ n) {R : ℝ} (hR : 1 ≤ R) {N : ℕ} (x : Fin N → E n)
    (hx : IsSparse ((3 * n + 3 : ℕ) : ℝ) R x) (f : 𝓢(E n, ℂ))
    (hf : tsupport f ⊆ ⋃ i, closedBall (x i) R) {q : ℝ} (hq : 0 < q) :
    ∃ g : Fin N → 𝓢(E n, ℂ), (∀ i, tsupport (g i) ⊆ closedBall (x i) R) ∧
      (∀ y, f y = ∑ i, g i y * phiLoc n R (x i) y) ∧
      ∑ i, ∫⁻ y, ‖g i y‖ₑ ^ q ≤ (2 : ℝ≥0∞) ^ q * ∫⁻ y, ‖f y‖ₑ ^ q := by
  have hR0 : 0 < R := by linarith
  -- f vanishes off the balls
  have hf0 : ∀ y, (∀ i, R < dist y (x i)) → f y = 0 := by
    intro y hy
    by_contra h
    have : y ∈ ⋃ i, closedBall (x i) R := hf (subset_tsupport _ h)
    obtain ⟨i, hi⟩ := mem_iUnion.1 this
    exact absurd (mem_closedBall.1 hi) (not_le.2 (hy i))
  -- uniqueness of the nearby centre
  have huniq : ∀ y i j, dist y (x i) < 2 * R → i ≠ j → 2 * R ≤ dist y (x j) := by
    intro y i j hi hij
    have := sparse_far hR hx hij
    have := dist_triangle (x i) y (x j)
    rw [dist_comm (x i) y] at this
    linarith
  have hzero : ∀ i y, R < dist y (x i) → gfun n R (x i) f y = 0 := by
    intro i y hy
    unfold gfun
    split_ifs with h
    · rw [hf0 y (fun j => ?_), zero_div]
      by_cases hij : i = j
      · subst hij; exact hy
      · linarith [huniq y i j h hij]
    · rfl
  have hsupp : ∀ i, tsupport (gfun n R (x i) f) ⊆ closedBall (x i) R := by
    intro i
    refine closure_minimal (fun y hy => ?_) isClosed_closedBall
    by_contra h
    exact hy (hzero i y (not_le.1 (fun h' => h (mem_closedBall.2 h'))))
  have hcs : ∀ i, HasCompactSupport (gfun n R (x i) f) := fun i =>
    (isCompact_closedBall (x i) R).of_isClosed_subset (isClosed_tsupport _) (hsupp i)
  have hcd : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (gfun n R (x i) f) := by
    intro i
    rw [contDiff_iff_contDiffAt]
    intro y
    by_cases hy : dist y (x i) < 2 * R
    · have hev : gfun n R (x i) f =ᶠ[𝓝 y] fun z => f z / phiLoc n R (x i) z := by
        filter_upwards [isOpen_lt (continuous_id.dist continuous_const) continuous_const
          |>.mem_nhds hy] with z hz
        simp only [gfun, if_pos (show dist z (x i) < 2 * R from hz)]
      refine ContDiffAt.congr_of_eventuallyEq ?_ hev
      have hne : phiLoc n R (x i) y ≠ 0 := by
        intro h0; have := phiLoc_lower (c := x i) hR0 hy; rw [h0, norm_zero] at this
        norm_num at this
      have h1 : ContDiffAt ℝ (⊤ : ℕ∞) (phiLoc n R (x i))⁻¹ y :=
        ContDiffAt.inv (phiLoc_contDiff.contDiffAt) hne
      have h2 := ((f.smooth ⊤).contDiffAt (x := y)).mul h1
      refine h2.congr_of_eventuallyEq (Eventually.of_forall (fun z => ?_))
      simp [div_eq_mul_inv]
    · have hy' : R < dist y (x i) := by linarith
      have hev : gfun n R (x i) f =ᶠ[𝓝 y] fun _ => 0 := by
        filter_upwards [isOpen_lt continuous_const (continuous_id.dist continuous_const)
          |>.mem_nhds hy'] with z hz
        exact hzero i z hz
      exact contDiffAt_const.congr_of_eventuallyEq hev
  refine ⟨fun i => (hcs i).toSchwartzMap (hcd i), fun i => hsupp i, ?_, ?_⟩
  · intro y
    show f y = ∑ i, gfun n R (x i) f y * phiLoc n R (x i) y
    by_cases h : ∃ i, dist y (x i) < 2 * R
    · obtain ⟨i, hi⟩ := h
      rw [Finset.sum_eq_single i]
      · have hne : phiLoc n R (x i) y ≠ 0 := by
          intro h0; have := phiLoc_lower (c := x i) hR0 hi; rw [h0, norm_zero] at this
          norm_num at this
        simp only [gfun, if_pos hi]
        field_simp
      · intro j _ hji
        have := huniq y i j hi (Ne.symm hji)
        simp only [gfun, if_neg (not_lt.2 this), zero_mul]
      · intro h; exact absurd (Finset.mem_univ i) h
    · push Not at h
      rw [hf0 y (fun i => by linarith [h i])]
      symm
      refine Finset.sum_eq_zero (fun i _ => ?_)
      simp only [gfun, if_neg (not_lt.2 (h i)), zero_mul]
  · -- pointwise bound
    have hpt : ∀ y, ∑ i, ‖gfun n R (x i) f y‖ₑ ^ q ≤ (2 : ℝ≥0∞) ^ q * ‖f y‖ₑ ^ q := by
      intro y
      by_cases h : ∃ i, dist y (x i) < 2 * R
      · obtain ⟨i, hi⟩ := h
        rw [Finset.sum_eq_single i]
        · have hl := phiLoc_lower (c := x i) hR0 hi
          have hb : ‖gfun n R (x i) f y‖ ≤ 2 * ‖f y‖ := by
            simp only [gfun, if_pos hi, norm_div]
            rw [div_le_iff₀ (by linarith)]
            nlinarith [norm_nonneg (f y)]
          rw [← ENNReal.mul_rpow_of_nonneg _ _ hq.le]
          refine ENNReal.rpow_le_rpow ?_ hq.le
          rw [← ofReal_norm, ← ofReal_norm]
          calc ENNReal.ofReal ‖gfun n R (x i) f y‖ ≤ ENNReal.ofReal (2 * ‖f y‖) :=
                ENNReal.ofReal_le_ofReal hb
            _ = 2 * ENNReal.ofReal ‖f y‖ := by
                rw [ENNReal.ofReal_mul (by norm_num)]; simp
        · intro j _ hji
          have := huniq y i j hi (Ne.symm hji)
          simp only [gfun, if_neg (not_lt.2 this), enorm_zero, ENNReal.zero_rpow_of_pos hq]
        · intro h; exact absurd (Finset.mem_univ i) h
      · push Not at h
        rw [Finset.sum_eq_zero (fun i _ => by
          simp only [gfun, if_neg (not_lt.2 (h i)), enorm_zero, ENNReal.zero_rpow_of_pos hq])]
        exact bot_le
    have hmeas : ∀ i, Measurable (fun y => ‖gfun n R (x i) f y‖ₑ ^ q) := fun i =>
      ((hcd i).continuous.measurable.enorm).pow_const q
    show ∑ i, ∫⁻ y, ‖gfun n R (x i) f y‖ₑ ^ q ≤ _
    rw [← lintegral_finset_sum _ (fun i _ => hmeas i), ← lintegral_const_mul' _ _
      (ENNReal.rpow_ne_top_of_nonneg hq.le (by simp))]
    exact lintegral_mono hpt

end TaoBR.RSU

end
end

section
section
/-!
# Lemma 3.2 of Tao 1999: assembly
-/

open MeasureTheory Metric Set Filter Topology
open scoped FourierTransform ENNReal NNReal SchwartzMap RealInnerProductSpace ComplexConjugate
  Pointwise

namespace TaoBR.RSU

/-- The class of inputs: measurable, bounded, supported in the annulus. -/
def PG (n : ℕ) (R : ℝ) {N : ℕ} (G : Fin N → E n → ℂ) : Prop :=
  ∀ i, Measurable (G i) ∧ (∃ B : ℝ, ∀ η, ‖G i η‖ ≤ B) ∧ ∀ η ∉ Ann n R, G i η = 0

variable {n : ℕ} {R : ℝ} {N : ℕ}

lemma Ann_subset (hR : 1 ≤ R) : Ann n R ⊆ closedBall 0 2 := by
  intro η hη
  rw [mem_closedBall, dist_zero_right]
  have : 1 / (16 * R) ≤ 1 := by rw [div_le_one (by positivity)]; linarith
  linarith [hη.2]

lemma Ann_measurable : MeasurableSet (Ann n R) :=
  (measurableSet_lt measurable_const measurable_norm).inter
    (measurableSet_lt measurable_norm measurable_const)

lemma PG_eq_indicator {G : Fin N → E n → ℂ} (hR : 1 ≤ R) (hG : PG n R G) (i : Fin N) :
    G i = (closedBall (0 : E n) 2).indicator (G i) := by
  funext η
  by_cases h : η ∈ closedBall (0 : E n) 2
  · rw [indicator_of_mem h]
  · rw [indicator_of_notMem h, (hG i).2.2 η (fun h' => h (Ann_subset hR h'))]

lemma PG_integrable {G : Fin N → E n → ℂ} (hR : 1 ≤ R) (hG : PG n R G) (i : Fin N) :
    Integrable (G i) := by
  obtain ⟨B, hB⟩ := (hG i).2.1
  rw [PG_eq_indicator hR hG i, integrable_indicator_iff measurableSet_closedBall]
  exact Measure.integrableOn_of_bounded (M := B) measure_closedBall_lt_top.ne
    (hG i).1.aestronglyMeasurable (Eventually.of_forall hB)

lemma PG_memLp {G : Fin N → E n → ℂ} (hR : 1 ≤ R) (hG : PG n R G) (i : Fin N) :
    MemLp (G i) 2 := by
  obtain ⟨B, hB⟩ := (hG i).2.1
  rw [PG_eq_indicator hR hG i, memLp_indicator_iff_restrict measurableSet_closedBall]
  have : IsFiniteMeasure (volume.restrict (closedBall (0 : E n) 2)) :=
    isFiniteMeasure_restrict.2 measure_closedBall_lt_top.ne
  exact MemLp.of_bound (hG i).1.aestronglyMeasurable B (Eventually.of_forall hB)

lemma PG_truncHi {G : Fin N → E n → ℂ} (hG : PG n R G) (t : ℝ) : PG n R (truncHi G t) := by
  intro i
  obtain ⟨hm, ⟨B, hB⟩, hs⟩ := hG i
  refine ⟨Measurable.ite (measurableSet_lt measurable_const hm.norm) hm measurable_const,
    ⟨max B 0, fun η => ?_⟩, fun η hη => ?_⟩
  · simp only [truncHi]; split_ifs
    · exact (hB η).trans (le_max_left _ _)
    · simp
  · simp only [truncHi, hs η hη]; simp

lemma PG_truncLo {G : Fin N → E n → ℂ} (hG : PG n R G) (t : ℝ) : PG n R (truncLo G t) := by
  intro i
  obtain ⟨hm, ⟨B, hB⟩, hs⟩ := hG i
  refine ⟨Measurable.ite (measurableSet_lt measurable_const hm.norm) measurable_const hm,
    ⟨max B 0, fun η => ?_⟩, fun η hη => ?_⟩
  · simp only [truncLo]; split_ifs
    · simp
    · exact (hB η).trans (le_max_left _ _)
  · simp only [truncLo, hs η hη]; simp

lemma mem_Ann_of_K (hR : 1 ≤ R) {c : E n} (ω : sphere (0 : E n) 1) {η : E n}
    (h : K n R c ((ω : E n) - η) ≠ 0) : η ∈ Ann n R := by
  have h1 := K_support (by linarith) h
  have hω : ‖(ω : E n)‖ = 1 := by simp
  have h2 := abs_norm_sub_norm_le (ω : E n) η
  rw [hω] at h2
  have := abs_lt.1 (h2.trans_lt h1)
  exact ⟨by linarith [this.2], by linarith [this.1]⟩

lemma restriction_eq_Top (hR : 1 ≤ R) (x : Fin N → E n) (f : 𝓢(E n, ℂ)) (g : Fin N → 𝓢(E n, ℂ))
    (hgs : ∀ i, tsupport (g i) ⊆ closedBall (x i) R)
    (hfg : ∀ y, f y = ∑ i, g i y * phiLoc n R (x i) y) :
    restriction (f : E n → ℂ) =
      Top n R x (fun i => (Ann n R).indicator (𝓕 (g i : E n → ℂ))) := by
  have hR0 : 0 < R := by linarith
  have hint : ∀ i, Integrable (fun y => g i y * phiLoc n R (x i) y) := by
    intro i
    have hc : HasCompactSupport (g i : E n → ℂ) :=
      HasCompactSupport.intro (isCompact_closedBall (x i) R)
        (fun y hy => image_eq_zero_of_notMem_tsupport (fun h => hy (hgs i h)))
    exact ((g i).continuous.mul phiLoc_contDiff.continuous).integrable_of_hasCompactSupport
      hc.mul_right
  funext ω
  simp only [restriction, Top]
  have hf : (f : E n → ℂ) = fun y => ∑ i, g i y * phiLoc n R (x i) y := funext hfg
  rw [hf, Real.fourier_eq]
  simp_rw [Finset.smul_sum]
  rw [integral_finset_sum _ (fun i _ => (Real.fourierIntegral_convergent_iff _).2 (hint i))]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  have := fourier_mul_phiLoc (c := x i) hR0 (g i) (g i).integrable (ω : E n)
  rw [Real.fourier_eq] at this
  rw [this]
  refine integral_congr_ae (Eventually.of_forall (fun η => ?_))
  by_cases hK : K n R (x i) ((ω : E n) - η) = 0
  · simp [hK]
  · simp only
    rw [indicator_of_mem (mem_Ann_of_K hR ω hK)]

lemma PG_G (hR : 1 ≤ R) (g : Fin N → 𝓢(E n, ℂ)) :
    PG n R (fun i => (Ann n R).indicator (𝓕 (g i : E n → ℂ))) := by
  intro i
  have hcont : Continuous (𝓕 (g i : E n → ℂ)) := by
    rw [← SchwartzMap.fourier_coe]; exact (𝓕 (g i)).continuous
  refine ⟨hcont.measurable.indicator Ann_measurable, ⟨∫ y, ‖g i y‖, fun η => ?_⟩,
    fun η hη => indicator_of_notMem hη _⟩
  dsimp only
  by_cases h : η ∈ Ann n R
  · rw [indicator_of_mem h]
    exact VectorFourier.norm_fourierIntegral_le_integral_norm _ _ _ _ _
  · rw [indicator_of_notMem h, norm_zero]
    exact integral_nonneg (fun _ => norm_nonneg _)

lemma sum_G_bound {q : ℝ} (hq : 0 < q) (g : Fin N → 𝓢(E n, ℂ)) :
    ∑ i, ∫⁻ η, ‖(Ann n R).indicator (𝓕 (g i : E n → ℂ)) η‖ₑ ^ q =
      ∑ i, ∫⁻ η in Ann n R, ‖𝓕 (g i : E n → ℂ) η‖ₑ ^ q := by
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [← lintegral_indicator Ann_measurable]
  congr 1; ext η
  by_cases h : η ∈ Ann n R
  · simp [indicator_of_mem h]
  · simp [indicator_of_notMem h, ENNReal.zero_rpow_of_pos hq]

lemma isSparse_mono {C C' : ℕ} {x : Fin N → E n} (hR : 1 ≤ R) (hC : C ≤ C')
    (hx : IsSparse (C' : ℝ) R x) : IsSparse (C : ℝ) R x := by
  intro i j hij
  refine le_trans ?_ (hx i j hij)
  have hN : (1 : ℝ) ≤ N := by
    have : 0 < N := Fin.pos i
    exact_mod_cast this
  rw [← Real.mul_rpow (by linarith) (by linarith), ← Real.mul_rpow (by linarith) (by linarith)]
  exact Real.rpow_le_rpow_of_exponent_le (one_le_mul_of_one_le_of_one_le hR hN)
    (by exact_mod_cast hC)

theorem restr_sparse_of_restr_uniform_dev (n : ℕ) (hn : 2 ≤ n) (p : ℝ≥0∞) (hp : 1 < p)
    (hp2 : p < 2) :
    ∃ C₀ : ℝ, ∀ α : ℝ, 0 < α → Restr n p α →
      ∃ C : ℝ≥0, ∀ R : ℝ, 1 ≤ R → ∀ (N : ℕ) (x : Fin N → E n), IsSparse C₀ R x →
        ∀ f : 𝓢(E n, ℂ), tsupport f ⊆ ⋃ i, closedBall (x i) R →
          eLpNorm (restriction f) p (sphereMeasure n) ≤
            C * ENNReal.ofReal (R ^ α) * eLpNorm f p volume := by
  obtain ⟨m, hm, Cs, -, hdec⟩ := sig_decay n hn
  obtain ⟨C0, hC0, A2, hA2, hL2⟩ := Top_L2 hn m hm Cs hdec
  refine ⟨(C0 : ℝ), ?_⟩
  intro α hα ⟨Cr, hCr⟩
  have hptop : p ≠ ⊤ := (hp2.trans ENNReal.ofNat_lt_top).ne
  set q := p.toReal with hq_def
  have hpq : p = ENNReal.ofReal q := (ENNReal.ofReal_toReal hptop).symm
  have hq1 : 1 < q := by
    have := (ENNReal.toReal_lt_toReal (by simp) hptop).2 hp; simpa using this
  have hq2 : q < 2 := by
    have := (ENNReal.toReal_lt_toReal hptop (by simp)).2 hp2; simpa using this
  have hq0 : 0 < q := by linarith
  rw [hpq] at hCr
  obtain ⟨C2, hC2⟩ := est2 n hn hq1.le hα.le Cr hCr
  have hA1 : 0 ≤ A1 n := by
    unfold A1; have := MPhi_nonneg n; positivity
  set A := A1 n + A2 with hA_def
  set Cm := ENNReal.ofReal (q * (2 / (q - 1) + 4 / (2 - q))) with hCm
  set K0 : ℝ≥0∞ := Cm * ENNReal.ofReal A * C2 * 2 ^ q with hK0_def
  have hK0 : K0 ≠ ⊤ := by
    simp only [hK0_def]
    refine ENNReal.mul_ne_top (ENNReal.mul_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top
      ENNReal.ofReal_ne_top) ENNReal.coe_ne_top) ?_
    exact ENNReal.rpow_ne_top_of_nonneg hq0.le (by simp)
  refine ⟨(K0 ^ (1 / q)).toNNReal, ?_⟩
  intro R hR N x hx f hf
  have hR0 : 0 < R := by linarith
  obtain ⟨g, hgs, hfg, hgsum⟩ := decomp n hn hR x (isSparse_mono hR hC0 hx) f hf hq0
  set G : Fin N → E n → ℂ := fun i => (Ann n R).indicator (𝓕 (g i : E n → ℂ)) with hG_def
  have hTG := restriction_eq_Top hR x f g hgs hfg
  have hPG : PG n R G := PG_G hR g
  have hmarc := marc (volume : Measure (E n)) (sphereMeasure n) (PG n R) (Top n R x)
    (ENNReal.ofReal (A * R)) (fun G t hG => PG_truncHi hG t) (fun G t hG => PG_truncLo hG t)
    (fun G G' hG hG' => Top_add hR0 G G' (PG_integrable hR hG) (PG_integrable hR hG'))
    (fun G hG => Top_meas G (fun i => (hG i).1)) (fun G hG i => (hG i).1)
    (fun G hG => (Top_L1 (by omega) hR G (fun i => (hG i).1)).trans (by
      gcongr; nlinarith))
    (fun G hG => (hL2 R hR N x hx G (PG_integrable hR hG) (PG_memLp hR hG)).trans (by
      gcongr; nlinarith))
    hq1 hq2 G hPG
  rw [← hTG] at hmarc
  -- bound the inputs
  have hin : ∑ i, ∫⁻ η, ‖G i η‖ₑ ^ q ≤
      C2 * ENNReal.ofReal (R ^ α) ^ q * ENNReal.ofReal (1 / R) * ((2 : ℝ≥0∞) ^ q *
        ∫⁻ y, ‖f y‖ₑ ^ q) := by
    rw [hG_def, sum_G_bound hq0 g]
    calc ∑ i, ∫⁻ η in Ann n R, ‖𝓕 (g i : E n → ℂ) η‖ₑ ^ q
        ≤ ∑ i, C2 * ENNReal.ofReal (R ^ α) ^ q * ENNReal.ofReal (1 / R) *
            ∫⁻ y, ‖g i y‖ₑ ^ q :=
          Finset.sum_le_sum (fun i _ => hC2 R hR (x i) (g i) (hgs i))
      _ = C2 * ENNReal.ofReal (R ^ α) ^ q * ENNReal.ofReal (1 / R) *
            ∑ i, ∫⁻ y, ‖g i y‖ₑ ^ q := by rw [Finset.mul_sum]
      _ ≤ _ := by gcongr
  have htot : ∫⁻ ω, ‖restriction (f : E n → ℂ) ω‖ₑ ^ q ∂(sphereMeasure n) ≤
      K0 * ENNReal.ofReal (R ^ α) ^ q * ∫⁻ y, ‖f y‖ₑ ^ q := by
    refine hmarc.trans ?_
    calc Cm * ENNReal.ofReal (A * R) * ∑ i, ∫⁻ η, ‖G i η‖ₑ ^ q
        ≤ Cm * ENNReal.ofReal (A * R) * (C2 * ENNReal.ofReal (R ^ α) ^ q *
            ENNReal.ofReal (1 / R) * ((2 : ℝ≥0∞) ^ q * ∫⁻ y, ‖f y‖ₑ ^ q)) := by gcongr
      _ = Cm * (ENNReal.ofReal (A * R) * ENNReal.ofReal (1 / R)) * C2 * 2 ^ q *
            ENNReal.ofReal (R ^ α) ^ q * ∫⁻ y, ‖f y‖ₑ ^ q := by ring
      _ = K0 * ENNReal.ofReal (R ^ α) ^ q * ∫⁻ y, ‖f y‖ₑ ^ q := by
          rw [← ENNReal.ofReal_mul (by nlinarith), mul_assoc A, mul_one_div_cancel hR0.ne',
            mul_one]
  -- take q-th roots
  have hq_ne : ENNReal.ofReal q ≠ 0 := by simpa using hq0
  rw [hpq, eLpNorm_eq_lintegral_rpow_enorm_toReal hq_ne ENNReal.ofReal_ne_top,
    eLpNorm_eq_lintegral_rpow_enorm_toReal hq_ne ENNReal.ofReal_ne_top,
    ENNReal.toReal_ofReal hq0.le, ENNReal.coe_toNNReal
      (ENNReal.rpow_ne_top_of_nonneg (by positivity) hK0)]
  calc (∫⁻ ω, ‖restriction (f : E n → ℂ) ω‖ₑ ^ q ∂(sphereMeasure n)) ^ (1 / q)
      ≤ (K0 * ENNReal.ofReal (R ^ α) ^ q * ∫⁻ y, ‖f y‖ₑ ^ q) ^ (1 / q) :=
        ENNReal.rpow_le_rpow htot (by positivity)
    _ = K0 ^ (1 / q) * ENNReal.ofReal (R ^ α) * (∫⁻ y, ‖f y‖ₑ ^ q) ^ (1 / q) := by
        rw [ENNReal.mul_rpow_of_nonneg _ _ (by positivity),
          ENNReal.mul_rpow_of_nonneg _ _ (by positivity), ← ENNReal.rpow_mul,
          mul_one_div_cancel hq0.ne', ENNReal.rpow_one]

end TaoBR.RSU

namespace TaoBR

alias restr_sparse_of_restr_uniform_dev := RSU.restr_sparse_of_restr_uniform_dev

end TaoBR

end
end

section
open TaoBR

open MeasureTheory Metric
open scoped ENNReal NNReal SchwartzMap


theorem solution (n : ℕ) (hn : 2 ≤ n) (p : ℝ≥0∞) (hp : 1 < p)
    (hp2 : p < 2) :
    ∃ C₀ : ℝ, ∀ α : ℝ, 0 < α → Restr n p α →
      ∃ C : ℝ≥0, ∀ R : ℝ, 1 ≤ R → ∀ (N : ℕ) (x : Fin N → E n), IsSparse C₀ R x →
        ∀ f : 𝓢(E n, ℂ), tsupport f ⊆ ⋃ i, closedBall (x i) R →
          eLpNorm (restriction f) p (sphereMeasure n) ≤
            C * ENNReal.ofReal (R ^ α) * eLpNorm f p volume := by
  apply TaoBR.restr_sparse_of_restr_uniform_dev <;> assumption

end
