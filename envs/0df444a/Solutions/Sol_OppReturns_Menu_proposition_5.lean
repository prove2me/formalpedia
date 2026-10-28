-- Prove2me | solution 1 for OppReturns.Menu.proposition_5
-- status  : ACCEPTED   (disprove)
-- author  : @Nickrobbins95
-- created : 2026-10-26T06:01:54.187973+00:00
-- url     : https://prove2.me/submissions/0943d41d-546d-4f2b-b7fd-caa5f1fd3ac7

import Mathlib
import Definitions.Def_OppReturns_Menu_Model

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Set

namespace OR77

noncomputable def psiU (V : ℝ) (x : ℝ) : ℝ := Set.indicator (Set.Ioo 0 V) (fun _ => 1 / V) x

noncomputable def nuU (V : ℝ) : Measure ℝ :=
  volume.withDensity (fun x => ENNReal.ofReal (psiU V x))

lemma nuU_eq (V : ℝ) : nuU V = ENNReal.ofReal (1 / V) • volume.restrict (Set.Ioo 0 V) := by
  unfold nuU psiU
  have h : (fun x => ENNReal.ofReal (Set.indicator (Ioo 0 V) (fun _ => 1 / V) x)) =
      Set.indicator (Ioo 0 V) (fun _ => ENNReal.ofReal (1 / V)) := by
    funext x; by_cases hx : x ∈ Ioo 0 V <;> simp [hx]
  rw [h, withDensity_indicator measurableSet_Ioo, withDensity_const]

lemma nuU_apply (V : ℝ) (A : Set ℝ) :
    nuU V A = ENNReal.ofReal (1 / V) * volume (A ∩ Ioo 0 V) := by
  rw [nuU_eq, Measure.smul_apply, Measure.restrict_apply' measurableSet_Ioo, smul_eq_mul]

lemma nuU_prob {V : ℝ} (hV : 0 < V) : IsProbabilityMeasure (nuU V) := by
  constructor
  rw [nuU_apply, univ_inter, Real.volume_Ioo, ← ENNReal.ofReal_mul (by positivity)]
  rw [sub_zero, one_div, inv_mul_cancel₀ hV.ne', ENNReal.ofReal_one]

lemma nuU_Iio {V : ℝ} (hV : 0 < V) {r : ℝ} (h0 : 0 ≤ r) (h1 : r ≤ V) :
    (nuU V (Iio r)).toReal = r / V := by
  have hs : Iio r ∩ Ioo 0 V = Ioo 0 r := by
    ext x; simp only [mem_inter_iff, mem_Iio, mem_Ioo]
    constructor
    · rintro ⟨h2, h3, _⟩; exact ⟨h3, h2⟩
    · rintro ⟨h2, h3⟩; exact ⟨h3, h2, by linarith⟩
  rw [nuU_apply, hs, Real.volume_Ioo, ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity),
    ENNReal.toReal_ofReal (by linarith)]
  ring

lemma nuU_Iio_ge {V : ℝ} (hV : 0 < V) {r : ℝ} (h1 : V ≤ r) :
    (nuU V (Iio r)).toReal = 1 := by
  have hs : Iio r ∩ Ioo 0 V = Ioo 0 V := by
    ext x; simp only [mem_inter_iff, mem_Iio, mem_Ioo]
    constructor
    · rintro ⟨_, h3, h4⟩; exact ⟨h3, h4⟩
    · rintro ⟨h2, h3⟩; exact ⟨by linarith, h2, h3⟩
  rw [nuU_apply, hs, Real.volume_Ioo, ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity),
    ENNReal.toReal_ofReal (by linarith), sub_zero]
  field_simp

lemma nuU_cdf {V : ℝ} (hV : 0 < V) (x : ℝ) :
    cdf (nuU V) x = max 0 (min (x / V) 1) := by
  haveI := nuU_prob hV
  rw [cdf_eq_real, measureReal_def]
  rcases le_or_gt x 0 with hx | hx
  · have hs : Iic x ∩ Ioo 0 V = ∅ := by
      ext y; simp only [mem_inter_iff, mem_Iic, mem_Ioo, mem_empty_iff_false, iff_false]
      rintro ⟨h2, h3, _⟩; linarith
    rw [nuU_apply, hs, measure_empty, mul_zero, ENNReal.toReal_zero]
    have : x / V ≤ 0 := div_nonpos_of_nonpos_of_nonneg hx hV.le
    rw [min_eq_left (by linarith), max_eq_left this]
  rcases lt_or_ge x V with hx2 | hx2
  · have hs : Iic x ∩ Ioo 0 V = Ioc 0 x := by
      ext y; simp only [mem_inter_iff, mem_Iic, mem_Ioo, mem_Ioc]
      constructor
      · rintro ⟨h2, h3, _⟩; exact ⟨h3, h2⟩
      · rintro ⟨h2, h3⟩; exact ⟨h3, h2, by linarith⟩
    rw [nuU_apply, hs, Real.volume_Ioc, ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity),
      ENNReal.toReal_ofReal (by linarith)]
    have h1 : x / V ≤ 1 := (div_le_one hV).2 hx2.le
    rw [min_eq_left h1, max_eq_right (by positivity)]
    ring
  · have hs : Iic x ∩ Ioo 0 V = Ioo 0 V := by
      ext y; simp only [mem_inter_iff, mem_Iic, mem_Ioo]
      constructor
      · rintro ⟨_, h3, h4⟩; exact ⟨h3, h4⟩
      · rintro ⟨h2, h3⟩; exact ⟨by linarith, h2, h3⟩
    rw [nuU_apply, hs, Real.volume_Ioo, ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity),
      ENNReal.toReal_ofReal (by linarith)]
    have h1 : 1 ≤ x / V := (one_le_div hV).2 hx2
    rw [min_eq_right h1, max_eq_right (by norm_num), sub_zero]
    field_simp

lemma nuU_integral {V : ℝ} (hV : 0 < V) (g : ℝ → ℝ) :
    ∫ u, g u ∂(nuU V) = (1 / V) * ∫ u in (0:ℝ)..V, g u := by
  rw [nuU_eq, integral_smul_measure, ENNReal.toReal_ofReal (by positivity), smul_eq_mul,
    intervalIntegral.integral_of_le hV.le, integral_Ioc_eq_integral_Ioo]

lemma nuU_Emax {V : ℝ} (hV : 0 < V) {r : ℝ} (h0 : 0 ≤ r) (h1 : r ≤ V) :
    ∫ u, max u r ∂(nuU V) = (V ^ 2 + r ^ 2) / (2 * V) := by
  rw [nuU_integral hV]
  have hc : Continuous (fun u : ℝ => max u r) := continuous_id.max continuous_const
  rw [← intervalIntegral.integral_add_adjacent_intervals (b := r) (hc.intervalIntegrable _ _)
    (hc.intervalIntegrable _ _)]
  have e1 : ∫ u in (0:ℝ)..r, max u r = ∫ u in (0:ℝ)..r, r := by
    apply intervalIntegral.integral_congr
    intro u hu; rw [uIcc_of_le h0] at hu; exact max_eq_right hu.2
  have e2 : ∫ u in r..V, max u r = ∫ u in r..V, u := by
    apply intervalIntegral.integral_congr
    intro u hu; rw [uIcc_of_le h1] at hu; exact max_eq_left hu.1
  rw [e1, e2, intervalIntegral.integral_const, integral_id, smul_eq_mul]
  field_simp; ring

lemma nuU_Emax_ge {V : ℝ} (hV : 0 < V) {r : ℝ} (h1 : V ≤ r) :
    ∫ u, max u r ∂(nuU V) = r := by
  rw [nuU_integral hV]
  have e1 : ∫ u in (0:ℝ)..V, max u r = ∫ u in (0:ℝ)..V, r := by
    apply intervalIntegral.integral_congr
    intro u hu; rw [uIcc_of_le hV.le] at hu; exact max_eq_right (hu.2.trans h1)
  rw [e1, intervalIntegral.integral_const, smul_eq_mul, sub_zero]
  field_simp

lemma nuU_full {V : ℝ} (hV : 0 < V) : OppReturns.Menu.FullSupport (nuU V) V := by
  refine ⟨?_, ?_⟩
  · have hs : (Icc 0 V)ᶜ ∩ Ioo 0 V = ∅ := by
      ext y; simp only [mem_inter_iff, mem_compl_iff, mem_empty_iff_false, iff_false]
      rintro ⟨h2, h3, h4⟩; exact h2 ⟨h3.le, h4.le⟩
    rw [nuU_apply, hs, measure_empty, mul_zero]
  · intro a b ha hab hb
    have hs : Ioo a b ∩ Ioo 0 V = Ioo a b := by
      apply inter_eq_left.2
      intro y hy; exact ⟨by linarith [hy.1], by linarith [hy.2]⟩
    rw [nuU_apply, hs, Real.volume_Ioo]
    apply ENNReal.mul_pos
    · exact (ENNReal.ofReal_pos.2 (by positivity)).ne'
    · exact (ENNReal.ofReal_pos.2 (by linarith)).ne'

lemma nuU_igfr {V : ℝ} (hV : 0 < V) : OppReturns.Menu.IGFR (nuU V) := by
  have hcdf := nuU_cdf hV
  refine ⟨psiU V, ⟨?_, rfl, ?_, ?_⟩, ?_⟩
  · intro x; unfold psiU; by_cases hx : x ∈ Ioo 0 V <;> simp [hx, hV.le]
  · intro ξ h0 h1
    rw [hcdf] at h0 h1
    have hξ0 : 0 < ξ := by
      by_contra h; push_neg at h
      have : ξ / V ≤ 0 := div_nonpos_of_nonpos_of_nonneg h hV.le
      rw [max_eq_left (by linarith [min_le_left (ξ / V) 1])] at h0; exact lt_irrefl _ h0
    have hξ1 : ξ < V := by
      by_contra h; push_neg at h
      have : 1 ≤ ξ / V := (one_le_div hV).2 h
      rw [min_eq_right this, max_eq_right (by norm_num)] at h1; exact lt_irrefl _ h1
    have hψ : psiU V ξ = 1 / V := by unfold psiU; simp [hξ0, hξ1]
    rw [hψ]
    have hd : HasDerivAt (fun x => x / V) (1 / V) ξ := by
      simpa using (hasDerivAt_id ξ).div_const V
    have hev : (fun x => cdf (nuU V) x) =ᶠ[nhds ξ] (fun x => x / V) := by
      filter_upwards [Ioo_mem_nhds hξ0 hξ1] with x hx
      rw [hcdf, min_eq_left ((div_le_one hV).2 hx.2.le), max_eq_right (div_nonneg hx.1.le hV.le)]
    exact (hd.congr_of_eventuallyEq hev).hasDerivWithinAt
  · intro ξ h0
    rw [hcdf] at h0
    unfold psiU
    have : ¬ ξ ∈ Ioo 0 V := by
      rintro ⟨h1, h2⟩
      rw [min_eq_left ((div_le_one hV).2 h2.le), max_eq_right (div_nonneg h1.le hV.le)] at h0
      have : 0 < ξ / V := div_pos h1 hV
      linarith
    simp [this]
  · have key : ∀ ξ, cdf (nuU V) ξ < 1 →
        LariviereIGFR.Char.genFailureRate (nuU V) (psiU V) ξ = if ξ ≤ 0 then 0 else ξ / (V - ξ) := by
      intro ξ h1
      rw [hcdf] at h1
      have hξ1 : ξ < V := by
        by_contra h; push_neg at h
        have : 1 ≤ ξ / V := (one_le_div hV).2 h
        rw [min_eq_right this, max_eq_right (by norm_num)] at h1; exact lt_irrefl _ h1
      unfold LariviereIGFR.Char.genFailureRate LariviereIGFR.Char.failureRate
        LariviereIGFR.Char.survival
      split_ifs with h
      · unfold psiU
        have : ¬ ξ ∈ Ioo 0 V := fun hh => by linarith [hh.1]
        simp [this]
      · push_neg at h
        have hψ : psiU V ξ = 1 / V := by unfold psiU; simp [h, hξ1]
        rw [hψ, hcdf, min_eq_left ((div_le_one hV).2 hξ1.le), max_eq_right (div_nonneg h.le hV.le)]
        have : V - ξ ≠ 0 := by linarith
        field_simp
    intro a ha b hb hab
    simp only [mem_setOf_eq] at ha hb
    rw [key a ha, key b hb]
    have hb1 : b < V := by
      rw [hcdf] at hb
      by_contra h; push_neg at h
      have : 1 ≤ b / V := (one_le_div hV).2 h
      rw [min_eq_right this, max_eq_right (by norm_num)] at hb; exact lt_irrefl _ hb
    split_ifs with h1 h2 h2
    · exact le_rfl
    · push_neg at h2; exact div_nonneg h2.le (by linarith)
    · push_neg at h1; linarith
    · push_neg at h1 h2
      rw [div_le_div_iff₀ (by linarith) (by linarith)]
      nlinarith

noncomputable def Mx (r f : ℝ) : ℝ :=
  f * (1 - 23/500 * f) + (r - 41/500) * (1 - 23/500) * (1 - r / (46/25))

noncomputable def phi (r : ℝ) : ℝ := (46/25 - r) ^ 2 / (2 * (46/25))

lemma phi_le (r : ℝ) (h0 : 0 ≤ r) (h1 : r ≤ 46/25) : phi r ≤ 23/25 := by
  unfold phi; rw [div_le_iff₀ (by norm_num)]; nlinarith

lemma big_mono (r f : ℝ) (hf0 : 0 ≤ f) (hf : f ≤ phi r) (hp : phi r ≤ 23/25) :
    79376/15555 * Mx r f - 22 * (41/250) * (1 - 23/500 * f) ≤
      79376/15555 * Mx r (phi r) - 22 * (41/250) * (1 - 23/500 * phi r) := by
  unfold Mx
  nlinarith [mul_nonneg (sub_nonneg.2 hf) (by nlinarith : (0:ℝ) ≤ 1 - 23/500 * (f + phi r))]

lemma small_mono (r f : ℝ) (hf0 : 0 ≤ f) (hf : f ≤ phi r) (hp : phi r ≤ 23/25) :
    Mx r f - 41/250 * (1 - 23/500 * f) ≤
      Mx r (phi r) - 41/250 * (1 - 23/500 * phi r) := by
  unfold Mx
  nlinarith [mul_nonneg (sub_nonneg.2 hf) (by nlinarith : (0:ℝ) ≤ 1 - 23/500 * (f + phi r))]

lemma big_at (r : ℝ) :
    79376/15555 * Mx r (phi r) - 22 * (41/250) * (1 - 23/500 * phi r) =
      18207029654/27950390625 - (r - 2/25) ^ 2 *
        (73747971/47702000 - 14883/119255 * r + 4961/286212 * r ^ 2) := by
  unfold Mx phi; ring

lemma q_pos (r : ℝ) : 0 < 73747971/47702000 - 14883/119255 * r + 4961/286212 * r ^ 2 := by
  nlinarith [sq_nonneg (r - 4)]

lemma small_at (r : ℝ) (h0 : 0 ≤ r) :
    Mx r (phi r) - 41/250 * (1 - 23/500 * phi r) ≤ 18207029654/27950390625 - 1/2000 := by
  have key : 18207029654/27950390625 - 1/2000 - (Mx r (phi r) - 41/250 * (1 - 23/500 * phi r)) =
      (r - 119/1000) ^ 2 * (90640883/294400000 - 3561/147200 * r + 5/1472 * r ^ 2) +
        560599/73600000000 * (r - 119/1000) + 30585721047377/39820800000000000 := by
    unfold Mx phi; ring
  have hq : 0 ≤ 90640883/294400000 - 3561/147200 * r + 5/1472 * r ^ 2 := by
    nlinarith [sq_nonneg (r - 4)]
  nlinarith [mul_nonneg (sq_nonneg (r - 119/1000)) hq]

noncomputable def D0 : Measure ℝ :=
  ENNReal.ofReal (1 - 63821/326655) • Measure.dirac (1:ℝ) +
    ENNReal.ofReal (63821/326655) • Measure.dirac (22:ℝ)

lemma D0_int (g : ℝ → ℝ) : Integrable g D0 := by
  unfold D0
  exact ((integrable_dirac enorm_lt_top).smul_measure ENNReal.ofReal_ne_top).add_measure
    ((integrable_dirac enorm_lt_top).smul_measure ENNReal.ofReal_ne_top)

lemma D0_integral (g : ℝ → ℝ) :
    ∫ x, g x ∂D0 = (1 - 63821/326655) * g 1 + 63821/326655 * g 22 := by
  have i1 : Integrable g (ENNReal.ofReal (1 - 63821/326655) • Measure.dirac (1:ℝ)) :=
    (integrable_dirac enorm_lt_top).smul_measure ENNReal.ofReal_ne_top
  have i2 : Integrable g (ENNReal.ofReal (63821/326655) • Measure.dirac (22:ℝ)) :=
    (integrable_dirac enorm_lt_top).smul_measure ENNReal.ofReal_ne_top
  unfold D0
  rw [integral_add_measure i1 i2, integral_smul_measure, integral_smul_measure, integral_dirac,
    integral_dirac, ENNReal.toReal_ofReal (by norm_num), ENNReal.toReal_ofReal (by norm_num),
    smul_eq_mul, smul_eq_mul]

lemma D0_prob : IsProbabilityMeasure D0 := by
  constructor
  unfold D0
  rw [Measure.add_apply, Measure.smul_apply, Measure.smul_apply, measure_univ, measure_univ,
    smul_eq_mul, smul_eq_mul, mul_one, mul_one, ← ENNReal.ofReal_add (by norm_num) (by norm_num)]
  norm_num

lemma D0_Iic : D0 (Iic 0) = 0 := by
  unfold D0
  rw [Measure.add_apply, Measure.smul_apply, Measure.smul_apply,
    Measure.dirac_apply' _ measurableSet_Iic, Measure.dirac_apply' _ measurableSet_Iic]
  simp

noncomputable def P0 : OppReturns.Menu.Params :=
  { X := 23/500, c := 123/500, s := 41/500, VL := 46/25, VS := 1,
    νL := nuU (46/25), νS := nuU 1, D := D0 }

lemma GL0 {r : ℝ} (h0 : 0 ≤ r) (h1 : r ≤ 46/25) : OppReturns.Menu.GLf P0 r = r / (46/25) :=
  nuU_Iio (by norm_num) h0 h1

lemma GL0' {r : ℝ} (h1 : 46/25 ≤ r) : OppReturns.Menu.GLf P0 r = 1 :=
  nuU_Iio_ge (by norm_num) h1

lemma GS0 {f : ℝ} (h0 : 0 ≤ f) (h1 : f ≤ 1) : OppReturns.Menu.GSf P0 f = f := by
  have := nuU_Iio (V := 1) (by norm_num) h0 h1
  rw [div_one] at this; exact this

lemma Em0 {r : ℝ} (h0 : 0 ≤ r) (h1 : r ≤ 46/25) :
    OppReturns.Menu.Emax P0 r = ((46/25) ^ 2 + r ^ 2) / (2 * (46/25)) :=
  nuU_Emax (by norm_num) h0 h1

lemma Em0' {r : ℝ} (h1 : 46/25 ≤ r) : OppReturns.Menu.Emax P0 r = r :=
  nuU_Emax_ge (by norm_num) h1

lemma ES0 (y : ℝ) : SupplyChainTheory.expSales P0.D y =
    (1 - 63821/326655) * min y 1 + 63821/326655 * min y 22 := by
  unfold SupplyChainTheory.expSales
  exact D0_integral (fun d => min y d)

lemma ES0_mono {a b : ℝ} (h : a ≤ b) :
    SupplyChainTheory.expSales P0.D a ≤ SupplyChainTheory.expSales P0.D b := by
  rw [ES0, ES0]
  have h1 : min a 1 ≤ min b 1 := min_le_min h le_rfl
  have h2 : min a 22 ≤ min b 22 := min_le_min h le_rfl
  nlinarith

lemma ES0_nonneg {a : ℝ} (h : 0 ≤ a) : 0 ≤ SupplyChainTheory.expSales P0.D a := by
  rw [ES0]
  have h1 : 0 ≤ min a 1 := le_min h (by norm_num)
  have h2 : 0 ≤ min a 22 := le_min h (by norm_num)
  nlinarith

lemma phi_eq (r : ℝ) : phi r = ((46/25) ^ 2 + r ^ 2) / (2 * (46/25)) - r := by
  unfold phi; ring

lemma standing0 : OppReturns.Menu.Standing P0 := by
  refine ⟨by norm_num [P0], by norm_num [P0], by norm_num [P0], by norm_num [P0], by norm_num [P0],
    by norm_num [P0], nuU_prob (by norm_num), nuU_prob (by norm_num), D0_prob,
    nuU_full (by norm_num), nuU_full (by norm_num), nuU_igfr (by norm_num), nuU_igfr (by norm_num),
    D0_Iic, D0_int _, ?_⟩
  rw [Em0 (by norm_num [P0]) (by norm_num [P0])]
  norm_num [P0]

lemma nv (M N y k w : ℝ) (hy : 0 ≤ y) (hN : 0 ≤ N) (hk : 0 ≤ k) (hw0 : 0 ≤ w) :
    M * ((1 - w) * min y 1 + w * min y 22) - k * (y * N) ≤
      max 0 (max (M - k * N) ((1 + 21 * w) * M - 22 * k * N)) := by
  have hA := le_max_left (M - k * N) ((1 + 21 * w) * M - 22 * k * N)
  have hB := le_max_right (M - k * N) ((1 + 21 * w) * M - 22 * k * N)
  have hC := le_max_right 0 (max (M - k * N) ((1 + 21 * w) * M - 22 * k * N))
  have hD := le_max_left 0 (max (M - k * N) ((1 + 21 * w) * M - 22 * k * N))
  set m := max (M - k * N) ((1 + 21 * w) * M - 22 * k * N)
  set m0 := max 0 m
  rcases le_total y 1 with h | h
  · rw [min_eq_left h, min_eq_left (by linarith)]
    have e : M * ((1 - w) * y + w * y) - k * (y * N) = y * (M - k * N) := by ring
    rw [e]
    rcases le_total 0 (M - k * N) with h2 | h2
    · nlinarith [mul_le_mul_of_nonneg_right h h2]
    · nlinarith [mul_nonneg hy (neg_nonneg.2 h2)]
  rcases le_total y 22 with h2 | h2
  · rw [min_eq_right h, min_eq_left h2]
    have e : M * ((1 - w) * 1 + w * y) - k * (y * N) =
        (22 - y) / 21 * (M - k * N) + (y - 1) / 21 * ((1 + 21 * w) * M - 22 * k * N) := by ring
    rw [e]
    nlinarith [mul_le_mul_of_nonneg_left hA (by linarith : (0:ℝ) ≤ (22 - y) / 21),
      mul_le_mul_of_nonneg_left hB (by linarith : (0:ℝ) ≤ (y - 1) / 21)]
  · rw [min_eq_right h, min_eq_right h2]
    nlinarith [mul_le_mul_of_nonneg_left h2 (mul_nonneg hk hN)]

noncomputable def g0 : ℝ := 18207029654/27950390625

lemma ubound {Q p r : ℝ} (h : OppReturns.Menu.FeasU P0 Q p r) :
    OppReturns.Menu.profitU P0 Q p r ≤ g0 := by
  obtain ⟨hQ, hr, hrp, hpE⟩ := h
  unfold OppReturns.Menu.profitU OppReturns.Menu.profit OppReturns.Menu.Mu OppReturns.Menu.Nf
  have hk : P0.c - P0.s = 41/250 := by norm_num [P0]
  have hX : P0.X = 23/500 := rfl
  have hs : P0.s = 41/500 := rfl
  rw [hk, hX, hs]
  rcases le_or_gt r (46/25) with h1 | h1
  · rw [Em0 hr h1] at hpE
    have hf0 : 0 ≤ p - r := by linarith
    have hfphi : p - r ≤ phi r := by rw [phi_eq]; linarith
    have hp := phi_le r hr h1
    rw [GS0 hf0 (by linarith), GL0 hr h1, ES0]
    have hN : 0 < 1 - 23/500 * (p - r) := by nlinarith
    set N := 1 - 23/500 * (p - r) with hNdef
    have hQ' : Q = Q / N * N := by field_simp
    have hy : 0 ≤ Q / N := div_nonneg hQ hN.le
    have hM : (p - r) * N + (r - 41/500) * (1 - 23/500) * (1 - r / (46/25)) = Mx r (p - r) := by
      unfold Mx; rw [hNdef]
    rw [hM]
    have key := nv (Mx r (p - r)) N (Q / N) (41/250) (63821/326655) hy hN.le (by norm_num)
      (by norm_num)
    rw [← hQ'] at key
    have b1 := small_mono r (p - r) hf0 hfphi hp
    have b2 := small_at r hr
    have b3 := big_mono r (p - r) hf0 hfphi hp
    have b4 := big_at r
    have b5 := q_pos r
    have b6 := mul_nonneg (sq_nonneg (r - 2/25)) b5.le
    refine key.trans (max_le (by norm_num [g0]) (max_le ?_ ?_))
    · unfold g0; rw [hNdef]; linarith
    · unfold g0; rw [hNdef]; nlinarith
  · rw [Em0' h1.le] at hpE
    have hpr : p - r = 0 := by linarith
    rw [hpr, GL0' h1.le, GS0 le_rfl (by norm_num)]
    have : 0 ≤ 41/250 * Q := by linarith
    have : (0 : ℝ) < g0 := by norm_num [g0]
    nlinarith

lemma feas0 : OppReturns.Menu.FeasU P0 (66088/3125) (106/115) (2/25) := by
  refine ⟨by norm_num, by norm_num, by norm_num, ?_⟩
  rw [Em0 (by norm_num) (by norm_num)]; norm_num

lemma val0 : OppReturns.Menu.profitU P0 (66088/3125) (106/115) (2/25) = g0 := by
  unfold OppReturns.Menu.profitU OppReturns.Menu.profit OppReturns.Menu.Mu OppReturns.Menu.Nf
  have hf : (106/115 : ℝ) - 2/25 = 484/575 := by norm_num
  rw [hf, GS0 (by norm_num) (by norm_num), GL0 (by norm_num) (by norm_num), ES0]
  have hX : P0.X = 23/500 := rfl
  have hs : P0.s = 41/500 := rfl
  have hc : P0.c = 123/500 := rfl
  rw [hX, hs, hc]
  norm_num [g0]

lemma optU0 : OppReturns.Menu.IsOptU P0 (66088/3125) (106/115) (2/25) :=
  ⟨feas0, fun _ _ _ h => (ubound h).trans (le_of_eq val0.symm)⟩

lemma binds0 : OppReturns.Menu.UniformBinds P0 := by
  intro Q p r ⟨hF, hopt⟩
  have hge := hopt _ _ _ feas0
  rw [val0] at hge
  obtain ⟨hQ, hr, hrp, hpE⟩ := hF
  by_contra hne
  have hlt : p < OppReturns.Menu.Emax P0 r := lt_of_le_of_ne hpE hne
  rcases le_or_gt r (46/25) with h1 | h1
  · have hE := Em0 hr h1
    have hF' : OppReturns.Menu.FeasU P0 Q (OppReturns.Menu.Emax P0 r) r :=
      ⟨hQ, hr, by rw [hE]; nlinarith, le_rfl⟩
    have h2 := hopt _ _ _ hF'
    rw [hE] at h2 hlt
    unfold OppReturns.Menu.profitU OppReturns.Menu.profit OppReturns.Menu.Mu
      OppReturns.Menu.Nf at h2 hge
    have hphi := phi_le r hr h1
    rw [phi_eq] at hphi
    have hf0 : 0 ≤ p - r := by linarith
    set E := ((46/25) ^ 2 + r ^ 2) / (2 * (46/25)) with hEdef
    rw [GS0 hf0 (by linarith)] at h2 hge
    rw [GS0 (by linarith) (by linarith)] at h2
    have hX : P0.X = 23/500 := rfl
    rw [hX] at h2 hge
    set D := (r - P0.s) * (1 - 23/500) * (1 - OppReturns.Menu.GLf P0 r)
    have hk : 0 ≤ (P0.c - P0.s) * Q := mul_nonneg (by norm_num [P0]) hQ
    have hg0 : (0 : ℝ) < g0 := by norm_num [g0]
    have hN' : 0 < 1 - 23/500 * (E - r) := by linarith
    have hNN : 1 - 23/500 * (E - r) ≤ 1 - 23/500 * (p - r) := by linarith
    have hyy : Q / (1 - 23/500 * (p - r)) ≤ Q / (1 - 23/500 * (E - r)) :=
      div_le_div_of_nonneg_left hQ hN' hNN
    have he := ES0_mono hyy
    have he0 := ES0_nonneg (div_nonneg hQ (hN'.trans_le hNN).le)
    set e := SupplyChainTheory.expSales P0.D (Q / (1 - 23/500 * (p - r)))
    set e' := SupplyChainTheory.expSales P0.D (Q / (1 - 23/500 * (E - r)))
    set M := (p - r) * (1 - 23/500 * (p - r)) + D
    set M' := (E - r) * (1 - 23/500 * (E - r)) + D
    have hMM : M < M' := by
      have : M' - M = (E - r - (p - r)) * (1 - 23/500 * ((p - r) + (E - r))) := by ring
      have h3 : 0 < (E - r - (p - r)) * (1 - 23/500 * ((p - r) + (E - r))) :=
        mul_pos (by linarith) (by linarith)
      linarith
    have hMe : 0 < M * e := by linarith
    have he_pos : 0 < e := by
      rcases he0.lt_or_eq with h | h
      · exact h
      · rw [← h, mul_zero] at hMe; exact absurd hMe (lt_irrefl 0)
    have hMpos : 0 < M := by
      by_contra hc; push_neg at hc
      nlinarith
    nlinarith [mul_le_mul_of_nonneg_left he (by linarith : (0:ℝ) ≤ M')]
  · rw [Em0' h1.le] at hlt
    linarith

lemma PiU0 : OppReturns.Menu.PiU P0 = g0 := by
  unfold OppReturns.Menu.PiU
  apply IsGreatest.csSup_eq
  refine ⟨⟨_, _, _, feas0, val0.symm⟩, ?_⟩
  rintro π ⟨Q, p, r, h, rfl⟩
  exact ubound h

lemma feasM0 : OppReturns.Menu.FeasM P0 (1 - 23/500 * (291/500)) (OppReturns.Menu.Emax P0 (41/500))
    (41/500) (2 + 291/500) 2 := by
  have hE := Em0 (r := 41/500) (by norm_num) (by norm_num)
  have hE2 := Em0' (r := 2) (by norm_num)
  refine ⟨by norm_num, by norm_num, by norm_num, ?_, by norm_num, ?_, ?_⟩
  · rw [hE]; norm_num
  · rw [hE, hE2]; norm_num
  · rw [hE]; norm_num [P0]

lemma valM0 : OppReturns.Menu.profitM P0 (1 - 23/500 * (291/500)) (OppReturns.Menu.Emax P0 (41/500))
    (41/500) (2 + 291/500) 2 = 7506928921/11500000000 := by
  have hE := Em0 (r := 41/500) (by norm_num) (by norm_num)
  unfold OppReturns.Menu.profitM OppReturns.Menu.profit OppReturns.Menu.Mm OppReturns.Menu.Nf
    OppReturns.Menu.honestMargin
  have hf : (2 + 291/500 : ℝ) - 2 = 291/500 := by norm_num
  rw [hf, GS0 (by norm_num) (by norm_num), ES0, hE]
  have hX : P0.X = 23/500 := rfl
  have hs : P0.s = 41/500 := rfl
  have hc : P0.c = 123/500 := rfl
  rw [hX, hs, hc]
  norm_num

lemma PiM0_ne : OppReturns.Menu.PiM P0 ≠ g0 := by
  unfold OppReturns.Menu.PiM
  by_cases hb : BddAbove {π | ∃ Q pH rH pR rR, OppReturns.Menu.FeasM P0 Q pH rH pR rR ∧
      π = OppReturns.Menu.profitM P0 Q pH rH pR rR}
  · have := le_csSup hb ⟨_, _, _, _, _, feasM0, valM0.symm⟩
    intro h; rw [h] at this; norm_num [g0] at this
  · rw [Real.sSup_of_not_bddAbove hb]; norm_num [g0]

end OR77

open OppReturns.Menu in
theorem solution : ¬ (∀ (P : Params) (hS : Standing P) (hB : UniformBinds P)
    (Q p r : ℝ) (hU : IsOptU P Q p r),
    (r < P.s → PiM P = PiU P ∧
      ∃ Qm pH rH pR rR, IsOptM P Qm pH rH pR rR ∧
        pH = p ∧ rH = r ∧ pR - rR = p - r) ∧
    (P.s ≤ r → PiM P = PiT P ∧
      ∃ Qt pt rtR rtH, IsOptT P Qt pt rtR rtH ∧
        ∃ Qm pH rH pR rR, IsOptM P Qm pH rH pR rR ∧
          pH = pt ∧ rH = rtH ∧ pR - rR = pt - rtR)) := by
  intro h
  have h1 := (h OR77.P0 OR77.standing0 OR77.binds0 _ _ _ OR77.optU0).1
    (by show (2/25 : ℝ) < 41/500; norm_num)
  exact OR77.PiM0_ne (h1.1.trans OR77.PiU0)
