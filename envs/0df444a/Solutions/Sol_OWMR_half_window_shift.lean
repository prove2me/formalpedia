-- Prove2me | solution 1 for OWMR.half_window_shift
-- status  : ACCEPTED   (prove)
-- author  : @Ming Hu
-- created : 2026-11-16T03:07:33.824709+00:00
-- url     : https://prove2.me/submissions/bfae1a4a-1ea3-45ef-bd02-94265032fe1e

import Theorems.Thm_OWMR_renewal_regeneration
import Theorems.Thm_OWMR_renewalMeasure_Ico_lt_top
import Mathlib.MeasureTheory.Integral.Bochner.Set

/-!
Lemma 5 (half-window shift). Write `Φ(υ) = ∫_{[0,b)} g(υ+x) U(dx)` and, for a first-passage
position `y ≥ b`, `Ψ(y) = ∫_{[0, 2b-y)} g(y+x) U(dx)` (zero for `y ≥ 2b`).

Step 1 (regeneration at the level `b`): `∫_{[b,2b)} g dU ≤ sup_{y ≥ b} Ψ(y)`.
Step 2 (concavity, as in the source): `Φ(0) + Ψ(y) ≤ 2 max_{[0,b]} Φ` for every `y ≥ b`, with the four
cases `y ≥ 2b`; `m ≤ b`; `b ≤ y ≤ m`; `m < y` and `b < m`, where `m` maximizes `g` on `[0, 2b]`.
Hence `∫_{[0,2b)} g dU = Φ(0) + ∫_{[b,2b)} g dU ≤ 2 max Φ`, and `Φ` attains its maximum on `[0,b]`.
The proof works with the clamped extension `G(x) = g(max 0 (min x 2b))`, which is continuous on `ℝ`
and agrees with `g` on `[0, 2b]`.
-/

open MeasureTheory
open scoped ENNReal NNReal
open OWMR

private lemma renewal_Iio_zero (ρ : Measure ℝ≥0) [IsProbabilityMeasure ρ] :
    renewalMeasure ρ (Set.Iio 0) = 0 := by
  unfold renewalMeasure
  rw [Measure.sum_apply _ measurableSet_Iio]
  refine ENNReal.tsum_eq_zero.2 fun n => ?_
  rw [Measure.map_apply (Finset.measurable_sum _ fun j _ => (measurable_pi_apply j).coe_nnreal_real)
    measurableSet_Iio]
  have : (fun z : Fin n → ℝ≥0 => ∑ j, (z j : ℝ)) ⁻¹' Set.Iio 0 = ∅ := by
    ext z
    simp only [Set.mem_preimage, Set.mem_Iio, Set.mem_empty_iff_false, iff_false, not_lt]
    exact Finset.sum_nonneg fun j _ => (z j).2
  rw [this, measure_empty]

private lemma intOn (ρ : Measure ℝ≥0) [IsProbabilityMeasure ρ] (hρ : 0 < ∫⁻ x, (x : ℝ≥0∞) ∂ρ)
    {φ : ℝ → ℝ} (hφ : Continuous φ) {a e : ℝ} (ha : 0 ≤ a) :
    IntegrableOn φ (Set.Ico a e) (renewalMeasure ρ) := by
  obtain ⟨C, hC⟩ := (isCompact_Icc (a := a) (b := e)).exists_bound_of_continuousOn hφ.continuousOn
  refine Measure.integrableOn_of_bounded (M := C)
    (ne_top_of_le_ne_top (renewalMeasure_Ico_lt_top ρ hρ e).ne
      (measure_mono (Set.Ico_subset_Ico_left ha))) hφ.aestronglyMeasurable ?_
  exact ae_restrict_of_forall_mem measurableSet_Ico fun x hx => hC x (Set.Ico_subset_Icc_self hx)

/-- Concavity facts used in Step 2, for a concave `G` on `[0, 2b]` maximized at `m`. -/
private lemma concave_facts (b m : ℝ) (G : ℝ → ℝ) (hG0 : ∀ x, 0 ≤ G x)
    (hconc : ConcaveOn ℝ (Set.Icc 0 (2 * b)) G) (hm : m ∈ Set.Icc 0 (2 * b))
    (hmax : ∀ x ∈ Set.Icc 0 (2 * b), G x ≤ G m) :
    (∀ a a', 0 ≤ a → a ≤ a' → a' ≤ m → G a ≤ G a') ∧
    (∀ a a', m ≤ a → a ≤ a' → a' ≤ 2 * b → G a' ≤ G a) ∧
    (∀ z, m ≤ z → z ≤ 2 * b → m < 2 * b → (2 * b - z) * G m ≤ (2 * b - m) * G z) := by
  refine ⟨fun a a' ha haa' ha'm => ?_, fun a a' hma haa' ha' => ?_, fun z hmz hz hm2 => ?_⟩
  · rcases eq_or_lt_of_le haa' with h | h
    · rw [h]
    have hpos : 0 < m - a := by linarith
    set l := (m - a') / (m - a) with hl
    have hl0 : 0 ≤ l := div_nonneg (by linarith) hpos.le
    have hl1 : 0 ≤ 1 - l := by
      rw [hl, sub_nonneg, div_le_one hpos]; linarith
    have hlm : l * (m - a) = m - a' := div_mul_cancel₀ _ hpos.ne'
    have hcv := hconc.2 (⟨ha, by linarith [hm.2]⟩ : a ∈ Set.Icc 0 (2 * b)) hm hl0 hl1
      (by ring)
    simp only [smul_eq_mul] at hcv
    rw [show l * a + (1 - l) * m = a' by linear_combination -hlm] at hcv
    have hGa := hmax a ⟨ha, by linarith [hm.2]⟩
    nlinarith [mul_le_mul_of_nonneg_left hGa hl1]
  · rcases eq_or_lt_of_le haa' with h | h
    · rw [h]
    have hpos : 0 < a' - m := by linarith
    set l := (a' - a) / (a' - m) with hl
    have hl0 : 0 ≤ l := div_nonneg (by linarith) hpos.le
    have hl1 : 0 ≤ 1 - l := by
      rw [hl, sub_nonneg, div_le_one hpos]; linarith
    have hlm : l * (a' - m) = a' - a := div_mul_cancel₀ _ hpos.ne'
    have hcv := hconc.2 hm (⟨by linarith [hm.1], ha'⟩ : a' ∈ Set.Icc 0 (2 * b)) hl0 hl1
      (by ring)
    simp only [smul_eq_mul] at hcv
    rw [show l * m + (1 - l) * a' = a by linear_combination -hlm] at hcv
    have hGa' := hmax a' ⟨by linarith [hm.1], ha'⟩
    nlinarith [mul_le_mul_of_nonneg_left hGa' hl0]
  · have hpos : 0 < 2 * b - m := by linarith
    set l := (2 * b - z) / (2 * b - m) with hl
    have hl0 : 0 ≤ l := div_nonneg (by linarith) hpos.le
    have hl1 : 0 ≤ 1 - l := by
      rw [hl, sub_nonneg, div_le_one hpos]; linarith
    have hlm : l * (2 * b - m) = 2 * b - z := div_mul_cancel₀ _ hpos.ne'
    have h2b : (2 * b) ∈ Set.Icc 0 (2 * b) := ⟨by linarith [hm.1], le_rfl⟩
    have hcv := hconc.2 hm h2b hl0 hl1 (by ring)
    simp only [smul_eq_mul] at hcv
    rw [show l * m + (1 - l) * (2 * b) = z by linear_combination -hlm] at hcv
    have hG2 := hG0 (2 * b)
    have h1 : l * G m ≤ G z := by nlinarith [mul_nonneg hl1 hG2]
    have h2 := mul_le_mul_of_nonneg_left h1 hpos.le
    have h3 : (2 * b - m) * (l * G m) = (2 * b - z) * G m := by
      rw [← mul_assoc, mul_comm (2 * b - m) l, hlm]
    linarith

theorem solution (ρ : Measure ℝ≥0) [IsProbabilityMeasure ρ]
    (hρ : 0 < ∫⁻ x, (x : ℝ≥0∞) ∂ρ) (b : ℝ) (hb : 0 < b) (g : ℝ → ℝ)
    (hgc : ContinuousOn g (Set.Icc 0 (2 * b))) (hg0 : ∀ x ∈ Set.Icc 0 (2 * b), 0 ≤ g x)
    (hgconc : ConcaveOn ℝ (Set.Icc 0 (2 * b)) g) :
    ∃ υ ∈ Set.Icc 0 b, ∫ x in Set.Ico 0 (2 * b), g x ∂(renewalMeasure ρ)
      ≤ 2 * ∫ x in Set.Ico 0 b, g (υ + x) ∂(renewalMeasure ρ) := by
  -- the clamped extension `G`
  have hPmem : ∀ x : ℝ, max 0 (min x (2 * b)) ∈ Set.Icc 0 (2 * b) := fun x =>
    ⟨le_max_left _ _, max_le (by linarith) (min_le_right _ _)⟩
  obtain ⟨G, hG⟩ : ∃ G : ℝ → ℝ, G = fun x => g (max 0 (min x (2 * b))) := ⟨_, rfl⟩
  have hGc : Continuous G := by
    rw [hG]
    exact hgc.comp_continuous (continuous_const.max (continuous_id.min continuous_const)) hPmem
  have hGeq : ∀ x ∈ Set.Icc (0 : ℝ) (2 * b), G x = g x := fun x hx => by
    rw [hG]
    simp only
    rw [min_eq_left hx.2, max_eq_right hx.1]
  have hG0 : ∀ x, 0 ≤ G x := fun x => by rw [hG]; exact hg0 _ (hPmem x)
  have hGconc : ConcaveOn ℝ (Set.Icc 0 (2 * b)) G :=
    hgconc.congr fun x hx => (hGeq x hx).symm
  -- a maximizer `m` of `G` on `[0, 2b]`
  obtain ⟨m, hm, hmaxOn⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := 2 * b)).exists_isMaxOn
    (Set.nonempty_Icc.2 (by linarith)) hGc.continuousOn
  have hmax : ∀ x ∈ Set.Icc (0 : ℝ) (2 * b), G x ≤ G m := isMaxOn_iff.1 hmaxOn
  obtain ⟨hM1, hM2, hchord⟩ := concave_facts b m G hG0 hGconc hm hmax
  have hmid : ∀ a ∈ Set.Icc (0 : ℝ) (2 * b), ∀ c ∈ Set.Icc (0 : ℝ) (2 * b),
      G a + G c ≤ 2 * G ((a + c) / 2) := by
    intro a ha c hc
    have := hGconc.2 ha hc (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (0 : ℝ) ≤ 1 / 2)
      (by norm_num)
    simp only [smul_eq_mul] at this
    rw [show 1 / 2 * a + 1 / 2 * c = (a + c) / 2 by ring] at this
    linarith
  -- finiteness and integrability on `[0, b)`
  have hUb : renewalMeasure ρ (Set.Ico 0 b) ≠ ∞ := (renewalMeasure_Ico_lt_top ρ hρ b).ne
  have : IsFiniteMeasure ((renewalMeasure ρ).restrict (Set.Ico 0 b)) :=
    isFiniteMeasure_restrict.2 hUb
  have hcG : ∀ c : ℝ, Continuous fun t => G (c + t) := fun c =>
    hGc.comp (continuous_const.add continuous_id)
  have hIG : ∀ c : ℝ, IntegrableOn (fun t => G (c + t)) (Set.Ico 0 b) (renewalMeasure ρ) :=
    fun c => intOn ρ hρ (hcG c) le_rfl
  have hIΨ : ∀ y : ℝ, IntegrableOn ((Set.Iio (2 * b - y)).indicator fun t => G (y + t))
      (Set.Ico 0 b) (renewalMeasure ρ) := fun y => (hIG y).indicator measurableSet_Iio
  obtain ⟨Φ, hΦ⟩ : ∃ Φ : ℝ → ℝ, Φ = fun υ => ∫ x in Set.Ico 0 b, G (υ + x) ∂(renewalMeasure ρ) :=
    ⟨_, rfl⟩
  obtain ⟨Ψ, hΨ⟩ : ∃ Ψ : ℝ → ℝ, Ψ = fun y => ∫ t in Set.Ico 0 b,
      (Set.Iio (2 * b - y)).indicator (fun t => G (y + t)) t ∂(renewalMeasure ρ) := ⟨_, rfl⟩
  -- `Φ` is continuous, so it attains its maximum on `[0, b]`
  obtain ⟨C, hC⟩ : ∃ C, ∀ x, |G x| ≤ C := by
    obtain ⟨C, hC⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := 2 * b)).exists_bound_of_continuousOn hgc
    refine ⟨C, fun x => ?_⟩
    have := hC _ (hPmem x)
    rw [Real.norm_eq_abs] at this
    rw [hG]
    exact this
  have hΦc : Continuous Φ := by
    rw [hΦ]
    exact continuous_of_dominated (bound := fun _ => C)
      (fun υ => (hcG υ).aestronglyMeasurable)
      (fun υ => ae_of_all _ fun x => by rw [Real.norm_eq_abs]; exact hC (υ + x))
      (integrable_const C) (ae_of_all _ fun x => hGc.comp (continuous_id.add continuous_const))
  obtain ⟨υs, hυs, hΦmaxOn⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := b)).exists_isMaxOn
    (Set.nonempty_Icc.2 hb.le) hΦc.continuousOn
  have hΦle : ∀ υ ∈ Set.Icc (0 : ℝ) b, Φ υ ≤ Φ υs := isMaxOn_iff.1 hΦmaxOn
  have hΦ0 : ∀ υ, 0 ≤ Φ υ := fun υ => by
    rw [hΦ]; exact setIntegral_nonneg measurableSet_Ico fun x _ => hG0 _
  have hmem0 : (0 : ℝ) ∈ Set.Icc 0 b := ⟨le_rfl, hb.le⟩
  have hmemb : b ∈ Set.Icc 0 b := ⟨hb.le, le_rfl⟩
  -- Step 2, middle case: `b ≤ y < 2b`, `y ≤ m`
  have hB : ∀ y, b ≤ y → y < 2 * b → y ≤ m → Φ 0 + Ψ y ≤ 2 * Φ υs := by
    intro y hy h2 hym
    have key : Φ 0 + Ψ y ≤ 2 * Φ (y / 2) := by
      simp only [hΦ, hΨ]
      calc (∫ x in Set.Ico 0 b, G (0 + x) ∂renewalMeasure ρ)
            + ∫ t in Set.Ico 0 b, (Set.Iio (2 * b - y)).indicator (fun t => G (y + t)) t
              ∂renewalMeasure ρ
          = ∫ t in Set.Ico 0 b, (G (0 + t)
              + (Set.Iio (2 * b - y)).indicator (fun t => G (y + t)) t) ∂renewalMeasure ρ :=
            (integral_add (hIG 0).integrable (hIΨ y).integrable).symm
        _ ≤ ∫ t in Set.Ico 0 b, 2 * G (y / 2 + t) ∂renewalMeasure ρ := by
            refine setIntegral_mono_on ((hIG 0).add (hIΨ y)) ((hIG (y / 2)).const_mul 2)
              measurableSet_Ico fun t ht => ?_
            rw [zero_add]
            by_cases ht2 : t < 2 * b - y
            · rw [Set.indicator_of_mem (Set.mem_Iio.2 ht2)]
              have := hmid t ⟨ht.1, by linarith [ht.2]⟩ (y + t) ⟨by linarith [ht.1], by linarith⟩
              rwa [show (t + (y + t)) / 2 = y / 2 + t by ring] at this
            · rw [Set.indicator_of_notMem (by simpa using ht2), add_zero]
              have hz0 : 0 ≤ y / 2 + t := by linarith [ht.1]
              have hz2 : y / 2 + t ≤ 2 * b := by linarith [ht.2, hm.2]
              have hGz := hG0 (y / 2 + t)
              rcases le_or_gt (y / 2 + t) m with hzm | hzm
              · have := hM1 t (y / 2 + t) ht.1 (by linarith) hzm
                linarith
              · have hm2b : m < 2 * b := lt_of_lt_of_le hzm hz2
                have hch := hchord (y / 2 + t) hzm.le hz2 hm2b
                have hGt : G t ≤ G m := hmax t ⟨ht.1, by linarith [ht.2]⟩
                have hzb : 2 * b - m ≤ 2 * (2 * b - (y / 2 + t)) := by linarith [ht.2]
                have h1 : (2 * b - m) * G t ≤ (2 * b - m) * G m :=
                  mul_le_mul_of_nonneg_left hGt (by linarith)
                have h2' : (2 * b - m) * G m ≤ 2 * (2 * b - (y / 2 + t)) * G m :=
                  mul_le_mul_of_nonneg_right hzb (hG0 m)
                have h3 : (2 * b - m) * G t ≤ (2 * b - m) * (2 * G (y / 2 + t)) := by linarith
                exact le_of_mul_le_mul_left h3 (by linarith)
        _ = 2 * ∫ t in Set.Ico 0 b, G (y / 2 + t) ∂renewalMeasure ρ := integral_const_mul _ _
    have := hΦle (y / 2) ⟨by linarith, by linarith⟩
    linarith
  -- Step 2: `Φ(0) + Ψ(y) ≤ 2 max Φ` for every `y ≥ b`
  have hclaim : ∀ y, b ≤ y → Φ 0 + Ψ y ≤ 2 * Φ υs := by
    intro y hy
    have h0 := hΦle 0 hmem0
    have hs0 := hΦ0 υs
    rcases le_or_gt (2 * b) y with h2 | h2
    · -- no partial sums of the fresh process land in `[b, 2b)`
      have hΨ0 : Ψ y = 0 := by
        rw [hΨ]
        simp only
        rw [setIntegral_congr_fun measurableSet_Ico (g := fun _ => (0 : ℝ)) fun t ht =>
          Set.indicator_of_notMem (by simp only [Set.mem_Iio, not_lt]; linarith [ht.1]) _,
          integral_zero]
      linarith
    rcases le_or_gt y m with hym | hym
    · exact hB y hy h2 hym
    rcases le_or_gt m b with hmb | hmb
    · -- `G` is nonincreasing on `[b, 2b]`: `Ψ(y) ≤ Φ(b)`
      have hle : Ψ y ≤ Φ b := by
        simp only [hΦ, hΨ]
        refine setIntegral_mono_on (hIΨ y) (hIG b) measurableSet_Ico fun t ht => ?_
        by_cases ht2 : t < 2 * b - y
        · rw [Set.indicator_of_mem (Set.mem_Iio.2 ht2)]
          exact hM2 (b + t) (y + t) (by linarith [ht.1]) (by linarith) (by linarith)
        · rw [Set.indicator_of_notMem (by simpa using ht2)]
          exact hG0 _
      have := hΦle b hmemb
      linarith
    · -- `G` is nonincreasing on `[m, 2b]`: `Ψ(y) ≤ Ψ(m)`, and `m` is a middle case
      have hle : Ψ y ≤ Ψ m := by
        simp only [hΨ]
        refine setIntegral_mono_on (hIΨ y) (hIΨ m) measurableSet_Ico fun t ht => ?_
        by_cases ht2 : t < 2 * b - y
        · rw [Set.indicator_of_mem (Set.mem_Iio.2 ht2),
            Set.indicator_of_mem (Set.mem_Iio.2 (by linarith))]
          exact hM2 (m + t) (y + t) (by linarith [ht.1]) (by linarith) (by linarith)
        · rw [Set.indicator_of_notMem (by simpa using ht2)]
          exact Set.indicator_nonneg (fun t _ => hG0 _) t
      have := hB m hmb.le (by linarith) le_rfl
      linarith
  -- Step 1: regeneration at the level `b`
  have hGm : Measurable fun x => ENNReal.ofReal (G x) := ENNReal.measurable_ofReal.comp hGc.measurable
  have hreg := renewal_regeneration ρ b ((Set.Ico b (2 * b)).indicator fun x => ENNReal.ofReal (G x))
    (hGm.indicator measurableSet_Ico)
  rw [lintegral_indicator measurableSet_Ico, Measure.restrict_restrict measurableSet_Ico,
    Set.inter_eq_left.2 Set.Ico_subset_Ici_self] at hreg
  have hae : ∀ᵐ t ∂(renewalMeasure ρ), 0 ≤ t := by
    have h := measure_eq_zero_iff_ae_notMem.1 (renewal_Iio_zero ρ)
    filter_upwards [h] with t ht
    simpa using ht
  have hRHS : ∀ y, b ≤ y → ∫⁻ t, (Set.Ico b (2 * b)).indicator (fun x => ENNReal.ofReal (G x))
      (y + t) ∂renewalMeasure ρ = ENNReal.ofReal (Ψ y) := by
    intro y hy
    rw [hΨ]
    simp only
    rw [ofReal_integral_eq_lintegral_ofReal (hIΨ y).integrable
      (ae_of_all _ fun t => Set.indicator_nonneg (fun t _ => hG0 _) t),
      ← lintegral_indicator measurableSet_Ico]
    refine lintegral_congr_ae ?_
    filter_upwards [hae] with t ht
    by_cases ht2 : t < 2 * b - y
    · have hm1 : y + t ∈ Set.Ico b (2 * b) := Set.mem_Ico.2 ⟨by linarith, by linarith⟩
      have hm2 : t ∈ Set.Ico 0 b := Set.mem_Ico.2 ⟨ht, by linarith⟩
      rw [Set.indicator_of_mem hm1, Set.indicator_of_mem hm2,
        Set.indicator_of_mem (Set.mem_Iio.2 ht2)]
    · rw [Set.indicator_of_notMem (fun h => ht2 (by linarith [h.2]))]
      by_cases ht3 : t ∈ Set.Ico 0 b
      · rw [Set.indicator_of_mem ht3, Set.indicator_of_notMem (by simpa using ht2),
          ENNReal.ofReal_zero]
      · rw [Set.indicator_of_notMem ht3]
  have hΦs0 := hΦle 0 hmem0
  have hbound : ∫⁻ x in Set.Ico b (2 * b), ENNReal.ofReal (G x) ∂renewalMeasure ρ
      ≤ ENNReal.ofReal (2 * Φ υs - Φ 0) := by
    refine hreg.trans (iSup₂_le fun y hy => ?_)
    rw [hRHS y hy]
    exact ENNReal.ofReal_le_ofReal (by linarith [hclaim y hy])
  have hupper : ∫ x in Set.Ico b (2 * b), G x ∂renewalMeasure ρ ≤ 2 * Φ υs - Φ 0 := by
    rw [integral_eq_lintegral_of_nonneg_ae (ae_of_all _ fun x => hG0 x)
      hGc.aestronglyMeasurable]
    exact ENNReal.toReal_le_of_le_ofReal (by linarith [hΦ0 υs]) hbound
  -- assemble: `∫_{[0,2b)} g dU = Φ(0) + ∫_{[b,2b)} G dU ≤ 2 Φ(υ*)`
  refine ⟨υs, hυs, ?_⟩
  have hsplit : ∫ x in Set.Ico 0 (2 * b), G x ∂renewalMeasure ρ
      = Φ 0 + ∫ x in Set.Ico b (2 * b), G x ∂renewalMeasure ρ := by
    rw [← Set.Ico_union_Ico_eq_Ico hb.le (by linarith : b ≤ 2 * b),
      setIntegral_union Set.Ico_disjoint_Ico_same measurableSet_Ico (intOn ρ hρ hGc le_rfl)
        (intOn ρ hρ hGc hb.le), hΦ]
    simp only [zero_add]
  have hlhs : ∫ x in Set.Ico 0 (2 * b), g x ∂renewalMeasure ρ
      = ∫ x in Set.Ico 0 (2 * b), G x ∂renewalMeasure ρ :=
    setIntegral_congr_fun measurableSet_Ico fun x hx =>
      (hGeq x (Set.Ico_subset_Icc_self hx)).symm
  have hrhs : ∫ x in Set.Ico 0 b, g (υs + x) ∂renewalMeasure ρ = Φ υs := by
    rw [hΦ]
    exact setIntegral_congr_fun measurableSet_Ico fun x hx =>
      (hGeq (υs + x) ⟨by linarith [hυs.1, hx.1], by linarith [hυs.2, hx.2]⟩).symm
  rw [hlhs, hrhs, hsplit]
  linarith
