-- Prove2me | solution 1 for OppReturns.Menu.proposition_4_bc
-- status  : ACCEPTED   (disprove)
-- author  : @kmehltretter82
-- created : 2026-11-09T19:30:19.6125+00:00
-- url     : https://prove2.me/submissions/d83e00ac-8dd5-4f67-bbe9-ecd22b2a89fd

import Mathlib
import Definitions.Def_OppReturns_Menu_Model

open MeasureTheory ProbabilityTheory Set

private noncomputable def unifDens (V : ℝ) : ℝ → ℝ :=
  Set.indicator (Set.Ioo 0 V) (fun _ => 1 / V)

private noncomputable def unifLaw (V : ℝ) : Measure ℝ :=
  volume.withDensity (fun x => ENNReal.ofReal (unifDens V x))

private lemma unifLaw_eq_smul (V : ℝ) :
    unifLaw V = ENNReal.ofReal (1 / V) • volume.restrict (Set.Ioo 0 V) := by
  ext s hs
  unfold unifLaw unifDens
  rw [withDensity_apply _ hs, Measure.smul_apply, Measure.restrict_apply hs, smul_eq_mul]
  have h1 : (fun x => ENNReal.ofReal (Set.indicator (Set.Ioo 0 V) (fun _ => 1 / V) x)) =
      Set.indicator (Set.Ioo 0 V) (fun _ => ENNReal.ofReal (1 / V)) := by
    ext x
    by_cases hx : x ∈ Set.Ioo 0 V <;> simp [hx]
  rw [h1, lintegral_indicator measurableSet_Ioo, Measure.restrict_restrict measurableSet_Ioo,
    lintegral_const, Measure.restrict_apply_univ, Set.inter_comm]

private lemma unifLaw_apply (V : ℝ) (s : Set ℝ) :
    unifLaw V s = ENNReal.ofReal (1 / V) * volume (s ∩ Set.Ioo 0 V) := by
  rw [unifLaw_eq_smul V, Measure.smul_apply, Measure.restrict_apply' measurableSet_Ioo, smul_eq_mul]

private lemma unifLaw_isProb (V : ℝ) (hV : 0 < V) : IsProbabilityMeasure (unifLaw V) := by
  refine ⟨?_⟩
  rw [unifLaw_apply V Set.univ, Set.univ_inter, Real.volume_Ioo, sub_zero,
    ← ENNReal.ofReal_mul (by positivity), one_div_mul_cancel hV.ne', ENNReal.ofReal_one]

private lemma unifLaw_fullSupport (V : ℝ) (hV : 0 < V) :
    OppReturns.Menu.FullSupport (unifLaw V) V := by
  refine ⟨?_, ?_⟩
  · rw [unifLaw_apply V]
    have hempty : (Set.Icc 0 V)ᶜ ∩ Set.Ioo 0 V = ∅ := by
      ext x
      simp only [Set.mem_inter_iff, Set.mem_compl_iff, Set.mem_Icc, Set.mem_Ioo,
        Set.mem_empty_iff_false, iff_false]
      rintro ⟨hnot, hx0, hxV⟩
      exact hnot ⟨hx0.le, hxV.le⟩
    rw [hempty, measure_empty, mul_zero]
  · intro a b ha hab hb
    rw [unifLaw_apply V]
    have hinter : Set.Ioo a b ∩ Set.Ioo 0 V = Set.Ioo a b :=
      Set.inter_eq_left.mpr (Set.Ioo_subset_Ioo ha hb)
    rw [hinter, Real.volume_Ioo]
    exact ENNReal.mul_pos
      (ENNReal.ofReal_pos.mpr (by positivity)).ne'
      (ENNReal.ofReal_pos.mpr (sub_pos.mpr hab)).ne'

private lemma unifLaw_Iic_toReal (V : ℝ) (hV : 0 < V) (x : ℝ) :
    (unifLaw V (Set.Iic x)).toReal =
      if x ≤ 0 then 0 else if x < V then x / V else 1 := by
  rw [unifLaw_apply V]
  split_ifs with hx0 hxV
  · have hempty : Set.Iic x ∩ Set.Ioo 0 V = ∅ := by
      ext y
      simp only [Set.mem_inter_iff, Set.mem_Iic, Set.mem_Ioo, Set.mem_empty_iff_false, iff_false]
      rintro ⟨hyx, hy0, _⟩
      linarith
    rw [hempty, measure_empty, mul_zero, ENNReal.toReal_zero]
  · have hx0' : 0 < x := not_le.mp hx0
    have hinter : Set.Iic x ∩ Set.Ioo 0 V = Set.Ioc 0 x := by
      ext y
      simp only [Set.mem_inter_iff, Set.mem_Iic, Set.mem_Ioo, Set.mem_Ioc]
      exact ⟨fun ⟨hyx, hy0, _⟩ => ⟨hy0, hyx⟩, fun ⟨hy0, hyx⟩ => ⟨hyx, hy0, hyx.trans_lt hxV⟩⟩
    rw [hinter, Real.volume_Ioc, sub_zero, ← ENNReal.ofReal_mul (by positivity),
      ENNReal.toReal_ofReal (by positivity)]
    ring
  · have hxV' : V ≤ x := not_lt.mp hxV
    have hinter : Set.Iic x ∩ Set.Ioo 0 V = Set.Ioo 0 V := by
      ext y
      simp only [Set.mem_inter_iff, Set.mem_Iic, Set.mem_Ioo]
      exact ⟨fun ⟨_, hy0, hyV⟩ => ⟨hy0, hyV⟩, fun ⟨hy0, hyV⟩ => ⟨hyV.le.trans hxV', hy0, hyV⟩⟩
    rw [hinter, Real.volume_Ioo, sub_zero, ← ENNReal.ofReal_mul (by positivity),
      one_div_mul_cancel hV.ne', ENNReal.ofReal_one, ENNReal.toReal_one]

private lemma unifLaw_Iio_toReal (V : ℝ) (hV : 0 < V) (x : ℝ) :
    (unifLaw V (Set.Iio x)).toReal =
      if x ≤ 0 then 0 else if x < V then x / V else 1 := by
  rw [unifLaw_apply V]
  split_ifs with hx0 hxV
  · have hempty : Set.Iio x ∩ Set.Ioo 0 V = ∅ := by
      ext y
      simp only [Set.mem_inter_iff, Set.mem_Iio, Set.mem_Ioo, Set.mem_empty_iff_false, iff_false]
      rintro ⟨hyx, hy0, _⟩
      linarith
    rw [hempty, measure_empty, mul_zero, ENNReal.toReal_zero]
  · have hx0' : 0 < x := not_le.mp hx0
    have hinter : Set.Iio x ∩ Set.Ioo 0 V = Set.Ioo 0 x := by
      ext y
      simp only [Set.mem_inter_iff, Set.mem_Iio, Set.mem_Ioo]
      exact ⟨fun ⟨hyx, hy0, _⟩ => ⟨hy0, hyx⟩, fun ⟨hy0, hyx⟩ => ⟨hyx, hy0, hyx.trans hxV⟩⟩
    rw [hinter, Real.volume_Ioo, sub_zero, ← ENNReal.ofReal_mul (by positivity),
      ENNReal.toReal_ofReal (by positivity)]
    ring
  · have hxV' : V ≤ x := not_lt.mp hxV
    have hinter : Set.Iio x ∩ Set.Ioo 0 V = Set.Ioo 0 V := by
      ext y
      simp only [Set.mem_inter_iff, Set.mem_Iio, Set.mem_Ioo]
      exact ⟨fun ⟨_, hy0, hyV⟩ => ⟨hy0, hyV⟩, fun ⟨hy0, hyV⟩ => ⟨hyV.trans_le hxV', hy0, hyV⟩⟩
    rw [hinter, Real.volume_Ioo, sub_zero, ← ENNReal.ofReal_mul (by positivity),
      one_div_mul_cancel hV.ne', ENNReal.ofReal_one, ENNReal.toReal_one]

private lemma unifLaw_cdf (V : ℝ) (hV : 0 < V) (x : ℝ) :
    cdf (unifLaw V) x = if x ≤ 0 then 0 else if x < V then x / V else 1 := by
  have hprob := unifLaw_isProb V hV
  rw [cdf_eq_real, Measure.real_def, unifLaw_Iic_toReal V hV x]

private lemma unifLaw_igfr (V : ℝ) (hV : 0 < V) :
    OppReturns.Menu.IGFR (unifLaw V) := by
  refine ⟨unifDens V, ⟨?_, rfl, ?_, ?_⟩, ?_⟩
  · intro x
    unfold unifDens
    by_cases hx : x ∈ Set.Ioo 0 V <;> simp [hx, hV.le]
  · intro ξ hpos hlt1
    rw [unifLaw_cdf V hV ξ] at hpos hlt1
    have hξ0 : 0 < ξ := by
      by_contra hle
      rw [if_pos (not_lt.mp hle)] at hpos
      exact lt_irrefl 0 hpos
    have hξV : ξ < V := by
      by_contra hge
      rw [if_neg (not_le.mpr hξ0), if_neg hge] at hlt1
      exact lt_irrefl 1 hlt1
    have hξ_mem : ξ ∈ Set.Ioo 0 V := ⟨hξ0, hξV⟩
    have hd_val : unifDens V ξ = 1 / V := Set.indicator_of_mem hξ_mem _
    rw [hd_val]
    have hev : (fun x => cdf (unifLaw V) x) =ᶠ[nhds ξ] (fun x => x / V) := by
      filter_upwards [Ioo_mem_nhds hξ0 hξV] with x hx
      rw [unifLaw_cdf V hV x, if_neg (not_le.mpr hx.1), if_pos hx.2]
    have hderiv : HasDerivAt (fun x : ℝ => x / V) (1 / V) ξ := by
      simpa using (hasDerivAt_id ξ).div_const V
    exact (hderiv.congr_of_eventuallyEq hev).hasDerivWithinAt
  · intro ξ h0
    rw [unifLaw_cdf V hV ξ] at h0
    have hξ0 : ξ ≤ 0 := by
      split_ifs at h0 with hle0 hltV
      · exact hle0
      · exfalso
        have hpos : 0 < ξ / V := div_pos (not_le.mp hle0) hV
        linarith
      · exfalso
        norm_num at h0
    have hnot : ξ ∉ Set.Ioo 0 V := fun h => by linarith [h.1]
    unfold unifDens
    simp [hnot]
  · intro x hx y hy hxy
    have hx1 : cdf (unifLaw V) x < 1 := hx
    have hy1 : cdf (unifLaw V) y < 1 := hy
    have hxV : x < V := by
      by_contra hge
      have hxV' : V ≤ x := not_lt.mp hge
      have hnot0 : ¬ x ≤ 0 := not_le.mpr (hV.trans_le hxV')
      rw [unifLaw_cdf V hV x, if_neg hnot0, if_neg hge] at hx1
      exact lt_irrefl 1 hx1
    have hyV : y < V := by
      by_contra hge
      have hyV' : V ≤ y := not_lt.mp hge
      have hnot0 : ¬ y ≤ 0 := not_le.mpr (hV.trans_le hyV')
      rw [unifLaw_cdf V hV y, if_neg hnot0, if_neg hge] at hy1
      exact lt_irrefl 1 hy1
    unfold LariviereIGFR.Char.genFailureRate LariviereIGFR.Char.failureRate
      LariviereIGFR.Char.survival
    by_cases hx0 : x ≤ 0
    · have hnotx : x ∉ Set.Ioo 0 V := fun h => by linarith [h.1]
      have hdx : unifDens V x = 0 := by simp [unifDens, hnotx]
      rw [hdx, zero_div, mul_zero]
      by_cases hy0 : y ≤ 0
      · have hnoty : y ∉ Set.Ioo 0 V := fun h => by linarith [h.1]
        have hdy : unifDens V y = 0 := by simp [unifDens, hnoty]
        rw [hdy, zero_div, mul_zero]
      · have hy0' : 0 < y := not_le.mp hy0
        have hmemy : y ∈ Set.Ioo 0 V := ⟨hy0', hyV⟩
        have hdy : unifDens V y = 1 / V := Set.indicator_of_mem hmemy _
        rw [hdy, unifLaw_cdf V hV y, if_neg hy0, if_pos hyV]
        have hsub : 0 < 1 - y / V := by
          rw [sub_pos, div_lt_one hV]
          exact hyV
        positivity
    · have hx0' : 0 < x := not_le.mp hx0
      have hy0' : 0 < y := hx0'.trans_le hxy
      have hy0 : ¬ y ≤ 0 := not_le.mpr hy0'
      have hmemx : x ∈ Set.Ioo 0 V := ⟨hx0', hxV⟩
      have hmemy : y ∈ Set.Ioo 0 V := ⟨hy0', hyV⟩
      have hdx : unifDens V x = 1 / V := Set.indicator_of_mem hmemx _
      have hdy : unifDens V y = 1 / V := Set.indicator_of_mem hmemy _
      rw [hdx, hdy, unifLaw_cdf V hV x, if_neg hx0, if_pos hxV,
        unifLaw_cdf V hV y, if_neg hy0, if_pos hyV]
      have hVx : 0 < V - x := sub_pos.mpr hxV
      have hVy : 0 < V - y := sub_pos.mpr hyV
      have h1 : x * (1 / V / (1 - x / V)) = x / (V - x) := by
        field_simp [hV.ne', hVx.ne']
      have h2 : y * (1 / V / (1 - y / V)) = y / (V - y) := by
        field_simp [hV.ne', hVy.ne']
      rw [h1, h2, div_le_div_iff₀ hVx hVy]
      nlinarith

private noncomputable def P_wit : OppReturns.Menu.Params where
  X := 1 / 2
  c := 1 / 2
  s := 1 / 4
  VL := 1
  VS := 40
  νL := unifLaw 1
  νS := unifLaw 40
  D := Measure.dirac 1

private lemma emax_P_wit_s : OppReturns.Menu.Emax P_wit P_wit.s = 17 / 32 := by
  unfold OppReturns.Menu.Emax P_wit
  dsimp
  rw [unifLaw_eq_smul 1, integral_smul_measure, ENNReal.toReal_ofReal (by norm_num),
    one_div_one, one_smul, ← MeasureTheory.integral_Ioc_eq_integral_Ioo,
    ← intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)]
  have hsplit : (∫ u in (0 : ℝ)..1, max u (1 / 4)) =
      (∫ u in (0 : ℝ)..(1 / 4), max u (1 / 4)) + (∫ u in (1 / 4 : ℝ)..1, max u (1 / 4)) := by
    refine (intervalIntegral.integral_add_adjacent_intervals ?_ ?_).symm
    · exact (continuous_id.max continuous_const).intervalIntegrable _ _
    · exact (continuous_id.max continuous_const).intervalIntegrable _ _
  rw [hsplit]
  have h1 : (∫ u in (0 : ℝ)..(1 / 4), max u (1 / 4)) = ∫ _ in (0 : ℝ)..(1 / 4), (1 / 4 : ℝ) := by
    refine intervalIntegral.integral_congr (fun u hu => ?_)
    rw [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1 / 4)] at hu
    exact max_eq_right hu.2
  have h2 : (∫ u in (1 / 4 : ℝ)..1, max u (1 / 4)) = ∫ u in (1 / 4 : ℝ)..1, u := by
    refine intervalIntegral.integral_congr (fun u hu => ?_)
    rw [Set.uIcc_of_le (by norm_num : (1 / 4 : ℝ) ≤ 1)] at hu
    exact max_eq_left hu.1
  rw [h1, h2, intervalIntegral.integral_const, integral_id]
  norm_num

private lemma emax_P_wit_20 : OppReturns.Menu.Emax P_wit 20 = 20 := by
  unfold OppReturns.Menu.Emax P_wit
  dsimp
  rw [unifLaw_eq_smul 1, integral_smul_measure, ENNReal.toReal_ofReal (by norm_num),
    one_div_one, one_smul, ← MeasureTheory.integral_Ioc_eq_integral_Ioo,
    ← intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)]
  have hcongr : (∫ u in (0 : ℝ)..1, max u 20) = ∫ _ in (0 : ℝ)..1, (20 : ℝ) := by
    refine intervalIntegral.integral_congr (fun u hu => ?_)
    rw [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at hu
    exact max_eq_right (by linarith [hu.2])
  rw [hcongr, intervalIntegral.integral_const]
  norm_num

private lemma standing_P_wit : OppReturns.Menu.Standing P_wit := by
  refine ⟨by norm_num [P_wit], by norm_num [P_wit], by norm_num [P_wit], by norm_num [P_wit],
    by norm_num [P_wit], by norm_num [P_wit], unifLaw_isProb 1 (by norm_num),
    unifLaw_isProb 40 (by norm_num), Measure.dirac.isProbabilityMeasure,
    unifLaw_fullSupport 1 (by norm_num), unifLaw_fullSupport 40 (by norm_num),
    unifLaw_igfr 1 (by norm_num), unifLaw_igfr 40 (by norm_num), ?_, ?_, ?_⟩
  · change Measure.dirac (1 : ℝ) (Set.Iic 0) = 0
    rw [Measure.dirac_apply' 1 measurableSet_Iic]
    simp
  · change Integrable (fun x : ℝ => x) (Measure.dirac 1)
    exact integrable_dirac (by simp)
  · rw [emax_P_wit_s]
    norm_num [P_wit]

private lemma expSales_dirac_one (q : ℝ) :
    SupplyChainTheory.expSales (Measure.dirac 1) q = min q 1 := by
  unfold SupplyChainTheory.expSales
  rw [integral_dirac]

private lemma feasT_20 : OppReturns.Menu.FeasT P_wit 1 20 0 20 := by
  refine ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num [P_wit], ?_⟩
  rw [emax_P_wit_20]
  norm_num

private lemma profitT_20 : OppReturns.Menu.profitT P_wit 1 20 0 20 = 19 / 4 := by
  unfold OppReturns.Menu.profitT OppReturns.Menu.profit OppReturns.Menu.Mt
    OppReturns.Menu.honestMargin OppReturns.Menu.Nf OppReturns.Menu.GSf OppReturns.Menu.GLf
  change ((1 / 2 : ℝ) * (20 - 0) * (1 - (unifLaw 40 (Set.Iio (20 - 0))).toReal) +
      (1 - 1 / 2) * ((20 - 1 / 4) - (20 - 1 / 4) * (unifLaw 1 (Set.Iio 20)).toReal)) *
      SupplyChainTheory.expSales (Measure.dirac 1)
        (1 / (1 - (1 / 2) * (unifLaw 40 (Set.Iio (20 - 0))).toReal)) -
      (1 / 2 - 1 / 4) * 1 = 19 / 4
  rw [unifLaw_Iio_toReal 40 (by norm_num) (20 - 0),
    unifLaw_Iio_toReal 1 (by norm_num) 20, expSales_dirac_one]
  norm_num

private lemma profitT_le_of_benchmark (Q rR : ℝ)
    (hFeas : OppReturns.Menu.FeasT P_wit Q (OppReturns.Menu.Emax P_wit P_wit.s) rR P_wit.s) :
    OppReturns.Menu.profitT P_wit Q (OppReturns.Menu.Emax P_wit P_wit.s) rR P_wit.s ≤ 17 / 32 := by
  rcases hFeas with ⟨hQ, hrR, _, hfr0, _, _⟩
  rw [emax_P_wit_s] at hfr0 ⊢
  have hs_eq : P_wit.s = 1 / 4 := rfl
  rw [hs_eq]
  unfold OppReturns.Menu.profitT OppReturns.Menu.profit
  have hGS_nonneg : 0 ≤ OppReturns.Menu.GSf P_wit (17 / 32 - rR) := ENNReal.toReal_nonneg
  have hGS_le_one : OppReturns.Menu.GSf P_wit (17 / 32 - rR) ≤ 1 := by
    change (unifLaw 40 (Set.Iio (17 / 32 - rR))).toReal ≤ 1
    rw [unifLaw_Iio_toReal 40 (by norm_num)]
    split_ifs with h1 h2
    · norm_num
    · exact (div_le_one (by norm_num)).mpr h2.le
    · norm_num
  have h1_sub_GS_nonneg : 0 ≤ 1 - OppReturns.Menu.GSf P_wit (17 / 32 - rR) := by linarith
  have h1_sub_GS_le_one : 1 - OppReturns.Menu.GSf P_wit (17 / 32 - rR) ≤ 1 := by linarith
  have hrenter_le : (17 / 32 - rR) * (1 - OppReturns.Menu.GSf P_wit (17 / 32 - rR)) ≤ 17 / 32 := by
    calc (17 / 32 - rR) * (1 - OppReturns.Menu.GSf P_wit (17 / 32 - rR))
      _ ≤ (17 / 32 - rR) * 1 := mul_le_mul_of_nonneg_left h1_sub_GS_le_one hfr0
      _ ≤ 17 / 32 := by linarith
  have hMt_nonneg : 0 ≤ OppReturns.Menu.Mt P_wit (17 / 32) rR (1 / 4) := by
    unfold OppReturns.Menu.Mt OppReturns.Menu.honestMargin
    have hX : P_wit.X = 1 / 2 := rfl
    have hs : P_wit.s = 1 / 4 := rfl
    rw [hX, hs]
    have hprod : 0 ≤ (17 / 32 - rR) * (1 - OppReturns.Menu.GSf P_wit (17 / 32 - rR)) :=
      mul_nonneg hfr0 h1_sub_GS_nonneg
    linarith
  have hMt_le : OppReturns.Menu.Mt P_wit (17 / 32) rR (1 / 4) ≤ 17 / 32 := by
    unfold OppReturns.Menu.Mt OppReturns.Menu.honestMargin
    have hX : P_wit.X = 1 / 2 := rfl
    have hs : P_wit.s = 1 / 4 := rfl
    rw [hX, hs]
    linarith
  have hexp_le :
      SupplyChainTheory.expSales P_wit.D (Q / OppReturns.Menu.Nf P_wit (17 / 32 - rR)) ≤ 1 := by
    change SupplyChainTheory.expSales (Measure.dirac 1)
      (Q / OppReturns.Menu.Nf P_wit (17 / 32 - rR)) ≤ 1
    rw [expSales_dirac_one]
    exact min_le_right _ _
  have hcost_nonneg : 0 ≤ (P_wit.c - P_wit.s) * Q := by
    have hc : P_wit.c = 1 / 2 := rfl
    have hs : P_wit.s = 1 / 4 := rfl
    rw [hc, hs]
    linarith
  calc OppReturns.Menu.Mt P_wit (17 / 32) rR (1 / 4) *
        SupplyChainTheory.expSales P_wit.D (Q / OppReturns.Menu.Nf P_wit (17 / 32 - rR)) -
        (P_wit.c - P_wit.s) * Q
    _ ≤ OppReturns.Menu.Mt P_wit (17 / 32) rR (1 / 4) * 1 - 0 := by
      linarith [mul_le_mul_of_nonneg_left hexp_le hMt_nonneg]
    _ ≤ 17 / 32 := by linarith

set_option linter.unusedVariables false in
theorem solution : ¬ (∀ (P : OppReturns.Menu.Params) (hS : OppReturns.Menu.Standing P),
    (∃ Q p rR rH, OppReturns.Menu.IsOptT P Q p rR rH) ∧
    ∀ Q p rR rH, OppReturns.Menu.IsOptT P Q p rR rH →
      p = OppReturns.Menu.Emax P P.s ∧ rH = P.s) := by
  intro hAll
  obtain ⟨⟨Q, p, rR, rH, hOpt⟩, huniq⟩ := hAll P_wit standing_P_wit
  obtain ⟨hp, hrH⟩ := huniq Q p rR rH hOpt
  subst hp
  subst hrH
  have hle := hOpt.2 1 20 0 20 feasT_20
  have hub := profitT_le_of_benchmark Q rR hOpt.1
  rw [profitT_20] at hle
  linarith
