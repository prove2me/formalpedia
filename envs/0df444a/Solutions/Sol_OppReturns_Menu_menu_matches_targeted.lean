-- Prove2me | solution 1 for OppReturns.Menu.menu_matches_targeted
-- status  : ACCEPTED   (disprove)
-- author  : @kmehltretter82
-- created : 2026-11-09T21:32:51.87838+00:00
-- url     : https://prove2.me/submissions/f76b79a6-dd6f-4426-99ab-c19266bc99bc

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

private lemma emax_P_wit (r : ℝ) (hr : 0 ≤ r) :
    OppReturns.Menu.Emax P_wit r = if r ≤ 1 then (1 + r ^ 2) / 2 else r := by
  unfold OppReturns.Menu.Emax P_wit
  dsimp
  rw [unifLaw_eq_smul 1, integral_smul_measure, ENNReal.toReal_ofReal (by norm_num),
    one_div_one, one_smul, ← MeasureTheory.integral_Ioc_eq_integral_Ioo,
    ← intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)]
  split_ifs with hr1
  · have hsplit : (∫ u in (0 : ℝ)..1, max u r) =
        (∫ u in (0 : ℝ)..r, max u r) + (∫ u in r..1, max u r) := by
      refine (intervalIntegral.integral_add_adjacent_intervals ?_ ?_).symm
      · exact (continuous_id.max continuous_const).intervalIntegrable _ _
      · exact (continuous_id.max continuous_const).intervalIntegrable _ _
    rw [hsplit]
    have h1 : (∫ u in (0 : ℝ)..r, max u r) = ∫ _ in (0 : ℝ)..r, r := by
      refine intervalIntegral.integral_congr (fun u hu => ?_)
      rw [Set.uIcc_of_le hr] at hu
      exact max_eq_right hu.2
    have h2 : (∫ u in r..1, max u r) = ∫ u in r..1, u := by
      refine intervalIntegral.integral_congr (fun u hu => ?_)
      rw [Set.uIcc_of_le hr1] at hu
      exact max_eq_left hu.1
    rw [h1, h2, intervalIntegral.integral_const, integral_id, smul_eq_mul]
    ring
  · have hcongr : (∫ u in (0 : ℝ)..1, max u r) = ∫ _ in (0 : ℝ)..1, r := by
      refine intervalIntegral.integral_congr (fun u hu => ?_)
      rw [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at hu
      exact max_eq_right (by linarith [hu.2])
    rw [hcongr, intervalIntegral.integral_const, smul_eq_mul]
    ring

private lemma emax_P_wit_s : OppReturns.Menu.Emax P_wit P_wit.s = 17 / 32 := by
  have hs : P_wit.s = 1 / 4 := rfl
  rw [hs, emax_P_wit (1 / 4) (by norm_num)]
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

private lemma GLf_P_wit (r : ℝ) :
    OppReturns.Menu.GLf P_wit r = if r ≤ 0 then 0 else if r < 1 then r else 1 := by
  change (unifLaw 1 (Set.Iio r)).toReal = _
  rw [unifLaw_Iio_toReal 1 (by norm_num) r]
  simp only [div_one]

private lemma GLf_P_wit_of_le_one {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r ≤ 1) :
    OppReturns.Menu.GLf P_wit r = r := by
  rw [GLf_P_wit]
  split_ifs with h1 h2
  · linarith
  · rfl
  · linarith

private lemma GLf_P_wit_of_gt_one {r : ℝ} (hr1 : 1 < r) :
    OppReturns.Menu.GLf P_wit r = 1 := by
  rw [GLf_P_wit, if_neg (by linarith), if_neg (by linarith)]

private lemma GSf_P_wit (f : ℝ) :
    OppReturns.Menu.GSf P_wit f = if f ≤ 0 then 0 else if f < 40 then f / 40 else 1 := by
  change (unifLaw 40 (Set.Iio f)).toReal = _
  rw [unifLaw_Iio_toReal 40 (by norm_num) f]

private lemma GSf_P_wit_of_mem {f : ℝ} (hf0 : 0 ≤ f) (hf40 : f ≤ 40) :
    OppReturns.Menu.GSf P_wit f = f / 40 := by
  rw [GSf_P_wit]
  split_ifs with h1 h2
  · linarith
  · rfl
  · linarith

private lemma honestMargin_le (p r : ℝ) (hr : 0 ≤ r) (hp : p ≤ OppReturns.Menu.Emax P_wit r) :
    OppReturns.Menu.honestMargin P_wit p r ≤ 9 / 32 := by
  unfold OppReturns.Menu.honestMargin
  have hs : P_wit.s = 1 / 4 := rfl
  rw [hs]
  rw [emax_P_wit r hr] at hp
  by_cases hr1 : r ≤ 1
  · rw [if_pos hr1] at hp
    rw [GLf_P_wit_of_le_one hr hr1]
    nlinarith [sq_nonneg (r - 1 / 4)]
  · rw [if_neg hr1] at hp
    rw [GLf_P_wit_of_gt_one (not_le.mp hr1)]
    linarith

private lemma emax_sub_le_half (r : ℝ) (hr : 0 ≤ r) :
    OppReturns.Menu.Emax P_wit r - r ≤ 1 / 2 := by
  rw [emax_P_wit r hr]
  split_ifs with hr1
  · nlinarith [mul_nonneg hr (by linarith : 0 ≤ 2 - r)]
  · linarith

private lemma feasT_opt :
    OppReturns.Menu.FeasT P_wit (479 / 640) (163 / 8) (1 / 4) (163 / 8) := by
  refine ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num [P_wit], ?_⟩
  rw [emax_P_wit (163 / 8) (by norm_num)]
  norm_num

private lemma profitT_opt :
    OppReturns.Menu.profitT P_wit (479 / 640) (163 / 8) (1 / 4) (163 / 8) = 24641 / 5120 := by
  unfold OppReturns.Menu.profitT OppReturns.Menu.profit OppReturns.Menu.Mt
    OppReturns.Menu.honestMargin OppReturns.Menu.Nf
  have hX : P_wit.X = 1 / 2 := rfl
  have hc : P_wit.c = 1 / 2 := rfl
  have hs : P_wit.s = 1 / 4 := rfl
  have hD : P_wit.D = Measure.dirac 1 := rfl
  rw [hX, hc, hs, hD, GSf_P_wit_of_mem (by norm_num) (by norm_num),
    GLf_P_wit_of_gt_one (by norm_num), expSales_dirac_one]
  norm_num

private lemma profitT_le_opt (Q p rR rH : ℝ)
    (hFeas : OppReturns.Menu.FeasT P_wit Q p rR rH) :
    OppReturns.Menu.profitT P_wit Q p rR rH ≤ 24641 / 5120 := by
  rcases hFeas with ⟨hQ, hrR, hrH, hfr0, hfrVS, hp_eq⟩
  have hVS : P_wit.VS = 40 := rfl
  rw [hVS] at hfrVS
  have hp : p = OppReturns.Menu.Emax P_wit rH := by linarith
  unfold OppReturns.Menu.profitT OppReturns.Menu.profit
  have hc : P_wit.c = 1 / 2 := rfl
  have hs : P_wit.s = 1 / 4 := rfl
  have hD : P_wit.D = Measure.dirac 1 := rfl
  rw [hc, hs, hD, expSales_dirac_one]
  have hGS : OppReturns.Menu.GSf P_wit (p - rR) = (p - rR) / 40 :=
    GSf_P_wit_of_mem hfr0 hfrVS
  have hNf : OppReturns.Menu.Nf P_wit (p - rR) = 1 - (p - rR) / 80 := by
    unfold OppReturns.Menu.Nf
    have hX : P_wit.X = 1 / 2 := rfl
    rw [hX, hGS]
    ring
  have hN_pos : 0 < OppReturns.Menu.Nf P_wit (p - rR) := by linarith
  by_cases hrH1 : rH ≤ 1
  · have hp_le_one : p ≤ 1 := by
      rw [hp, emax_P_wit rH hrH, if_pos hrH1]
      nlinarith [mul_nonneg hrH (by linarith : 0 ≤ 1 - rH)]
    have hf_le_one : p - rR ≤ 1 := by linarith
    have hhm : OppReturns.Menu.honestMargin P_wit p rH ≤ 9 / 32 :=
      honestMargin_le p rH hrH hp.le
    have hMt_le : OppReturns.Menu.Mt P_wit p rR rH ≤ 41 / 64 := by
      unfold OppReturns.Menu.Mt
      have hX : P_wit.X = 1 / 2 := rfl
      rw [hX, hGS]
      nlinarith
    have hmin_nonneg : 0 ≤ min (Q / OppReturns.Menu.Nf P_wit (p - rR)) 1 :=
      le_min (div_nonneg hQ hN_pos.le) (by norm_num)
    have hmin_le : min (Q / OppReturns.Menu.Nf P_wit (p - rR)) 1 ≤ 1 := min_le_right _ _
    by_cases hMt0 : 0 ≤ OppReturns.Menu.Mt P_wit p rR rH
    · have hmul : OppReturns.Menu.Mt P_wit p rR rH *
          min (Q / OppReturns.Menu.Nf P_wit (p - rR)) 1 ≤
          OppReturns.Menu.Mt P_wit p rR rH * 1 :=
        mul_le_mul_of_nonneg_left hmin_le hMt0
      linarith
    · have hmul : OppReturns.Menu.Mt P_wit p rR rH *
          min (Q / OppReturns.Menu.Nf P_wit (p - rR)) 1 ≤ 0 :=
        mul_nonpos_of_nonpos_of_nonneg (not_le.mp hMt0).le hmin_nonneg
      linarith
  · have hrH1' : 1 < rH := not_le.mp hrH1
    have hp_val : p = rH := by
      rw [hp, emax_P_wit rH hrH, if_neg hrH1]
    have hhm0 : OppReturns.Menu.honestMargin P_wit p rH = 0 := by
      unfold OppReturns.Menu.honestMargin
      have hs' : P_wit.s = 1 / 4 := rfl
      rw [hs', hp_val, GLf_P_wit_of_gt_one hrH1']
      ring
    have hMt_eq : OppReturns.Menu.Mt P_wit p rR rH = (1 / 2) * (p - rR) * (1 - (p - rR) / 40) := by
      unfold OppReturns.Menu.Mt
      have hX : P_wit.X = 1 / 2 := rfl
      rw [hX, hGS, hhm0]
      ring
    have hMt_nonneg : 0 ≤ OppReturns.Menu.Mt P_wit p rR rH := by
      rw [hMt_eq]
      nlinarith
    have hdiff_le : OppReturns.Menu.Mt P_wit p rR rH -
        (1 / 4) * OppReturns.Menu.Nf P_wit (p - rR) ≤ 24641 / 5120 := by
      rw [hMt_eq, hNf]
      nlinarith [sq_nonneg (p - rR - 161 / 8)]
    by_cases hQN : Q ≤ OppReturns.Menu.Nf P_wit (p - rR)
    · have hmin_le : min (Q / OppReturns.Menu.Nf P_wit (p - rR)) 1 ≤
          Q / OppReturns.Menu.Nf P_wit (p - rR) := min_le_left _ _
      have hQN0 : 0 ≤ Q / OppReturns.Menu.Nf P_wit (p - rR) := div_nonneg hQ hN_pos.le
      have hQN1 : Q / OppReturns.Menu.Nf P_wit (p - rR) ≤ 1 := (div_le_one hN_pos).mpr hQN
      have hQ_eq : Q = (Q / OppReturns.Menu.Nf P_wit (p - rR)) * OppReturns.Menu.Nf P_wit (p - rR) :=
        (div_mul_cancel₀ Q hN_pos.ne').symm
      have h1 : OppReturns.Menu.Mt P_wit p rR rH *
          min (Q / OppReturns.Menu.Nf P_wit (p - rR)) 1 - (1 / 2 - 1 / 4) * Q ≤
          (Q / OppReturns.Menu.Nf P_wit (p - rR)) *
            (OppReturns.Menu.Mt P_wit p rR rH - (1 / 4) * OppReturns.Menu.Nf P_wit (p - rR)) := by
        have hmul := mul_le_mul_of_nonneg_left hmin_le hMt_nonneg
        linarith
      have h2 : (Q / OppReturns.Menu.Nf P_wit (p - rR)) *
          (OppReturns.Menu.Mt P_wit p rR rH - (1 / 4) * OppReturns.Menu.Nf P_wit (p - rR)) ≤
          (Q / OppReturns.Menu.Nf P_wit (p - rR)) * (24641 / 5120) :=
        mul_le_mul_of_nonneg_left hdiff_le hQN0
      linarith
    · have hmin_le : min (Q / OppReturns.Menu.Nf P_wit (p - rR)) 1 ≤ 1 := min_le_right _ _
      have hmul := mul_le_mul_of_nonneg_left hmin_le hMt_nonneg
      linarith

private lemma isOptT_wit :
    OppReturns.Menu.IsOptT P_wit (479 / 640) (163 / 8) (1 / 4) (163 / 8) := by
  refine ⟨feasT_opt, fun Q' p' rR' rH' hFeas => ?_⟩
  rw [profitT_opt]
  exact profitT_le_opt Q' p' rR' rH' hFeas

private lemma feasM_wit :
    OppReturns.Menu.FeasM P_wit 0 (17 / 32) (1 / 4) (17 / 32) (1 / 4) := by
  refine ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, ?_, ?_⟩
  · have he : OppReturns.Menu.Emax P_wit (1 / 4) = 17 / 32 := emax_P_wit_s
    rw [he]
    norm_num
  · norm_num [P_wit]

private lemma profitM_le_one (Q pH rH pR rR : ℝ)
    (hFeas : OppReturns.Menu.FeasM P_wit Q pH rH pR rR) :
    OppReturns.Menu.profitM P_wit Q pH rH pR rR ≤ 1 := by
  rcases hFeas with ⟨hQ, hrH, hrR, hrHpH, hrRpR, hIC, hfee⟩
  have hpH_le : pH ≤ OppReturns.Menu.Emax P_wit rH := by
    have h0 : 0 ≤ max (OppReturns.Menu.Emax P_wit rR - pR) 0 := le_max_right _ _
    linarith
  have hfee_le_H : pR - rR ≤ pH - rH := le_trans hfee (min_le_left _ _)
  have hfee_le_half : pR - rR ≤ 1 / 2 := by
    have hsub := emax_sub_le_half rH hrH
    linarith
  have hfee_nonneg : 0 ≤ pR - rR := by linarith
  have hGS : OppReturns.Menu.GSf P_wit (pR - rR) = (pR - rR) / 40 :=
    GSf_P_wit_of_mem hfee_nonneg (by linarith)
  have hhm : OppReturns.Menu.honestMargin P_wit pH rH ≤ 9 / 32 :=
    honestMargin_le pH rH hrH hpH_le
  have hMm_le : OppReturns.Menu.Mm P_wit pR rR pH rH ≤ 1 := by
    unfold OppReturns.Menu.Mm
    have hX : P_wit.X = 1 / 2 := rfl
    rw [hX, hGS]
    nlinarith
  have hNf : OppReturns.Menu.Nf P_wit (pR - rR) = 1 - (pR - rR) / 80 := by
    unfold OppReturns.Menu.Nf
    have hX : P_wit.X = 1 / 2 := rfl
    rw [hX, hGS]
    ring
  have hN_pos : 0 < OppReturns.Menu.Nf P_wit (pR - rR) := by linarith
  unfold OppReturns.Menu.profitM OppReturns.Menu.profit
  have hc : P_wit.c = 1 / 2 := rfl
  have hs : P_wit.s = 1 / 4 := rfl
  have hD : P_wit.D = Measure.dirac 1 := rfl
  rw [hc, hs, hD, expSales_dirac_one]
  have hmin_nonneg : 0 ≤ min (Q / OppReturns.Menu.Nf P_wit (pR - rR)) 1 :=
    le_min (div_nonneg hQ hN_pos.le) (by norm_num)
  have hmin_le : min (Q / OppReturns.Menu.Nf P_wit (pR - rR)) 1 ≤ 1 := min_le_right _ _
  by_cases hMm0 : 0 ≤ OppReturns.Menu.Mm P_wit pR rR pH rH
  · have hmul := mul_le_mul_of_nonneg_left hmin_le hMm0
    linarith
  · have hmul := mul_nonpos_of_nonpos_of_nonneg (not_le.mp hMm0).le hmin_nonneg
    linarith

private lemma piM_le_one : OppReturns.Menu.PiM P_wit ≤ 1 := by
  unfold OppReturns.Menu.PiM
  refine csSup_le ?_ ?_
  · exact ⟨_, ⟨0, 17 / 32, 1 / 4, 17 / 32, 1 / 4, feasM_wit, rfl⟩⟩
  · rintro π ⟨Q, pH, rH, pR, rR, hFeas, rfl⟩
    exact profitM_le_one Q pH rH pR rR hFeas

private lemma piT_ge_opt : 24641 / 5120 ≤ OppReturns.Menu.PiT P_wit := by
  unfold OppReturns.Menu.PiT
  refine le_csSup ?_ ?_
  · refine ⟨24641 / 5120, ?_⟩
    rintro π ⟨Q, p, rR, rH, hFeas, rfl⟩
    exact profitT_le_opt Q p rR rH hFeas
  · exact ⟨479 / 640, 163 / 8, 1 / 4, 163 / 8, feasT_opt, profitT_opt.symm⟩

set_option linter.unusedVariables false in
theorem solution : ¬ (∀ (P : OppReturns.Menu.Params) (hS : OppReturns.Menu.Standing P)
    (Q p rR rH : ℝ) (hT : OppReturns.Menu.IsOptT P Q p rR rH) (hR : P.s ≤ rR),
    OppReturns.Menu.PiM P = OppReturns.Menu.PiT P) := by
  intro hAll
  have heq := hAll P_wit standing_P_wit (479 / 640) (163 / 8) (1 / 4) (163 / 8)
    isOptT_wit (by norm_num [P_wit])
  have hM := piM_le_one
  have hT := piT_ge_opt
  linarith
