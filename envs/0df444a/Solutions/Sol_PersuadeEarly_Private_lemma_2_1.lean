-- Prove2me | solution 1 for PersuadeEarly.Private.lemma_2_1
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-22T05:35:16.775532+00:00
-- url     : https://prove2.me/submissions/36220cc7-6181-4e12-93df-d08934ff03b6

import Mathlib
import Definitions.Def_PersuadeEarly_Private_Valuation
import Definitions.Def_PersuadeEarly_Private_Mechanism
import Definitions.Def_PersuadeEarly_Private_PrivateMech
import Definitions.Def_PersuadeEarly_Private_AppendixA


open MeasureTheory Set

namespace PersuadeEarly.Private.PEAux

variable {M : Model}

lemma f_nonneg (hM : M.Standing) : ∀ v ∈ Icc 0 M.b, 0 ≤ M.f v := by
  intro v hv
  rcases eq_or_lt_of_le hv.2 with h | h
  · subst h
    have hc : ContinuousWithinAt M.f (Ico 0 M.b) M.b :=
      (hM.f_cont M.b hv).mono Ico_subset_Icc_self
    have hne : (nhdsWithin M.b (Ico 0 M.b)).NeBot := by
      rw [← mem_closure_iff_nhdsWithin_neBot, closure_Ico hM.b_pos.ne]
      exact right_mem_Icc.2 hM.b_pos.le
    exact ge_of_tendsto hc (eventually_nhdsWithin_of_forall fun x hx => (hM.f_pos x hx).le)
  · exact (hM.f_pos v ⟨hv.1, h⟩).le

lemma f_intOn (hM : M.Standing) : IntegrableOn M.f (Icc 0 M.b) volume :=
  hM.f_cont.integrableOn_compact isCompact_Icc

theorem mu_finite (hM : M.Standing) : IsFiniteMeasure M.mu := by
  unfold Model.mu
  exact isFiniteMeasure_withDensity_ofReal (f_intOn hM).2

lemma integral_mu (hM : M.Standing) (g : ℝ → ℝ) :
    ∫ v, g v ∂M.mu = ∫ v in Icc 0 M.b, M.f v * g v := by
  unfold Model.mu
  rw [integral_withDensity_eq_integral_toReal_smul₀]
  · refine setIntegral_congr_fun measurableSet_Icc fun v hv => ?_
    simp [ENNReal.toReal_ofReal (f_nonneg hM v hv)]
  · exact ENNReal.measurable_ofReal.comp_aemeasurable
      (hM.f_cont.aemeasurable measurableSet_Icc)
  · exact Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top

/-- integral of a "threshold" integrand. -/
lemma integral_mu_ite (hM : M.Standing) (a : ℝ) (ha0 : 0 ≤ a) (hab : a ≤ M.b) (g : ℝ → ℝ) :
    ∫ v, (if a ≤ v then g v else 0) ∂M.mu = ∫ v in a..M.b, M.f v * g v := by
  rw [integral_mu hM]
  have : (fun v => M.f v * (if a ≤ v then g v else 0)) =
      (Ici a).indicator (fun v => M.f v * g v) := by
    ext v; by_cases h : a ≤ v <;> simp [h, indicator]
  have hs : Icc 0 M.b ∩ Ici a = Icc a M.b := by
    ext v; simp only [mem_inter_iff, mem_Icc, mem_Ici]
    constructor
    · rintro ⟨⟨_, h2⟩, h3⟩; exact ⟨h3, h2⟩
    · rintro ⟨h1, h2⟩; exact ⟨⟨ha0.trans h1, h2⟩, h1⟩
  rw [this, setIntegral_indicator measurableSet_Ici, hs,
    integral_Icc_eq_integral_Ioc, intervalIntegral.integral_of_le hab]

lemma Fbar_eq_integral (hM : M.Standing) (y : ℝ) (hy0 : 0 ≤ y) (hyb : y ≤ M.b) :
    M.Fbar y = ∫ v in y..M.b, M.f v := by
  unfold Model.Fbar
  have h1 : (M.mu (Ioi y)).toReal = ∫ v, (Ioi y).indicator 1 v ∂M.mu := by
    rw [integral_indicator_one measurableSet_Ioi]; rfl
  rw [h1, integral_mu hM]
  have : (fun v => M.f v * (Ioi y).indicator 1 v) = (Ioi y).indicator M.f := by
    ext v; by_cases h : y < v <;> simp [h, indicator]
  have hs : Icc 0 M.b ∩ Ioi y = Ioc y M.b := by
    ext v; simp only [mem_inter_iff, mem_Icc, mem_Ioi, mem_Ioc]
    constructor
    · rintro ⟨⟨_, h2⟩, h3⟩; exact ⟨h3, h2⟩
    · rintro ⟨h1, h2⟩; exact ⟨⟨hy0.trans h1.le, h2⟩, h1⟩
  rw [this, setIntegral_indicator measurableSet_Ioi, hs,
    intervalIntegral.integral_of_le hyb]

lemma Fbar_zero (hM : M.Standing) : M.Fbar 0 = 1 := by
  rw [Fbar_eq_integral hM 0 le_rfl hM.b_pos.le, hM.f_int]

lemma Fbar_b (hM : M.Standing) : M.Fbar M.b = 0 := by
  rw [Fbar_eq_integral hM _ hM.b_pos.le le_rfl, intervalIntegral.integral_same]

lemma Fbar_contOn (hM : M.Standing) : ContinuousOn M.Fbar (Icc 0 M.b) := by
  have h := intervalIntegral.continuousOn_primitive_interval_left (μ := volume)
    (a := 0) (b := M.b) (f := M.f) (by rw [uIcc_of_le hM.b_pos.le]; exact f_intOn hM)
  rw [uIcc_of_le hM.b_pos.le] at h
  exact h.congr fun y hy => Fbar_eq_integral hM y hy.1 hy.2

lemma f_intervalIntegrable (hM : M.Standing) {x y : ℝ} (hx : x ∈ Icc 0 M.b) (hy : y ∈ Icc 0 M.b) :
    IntervalIntegrable M.f volume x y :=
  (hM.f_cont.mono (uIcc_subset_Icc hx hy)).intervalIntegrable

lemma Fbar_sub (hM : M.Standing) {x y : ℝ} (hx : x ∈ Icc 0 M.b) (hy : y ∈ Icc 0 M.b) :
    M.Fbar x - M.Fbar y = ∫ v in x..y, M.f v := by
  rw [Fbar_eq_integral hM x hx.1 hx.2, Fbar_eq_integral hM y hy.1 hy.2]
  rw [sub_eq_iff_eq_add, intervalIntegral.integral_add_adjacent_intervals]
  · exact f_intervalIntegrable hM hx hy
  · exact f_intervalIntegrable hM hy ⟨hM.b_pos.le, le_rfl⟩

lemma Fbar_strictAnti (hM : M.Standing) : StrictAntiOn M.Fbar (Icc 0 M.b) := by
  intro x hx y hy hxy
  have := Fbar_sub hM hx hy
  have hpos : 0 < ∫ v in x..y, M.f v :=
    intervalIntegral.intervalIntegral_pos_of_pos_on (f_intervalIntegrable hM hx hy)
      (fun v hv => hM.f_pos v ⟨hx.1.trans hv.1.le, hv.2.trans_le hy.2⟩) hxy
  linarith

lemma Fbar_nonneg (y : ℝ) : 0 ≤ M.Fbar y := ENNReal.toReal_nonneg

lemma Fbar_le_one (hM : M.Standing) (y : ℝ) : M.Fbar y ≤ 1 := by
  have := mu_finite hM
  have h0 : M.Fbar 0 = 1 := Fbar_zero hM
  unfold Model.Fbar at h0 ⊢
  have hu : (M.mu (Ioi y)).toReal ≤ (M.mu univ).toReal :=
    ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono (subset_univ _))
  have hu2 : M.mu univ = M.mu (Ioi 0) := by
    unfold Model.mu
    rw [withDensity_apply _ MeasurableSet.univ, withDensity_apply _ measurableSet_Ioi,
      Measure.restrict_restrict measurableSet_Ioi, Measure.restrict_univ]
    apply setLIntegral_congr
    have hs : Icc 0 M.b ∩ Ioi 0 = Ioc 0 M.b := by
      ext v; simp only [mem_inter_iff, mem_Icc, mem_Ioi, mem_Ioc]
      constructor
      · rintro ⟨⟨_, h2⟩, h3⟩; exact ⟨h3, h2⟩
      · rintro ⟨h1, h2⟩; exact ⟨⟨h1.le, h2⟩, h1⟩
    rw [Set.inter_comm, hs]
    exact Ioc_ae_eq_Icc.symm
  rw [hu2] at hu; linarith

lemma Fbar_anti (hM : M.Standing) : Antitone M.Fbar := by
  have := mu_finite hM
  intro x y hxy
  unfold Model.Fbar
  exact ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono (Ioi_subset_Ioi hxy))

/-- `F̄^{-1}(q)` for `q ∈ (0,1)`. -/
lemma FbarInv_spec (hM : M.Standing) {q : ℝ} (hq0 : 0 < q) (hq1 : q < 1) :
    M.FbarInv q ∈ Ioo 0 M.b ∧ M.Fbar (M.FbarInv q) = q := by
  have hb := hM.b_pos.le
  obtain ⟨c, hc, hcq⟩ : ∃ c ∈ Icc 0 M.b, M.Fbar c = q := by
    have := intermediate_value_Icc' hb (Fbar_contOn hM)
    rw [Fbar_zero hM, Fbar_b hM] at this
    exact this ⟨hq0.le, hq1.le⟩
  have hleast : IsLeast {v ∈ Icc 0 M.b | M.Fbar v ≤ q} c := by
    refine ⟨⟨hc, hcq.le⟩, fun v hv => ?_⟩
    by_contra h
    push Not at h
    have := Fbar_strictAnti hM hv.1 hc h
    linarith [hv.2]
  have : M.FbarInv q = c := hleast.csInf_eq
  rw [this]
  refine ⟨⟨?_, ?_⟩, hcq⟩
  · rcases eq_or_lt_of_le hc.1 with h | h
    · rw [← h, Fbar_zero hM] at hcq; linarith
    · exact h
  · rcases eq_or_lt_of_le hc.2 with h | h
    · rw [h, Fbar_b hM] at hcq; linarith
    · exact h

lemma qL_lt_one_of (hM : M.Standing) (h : 0 < M.FbarInv M.qL) : M.qL < 1 := by
  by_contra hq
  push Not at hq
  have hmem : (0 : ℝ) ∈ {v ∈ Icc 0 M.b | M.Fbar v ≤ M.qL} :=
    ⟨left_mem_Icc.2 hM.b_pos.le, by rw [Fbar_zero hM]; exact hq⟩
  have : M.FbarInv M.qL ≤ 0 := csInf_le ⟨0, fun v hv => hv.1.1⟩ hmem
  linarith

end PersuadeEarly.Private.PEAux


open MeasureTheory Set Filter Topology

namespace PersuadeEarly.Private.PEAux

variable {M : Model}

lemma Fbar_hasDerivAt (hM : M.Standing) {s : ℝ} (hs : s ∈ Ioo 0 M.b) :
    HasDerivAt M.Fbar (-M.f s) s := by
  have hnhds : Icc 0 M.b ∈ 𝓝 s := Icc_mem_nhds hs.1 hs.2
  have hfc : ContinuousAt M.f s := hM.f_cont.continuousAt hnhds
  have h1 : HasDerivAt (fun u => ∫ v in u..M.b, M.f v) (-M.f s) s :=
    intervalIntegral.integral_hasDerivAt_left
      (f_intervalIntegrable hM ⟨hs.1.le, hs.2.le⟩ ⟨hM.b_pos.le, le_rfl⟩)
      ((hM.f_cont.mono Ioo_subset_Icc_self).stronglyMeasurableAtFilter isOpen_Ioo s hs) hfc
  refine h1.congr_of_eventuallyEq ?_
  filter_upwards [hnhds] with y hy
  exact Fbar_eq_integral hM y hy.1 hy.2

lemma Fbar_pos (hM : M.Standing) {s : ℝ} (hs0 : 0 ≤ s) (hsb : s < M.b) : 0 < M.Fbar s := by
  have := Fbar_strictAnti hM ⟨hs0, hsb.le⟩ ⟨hM.b_pos.le, le_rfl⟩ hsb
  rwa [Fbar_b hM] at this

lemma Fbar_ge_b (hM : M.Standing) {s : ℝ} (h : M.b ≤ s) : M.Fbar s = 0 := by
  have := Fbar_anti hM h
  rw [Fbar_b hM] at this
  exact le_antisymm this (Fbar_nonneg s)

lemma u_strictConvex (hM : M.Standing) :
    StrictConvexOn ℝ (Ico 0 M.b) (fun s => (M.Fbar s)⁻¹) := by
  apply StrictMonoOn.strictConvexOn_of_deriv (convex_Ico 0 M.b)
  · exact ((Fbar_contOn hM).mono Ico_subset_Icc_self).inv₀
      (fun s hs => (Fbar_pos hM hs.1 hs.2).ne')
  · rw [interior_Ico]
    have hd : ∀ s ∈ Ioo 0 M.b, deriv (fun s => (M.Fbar s)⁻¹) s =
        (M.f s / M.Fbar s) * (M.Fbar s)⁻¹ := by
      intro s hs
      have hD : HasDerivAt (fun y => (M.Fbar y)⁻¹) (-(-M.f s) / M.Fbar s ^ 2) s :=
        (Fbar_hasDerivAt hM hs).inv (Fbar_pos hM hs.1.le hs.2).ne'
      rw [hD.deriv]
      have := (Fbar_pos hM hs.1.le hs.2).ne'
      field_simp
    intro s hs s' hs' hss'
    rw [hd s hs, hd s' hs']
    have hFs := Fbar_pos hM hs.1.le hs.2
    have hFs' := Fbar_pos hM hs'.1.le hs'.2
    have hh : M.f s / M.Fbar s ≤ M.f s' / M.Fbar s' :=
      hM.hazard_mono ⟨hs.1.le, hs.2⟩ ⟨hs'.1.le, hs'.2⟩ hss'.le
    have hhpos : 0 < M.f s / M.Fbar s := div_pos (hM.f_pos s ⟨hs.1.le, hs.2⟩) hFs
    have hinv : (M.Fbar s)⁻¹ < (M.Fbar s')⁻¹ := by
      rw [inv_lt_inv₀ hFs hFs']
      exact Fbar_strictAnti hM ⟨hs.1.le, hs.2.le⟩ ⟨hs'.1.le, hs'.2.le⟩ hss'
    calc M.f s / M.Fbar s * (M.Fbar s)⁻¹ < M.f s / M.Fbar s * (M.Fbar s')⁻¹ :=
          mul_lt_mul_of_pos_left hinv hhpos
      _ ≤ M.f s' / M.Fbar s' * (M.Fbar s')⁻¹ :=
          mul_le_mul_of_nonneg_right hh (inv_nonneg.2 hFs'.le)

lemma le_FbarInv (hM : M.Standing) {q t : ℝ} (hq : 0 ≤ q) (ht : q < M.Fbar t) :
    t ≤ M.FbarInv q := by
  unfold Model.FbarInv
  apply le_csInf (show Set.Nonempty {v ∈ Icc 0 M.b | M.Fbar v ≤ q} from
    ⟨M.b, ⟨⟨hM.b_pos.le, le_rfl⟩, by rw [Fbar_b hM]; exact hq⟩⟩)
  intro v hv
  by_contra h
  push Not at h
  have := Fbar_anti hM h.le
  linarith [hv.2]

/-- The core estimate behind Lemma 2. -/
lemma phi_core (hM : M.Standing) (p : ℝ) (hp : p ∈ Icc 0 M.b) (t : ℝ) (hpt : p ≤ t) :
    phi M t p ≤ max ((M.FbarInv M.qL - p) * M.qL) 0 ∧
      (M.qL < M.Fbar p → t ≠ M.FbarInv M.qL → phi M t p < (M.FbarInv M.qL - p) * M.qL) := by
  have hqL := hM.qL_pos
  set p1 := M.FbarInv M.qL with hp1
  set x := M.Fbar t with hx
  set y := M.Fbar p with hy
  have hxy : x ≤ y := Fbar_anti hM hpt
  have hx0 : 0 ≤ x := Fbar_nonneg t
  have hy1 : y ≤ 1 := Fbar_le_one hM p
  -- facts valid when `qL < y`
  have hstrict_pre : M.qL < y → M.qL < 1 ∧ p < p1 ∧ 0 < (p1 - p) * M.qL := by
    intro hqy
    have hq1 : M.qL < 1 := lt_of_lt_of_le hqy hy1
    obtain ⟨⟨hp1pos, hp1b⟩, hFp1⟩ := FbarInv_spec hM hqL hq1
    have hpp1 : p < p1 := by
      by_contra h
      push Not at h
      have := Fbar_anti hM h
      rw [hp1, hFp1] at this
      linarith
    exact ⟨hq1, hpp1, mul_pos (by linarith) hqL⟩
  unfold phi
  rw [← hx, ← hy]
  rcases eq_or_lt_of_le hx0 with hx00 | hxpos
  · -- x = 0
    rw [← hx00]
    simp only [mul_zero, zero_mul]
    refine ⟨le_max_right _ _, fun hqy _ => (hstrict_pre hqy).2.2⟩
  have htb : t < M.b := by
    by_contra h
    push Not at h
    have := Fbar_ge_b hM h
    linarith
  have ht0 : 0 ≤ t := hp.1.trans hpt
  rcases lt_or_ge M.qL x with hqx | hxq
  · -- qL < x
    have htp1 : t ≤ p1 := le_FbarInv hM hqL.le hqx
    have e : (t - p) * x * (avail M.qL x - avail (max (M.qL - x) 0) (y - x)) =
        (t - p) * M.qL := by
      simp only [avail, if_neg (not_le.2 hqL), if_neg (not_le.2 hqx),
        max_eq_right (by linarith : M.qL - x ≤ 0), le_refl, if_true]
      field_simp
      simp
    rw [e]
    refine ⟨le_max_of_le_left (mul_le_mul_of_nonneg_right (by linarith) hqL.le),
      fun _ hne => mul_lt_mul_of_pos_right (by
        have := lt_of_le_of_ne htp1 hne; linarith) hqL⟩
  · -- x ≤ qL
    have ha1 : avail M.qL x = 1 := by
      simp only [avail, if_neg (not_le.2 hqL), if_pos hxq]
    rw [ha1]
    rcases eq_or_lt_of_le hxq with hxe | hxl
    · -- x = qL
      have ha2 : avail (max (M.qL - x) 0) (y - x) = 0 := by
        simp only [avail, hxe, sub_self, max_self, le_refl, if_true]
      rw [ha2, sub_zero, hxe]
      rcases lt_or_ge M.qL 1 with hq1 | hq1
      · obtain ⟨⟨hp1pos, hp1b⟩, hFp1⟩ := FbarInv_spec hM hqL hq1
        have htp : t = p1 := by
          by_contra hne
          rcases lt_or_gt_of_ne hne with h | h
          · have := Fbar_strictAnti hM ⟨ht0, htb.le⟩ ⟨hp1pos.le, hp1b.le⟩ h
            rw [hFp1] at this; linarith [hx]
          · have := Fbar_strictAnti hM ⟨hp1pos.le, hp1b.le⟩ ⟨ht0, htb.le⟩ h
            rw [hFp1] at this; linarith [hx]
        refine ⟨?_, fun _ hne => absurd htp hne⟩
        rw [htp, mul_one]; exact le_max_left _ _
      · -- qL = 1 forces t = 0
        have hq1' : M.qL = 1 := le_antisymm hM.qL_le_one hq1
        have ht00 : t = 0 := by
          by_contra hne
          have htpos : 0 < t := lt_of_le_of_ne ht0 (Ne.symm hne)
          have := Fbar_strictAnti hM ⟨le_rfl, hM.b_pos.le⟩ ⟨ht0, htb.le⟩ htpos
          rw [Fbar_zero hM] at this
          linarith
        have hp00 : p = 0 := le_antisymm (ht00 ▸ hpt) hp.1
        refine ⟨?_, fun hqy _ => by linarith⟩
        rw [ht00, hp00]; simp
    · -- x < qL
      by_cases hyq : y ≤ M.qL
      · have ha2 : avail (max (M.qL - x) 0) (y - x) = 1 := by
          simp only [avail, max_eq_left (by linarith : 0 ≤ M.qL - x),
            if_neg (not_le.2 (by linarith : (0:ℝ) < M.qL - x)), if_pos (by linarith : y - x ≤ M.qL - x)]
        rw [ha2]
        simp only [sub_self, mul_zero]
        exact ⟨le_max_right _ _, fun hqy _ => by linarith⟩
      · push Not at hyq
        obtain ⟨hq1, hpp1, hpos⟩ := hstrict_pre hyq
        obtain ⟨⟨hp1pos, hp1b⟩, hFp1⟩ := FbarInv_spec hM hqL hq1
        rw [← hp1] at hFp1 hp1pos hp1b
        have ha2 : avail (max (M.qL - x) 0) (y - x) = (M.qL - x) / (y - x) := by
          simp only [avail, max_eq_left (by linarith : 0 ≤ M.qL - x),
            if_neg (not_le.2 (by linarith : (0:ℝ) < M.qL - x)),
            if_neg (not_le.2 (by linarith : M.qL - x < y - x))]
        rw [ha2]
        have htp1 : p1 < t := by
          by_contra h
          push Not at h
          have := Fbar_anti hM h
          rw [hFp1] at this
          linarith
        have hconv := (u_strictConvex hM).secant_strict_mono_aux2 (x := p) (y := p1) (z := t)
          ⟨hp.1, hpp1.trans hp1b⟩ ⟨ht0, htb⟩ hpp1 htp1
        simp only [hFp1] at hconv
        rw [← hx, ← hy] at hconv
        have hy0 : 0 < y := by linarith
        have hd1 : 0 < p1 - p := by linarith
        have hd2 : 0 < t - p := by linarith
        have hyx : 0 < y - x := by linarith
        have key : (t - p) * x * (y - M.qL) < (p1 - p) * M.qL * (y - x) := by
          rw [div_lt_div_iff₀ hd1 hd2] at hconv
          have e1 : (M.qL⁻¹ - y⁻¹) = (y - M.qL) / (M.qL * y) := by field_simp
          have e2 : (x⁻¹ - y⁻¹) = (y - x) / (x * y) := by field_simp
          rw [e1, e2] at hconv
          rw [div_mul_eq_mul_div, div_mul_eq_mul_div, div_lt_div_iff₀ (by positivity)
            (by positivity)] at hconv
          nlinarith [mul_pos hxpos hy0, mul_pos hqL hy0, mul_pos hxpos hqL]
        have e : (t - p) * x * (1 - (M.qL - x) / (y - x)) = (t - p) * x * (y - M.qL) / (y - x) := by
          field_simp; ring
        rw [e]
        have hlt : (t - p) * x * (y - M.qL) / (y - x) < (p1 - p) * M.qL := by
          rw [div_lt_iff₀ hyx]; linarith
        exact ⟨le_max_of_le_left hlt.le, fun _ _ => hlt⟩

theorem lemma21 (M : Model) (hM : M.Standing) :
    ∀ p ∈ Icc 0 M.b, ∀ t, p ≤ t → phi M t p ≤ max ((M.FbarInv M.qL - p) * M.qL) 0 :=
  fun p hp t hpt => (phi_core hM p hp t hpt).1

theorem lemma22 (M : Model) (hM : M.Standing) :
    ∀ p ∈ Icc 0 M.b, M.qL < M.Fbar p →
      {t | p ≤ t ∧ ∀ s, p ≤ s → phi M s p ≤ phi M t p} = {M.FbarInv M.qL} := by
  intro p hp hqy
  have hqL := hM.qL_pos
  have hq1 : M.qL < 1 := lt_of_lt_of_le hqy (Fbar_le_one hM p)
  obtain ⟨⟨hp1pos, hp1b⟩, hFp1⟩ := FbarInv_spec hM hqL hq1
  have hpp1 : p < M.FbarInv M.qL := by
    by_contra h
    push Not at h
    have := Fbar_anti hM h
    rw [hFp1] at this
    linarith
  have hphi1 : phi M (M.FbarInv M.qL) p = (M.FbarInv M.qL - p) * M.qL := by
    unfold phi
    rw [hFp1]
    simp [avail, not_le.2 hqL]
  have hpos : 0 < (M.FbarInv M.qL - p) * M.qL := mul_pos (by linarith) hqL
  ext t
  simp only [mem_setOf_eq, mem_singleton_iff]
  constructor
  · rintro ⟨hpt, hmax⟩
    by_contra hne
    have h1 := (phi_core hM p hp t hpt).2 hqy hne
    have h2 := hmax _ hpp1.le
    rw [hphi1] at h2
    linarith
  · rintro rfl
    refine ⟨hpp1.le, fun s hs => ?_⟩
    rw [hphi1]
    have := (phi_core hM p hp s hs).1
    rwa [max_eq_left hpos.le] at this

end PersuadeEarly.Private.PEAux


open Set PersuadeEarly.Private in
theorem solution (M : Model) (hM : M.Standing) :
    ∀ p ∈ Icc 0 M.b, ∀ t, p ≤ t → phi M t p ≤ max ((M.FbarInv M.qL - p) * M.qL) 0 :=
  PersuadeEarly.Private.PEAux.lemma21 M hM
