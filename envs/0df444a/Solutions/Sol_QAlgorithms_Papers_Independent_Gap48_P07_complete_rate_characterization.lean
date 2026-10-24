-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Gap48.P07.complete_rate_characterization
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-23T13:54:44.141266+00:00
-- url     : https://prove2.me/submissions/e4c61177-1758-4d63-b582-fa6a348d6b06

import Definitions.Def_QAlgorithms_Papers_Independent_Gap48_P07

open Set Filter MeasureTheory
open scoped Topology

noncomputable section
namespace X7R

def mt (m : ℝ → ℝ) (s : ℝ) : ℝ := if 0 < s then m s else 0
def G (m : ℝ → ℝ) (t : ℝ) : ℝ := ∫ s in Ioi t, m s
def P (m : ℝ → ℝ) (t : ℝ) : ℝ := ∫ s in Ioc 0 t, s * m s
def F (m : ℝ → ℝ) (t : ℝ) : ℝ := ∫ s, min s t * mt m s

structure Hyp (m : ℝ → ℝ) : Prop where
  cont : ContinuousOn m (Ioi 0)
  nonneg : ∀ s, 0 < s → 0 ≤ m s
  int0 : IntegrableOn (fun s => s * m s) (Ioc 0 1)
  int1 : IntegrableOn m (Ioi 1)

variable {m : ℝ → ℝ}

lemma mt_eq (m : ℝ → ℝ) : mt m = (Ioi (0:ℝ)).piecewise m 0 := by
  funext s; simp only [mt, Set.piecewise, mem_Ioi]; split_ifs <;> rfl

lemma mt_meas (hm : Hyp m) : Measurable (mt m) := by
  classical
  rw [mt_eq]
  exact ContinuousOn.measurable_piecewise hm.cont continuousOn_const measurableSet_Ioi

lemma mt_nonneg (hm : Hyp m) (s : ℝ) : 0 ≤ mt m s := by
  unfold mt; split_ifs with h
  · exact hm.nonneg s h
  · exact le_rfl

lemma intOn_Icc (hm : Hyp m) {a b : ℝ} (ha : 0 < a) : IntegrableOn m (Icc a b) :=
  (hm.cont.mono (fun x hx => lt_of_lt_of_le ha hx.1)).integrableOn_compact isCompact_Icc

lemma intOn_Icc' (hm : Hyp m) {a b : ℝ} (ha : 0 < a) : IntegrableOn (fun s => s * m s) (Icc a b) :=
  ((continuousOn_id.mul hm.cont).mono (fun x hx => lt_of_lt_of_le ha hx.1)).integrableOn_compact isCompact_Icc

lemma intOn_Ioi (hm : Hyp m) {t : ℝ} (ht : 0 < t) : IntegrableOn m (Ioi t) := by
  rcases le_total 1 t with h | h
  · exact hm.int1.mono_set (Ioi_subset_Ioi h)
  · have : Ioi t = Ioc t 1 ∪ Ioi 1 := (Ioc_union_Ioi_eq_Ioi h).symm
    rw [this]
    exact ((intOn_Icc hm ht).mono_set Ioc_subset_Icc_self).union hm.int1

lemma intOn_sm (hm : Hyp m) {t : ℝ} (ht : 0 < t) : IntegrableOn (fun s => s * m s) (Ioc 0 t) := by
  rcases le_total t 1 with h | h
  · exact hm.int0.mono_set (Ioc_subset_Ioc_right h)
  · have : Ioc 0 t = Ioc 0 1 ∪ Ioc 1 t := (Ioc_union_Ioc_eq_Ioc zero_le_one h).symm
    rw [this]
    exact hm.int0.union ((intOn_Icc' hm one_pos).mono_set Ioc_subset_Icc_self)

lemma G_eq (hm : Hyp m) {t : ℝ} (ht : 0 < t) : G m t = G m 1 + ∫ s in t..1, m s := by
  have := intervalIntegral.integral_Ioi_sub_Ioi' (intOn_Ioi hm ht) (intOn_Ioi hm one_pos)
  unfold G; linarith

lemma G_nonneg (hm : Hyp m) {t : ℝ} (ht : 0 ≤ t) : 0 ≤ G m t :=
  setIntegral_nonneg measurableSet_Ioi (fun s hs => hm.nonneg s (lt_of_le_of_lt ht hs))

lemma hasDerivAt_G (hm : Hyp m) {t : ℝ} (ht : 0 < t) : HasDerivAt (G m) (-m t) t := by
  have hii : IntervalIntegrable m volume t 1 := by
    rcases le_total t 1 with h | h
    · exact (intervalIntegrable_iff_integrableOn_Icc_of_le h).mpr (intOn_Icc hm ht)
    · exact ((intervalIntegrable_iff_integrableOn_Icc_of_le h).mpr (intOn_Icc hm one_pos)).symm
  have hd := intervalIntegral.integral_hasDerivAt_left hii
    (hm.cont.stronglyMeasurableAtFilter isOpen_Ioi t ht) (hm.cont.continuousAt (Ioi_mem_nhds ht))
  have hd2 := hd.const_add (G m 1)
  refine hd2.congr_of_eventuallyEq ?_
  filter_upwards [Ioi_mem_nhds ht] with u hu
  exact G_eq hm hu

lemma P_eq (hm : Hyp m) {t : ℝ} (ht : 0 < t) : P m t = P m 1 - ∫ s in t..1, s * m s := by
  have h1 : P m t = ∫ s in (0:ℝ)..t, s * m s := by
    rw [intervalIntegral.integral_of_le ht.le]; rfl
  have h2 : P m 1 = ∫ s in (0:ℝ)..1, s * m s := by
    rw [intervalIntegral.integral_of_le zero_le_one]; rfl
  have i1 : IntervalIntegrable (fun s => s * m s) volume 0 t :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le ht.le).mpr (intOn_sm hm ht)
  have i2 : IntervalIntegrable (fun s => s * m s) volume t 1 := by
    rcases le_total t 1 with h | h
    · exact (intervalIntegrable_iff_integrableOn_Icc_of_le h).mpr (intOn_Icc' hm ht)
    · exact ((intervalIntegrable_iff_integrableOn_Icc_of_le h).mpr (intOn_Icc' hm one_pos)).symm
  have := intervalIntegral.integral_add_adjacent_intervals i1 i2
  rw [h1, h2]; linarith

lemma hasDerivAt_P (hm : Hyp m) {t : ℝ} (ht : 0 < t) : HasDerivAt (P m) (t * m t) t := by
  have hii : IntervalIntegrable (fun s => s * m s) volume t 1 := by
    rcases le_total t 1 with h | h
    · exact (intervalIntegrable_iff_integrableOn_Icc_of_le h).mpr (intOn_Icc' hm ht)
    · exact ((intervalIntegrable_iff_integrableOn_Icc_of_le h).mpr (intOn_Icc' hm one_pos)).symm
  have hc : ContinuousOn (fun s => s * m s) (Ioi 0) := continuousOn_id.mul hm.cont
  have hd := intervalIntegral.integral_hasDerivAt_left hii
    (hc.stronglyMeasurableAtFilter isOpen_Ioi t ht) (hc.continuousAt (Ioi_mem_nhds ht))
  have hd2 := hd.const_sub (P m 1)
  rw [neg_neg] at hd2
  refine hd2.congr_of_eventuallyEq ?_
  filter_upwards [Ioi_mem_nhds ht] with u hu
  exact P_eq hm hu

lemma F_pieces (hm : Hyp m) {t : ℝ} (ht : 0 < t) :
    IntegrableOn (fun s => min s t * mt m s) (Iic 0) ∧
    IntegrableOn (fun s => min s t * mt m s) (Ioc 0 t) ∧
    IntegrableOn (fun s => min s t * mt m s) (Ioi t) ∧
    (∫ s in Iic 0, min s t * mt m s) = 0 ∧
    (∫ s in Ioc 0 t, min s t * mt m s) = P m t ∧
    (∫ s in Ioi t, min s t * mt m s) = t * G m t := by
  have e0 : EqOn (fun s => min s t * mt m s) (fun _ => (0:ℝ)) (Iic 0) := by
    intro s hs; simp [mt, not_lt.mpr (show s ≤ 0 from hs)]
  have e1 : EqOn (fun s => min s t * mt m s) (fun s => s * m s) (Ioc 0 t) := by
    intro s hs; simp [mt, hs.1, min_eq_left hs.2]
  have e2 : EqOn (fun s => min s t * mt m s) (fun s => t * m s) (Ioi t) := by
    intro s hs
    have hs' : 0 < s := lt_trans ht hs
    simp [mt, hs', min_eq_right (le_of_lt (show t < s from hs))]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact (integrableOn_congr_fun e0 measurableSet_Iic).mpr integrableOn_zero
  · exact (integrableOn_congr_fun e1 measurableSet_Ioc).mpr (intOn_sm hm ht)
  · exact (integrableOn_congr_fun e2 measurableSet_Ioi).mpr ((intOn_Ioi hm ht).const_mul t)
  · rw [setIntegral_congr_fun measurableSet_Iic e0]; simp
  · rw [setIntegral_congr_fun measurableSet_Ioc e1]; rfl
  · rw [setIntegral_congr_fun measurableSet_Ioi e2, integral_const_mul]; rfl

lemma F_int (hm : Hyp m) {t : ℝ} (ht : 0 < t) : Integrable (fun s => min s t * mt m s) := by
  obtain ⟨i0, i1, i2, -, -, -⟩ := F_pieces hm ht
  have : (univ : Set ℝ) = (Iic 0 ∪ Ioc 0 t) ∪ Ioi t := by
    rw [Iic_union_Ioc_eq_Iic ht.le, Iic_union_Ioi]
  rw [← integrableOn_univ, this]
  exact (i0.union i1).union i2

lemma F_eq (hm : Hyp m) {t : ℝ} (ht : 0 < t) : F m t = P m t + t * G m t := by
  obtain ⟨i0, i1, i2, e0, e1, e2⟩ := F_pieces hm ht
  unfold F
  rw [← intervalIntegral.integral_Iic_add_Ioi (i0.union i1 |>.mono_set (by rw [Iic_union_Ioc_eq_Iic ht.le])) i2, e2]
  rw [← Iic_union_Ioc_eq_Iic ht.le, setIntegral_union (Set.disjoint_left.mpr fun x hx hx' => by
    exact absurd hx (not_le.mpr hx'.1)) measurableSet_Ioc i0 i1, e0, e1, zero_add]

lemma F_lim (hm : Hyp m) : Tendsto (F m) (𝓝[>] 0) (𝓝 0) := by
  have hb := F_int hm one_pos
  have key := tendsto_integral_filter_of_dominated_convergence (μ := volume) (l := 𝓝[>] (0:ℝ))
    (F := fun t s => min s t * mt m s) (f := fun _ => (0:ℝ)) (fun s => min s 1 * mt m s) ?_ ?_ hb ?_
  · have hF : F m = fun t => ∫ s, min s t * mt m s := rfl
    rw [hF]; simpa using key
  · exact Eventually.of_forall fun t =>
      ((continuous_id.min continuous_const).measurable.mul (mt_meas hm)).aestronglyMeasurable
  · filter_upwards [Ioo_mem_nhdsGT (show (0:ℝ) < 1 from one_pos)] with t ht
    refine Eventually.of_forall fun s => ?_
    rw [Real.norm_eq_abs]
    by_cases hs : 0 < s
    · have h1 : 0 ≤ min s t := le_min hs.le ht.1.le
      rw [abs_of_nonneg (mul_nonneg h1 (mt_nonneg hm s))]
      exact mul_le_mul_of_nonneg_right (min_le_min_left s ht.2.le) (mt_nonneg hm s)
    · simp [mt, hs]
  · refine Eventually.of_forall fun s => ?_
    by_cases hs : 0 < s
    · have : Tendsto (fun t => min s t * mt m s) (𝓝[>] 0) (𝓝 (min s 0 * mt m s)) :=
        ((continuous_const.min continuous_id).tendsto 0 |>.mono_left nhdsWithin_le_nhds).mul_const _
      rwa [min_eq_right hs.le, zero_mul] at this
    · simp [mt, hs]

end X7R


open Set Filter MeasureTheory
open scoped Topology ContDiff

noncomputable section
namespace X7R

open QAlgorithms.Papers.Independent.Gap48.P07
open QAlgorithms.Papers.Independent.Renew46.P11 (Bernstein CompletelyMonotone)

lemma eqOn_iteratedDeriv {f g : ℝ → ℝ} {s : Set ℝ} (hs : IsOpen s) (h : EqOn f g s) (k : ℕ) :
    EqOn (iteratedDeriv k f) (iteratedDeriv k g) s := by
  intro x hx
  have he : f =ᶠ[𝓝 x] g := Filter.eventually_of_mem (hs.mem_nhds hx) h
  exact (he.iteratedDeriv k).eq_of_nhds

lemma mt_meas' {m : ℝ → ℝ} (hc : ContinuousOn m (Ioi 0)) : Measurable (mt m) := by
  classical
  rw [mt_eq]
  exact ContinuousOn.measurable_piecewise hc continuousOn_const measurableSet_Ioi

/-- From complete Bernstein data, the density satisfies `Hyp` and `t * rate = a t/2 + b + F t`. -/
lemma cb_data (g : BernsteinData) (m : ℝ → ℝ) (hm : CompletelyMonotone m)
    (hmu : g.mu = volume.withDensity (fun s => ENNReal.ofReal (mt m s))) :
    Hyp m ∧ ∀ t, 0 < t → t * bernsteinRate g t = g.a / 2 * t + g.b + F m t := by
  have hc : ContinuousOn m (Ioi 0) := hm.1.continuousOn
  have hnn : ∀ s, 0 < s → 0 ≤ m s := fun s hs => by simpa using hm.2 0 s hs
  have hmeas := mt_meas' hc
  have hmtnn : ∀ s, 0 ≤ mt m s := fun s => by unfold mt; split_ifs with h; exacts [hnn s h, le_rfl]
  have hlt : ∀ᵐ s ∂(volume : Measure ℝ), ENNReal.ofReal (mt m s) < ⊤ := ae_of_all _ fun _ => ENNReal.ofReal_lt_top
  have hL := g.levy_integrable
  rw [hmu, integrable_withDensity_iff_integrable_smul' (hmeas.ennreal_ofReal) hlt] at hL
  simp only [ENNReal.toReal_ofReal (hmtnn _), smul_eq_mul] at hL
  have hint0 : IntegrableOn (fun s => s * m s) (Ioc 0 1) := by
    refine Integrable.mono' (hL.const_mul 2).integrableOn ?_ ?_
    · exact ((continuousOn_id.mul hc).mono (fun x hx => hx.1)).aestronglyMeasurable measurableSet_Ioc
    · refine (ae_restrict_iff' measurableSet_Ioc).mpr (ae_of_all _ fun s hs => ?_)
      have hs0 : 0 < s := hs.1
      simp only [mt, hs0, if_true, Real.norm_eq_abs]
      rw [abs_of_nonneg (mul_nonneg hs0.le (hnn s hs0))]
      have h1 : s * m s = (1 + s) * (s / (1 + s)) * m s := by field_simp
      rw [h1]
      have h2 : 0 ≤ s / (1 + s) * m s := mul_nonneg (by positivity) (hnn s hs0)
      nlinarith [hs.2]
  have hint1 : IntegrableOn m (Ioi 1) := by
    refine Integrable.mono' (hL.const_mul 2).integrableOn ?_ ?_
    · exact (hc.mono (fun x (hx : x ∈ Ioi (1:ℝ)) => show x ∈ Ioi (0:ℝ) from mem_Ioi.mpr (lt_trans one_pos (mem_Ioi.mp hx)))).aestronglyMeasurable measurableSet_Ioi
    · refine (ae_restrict_iff' measurableSet_Ioi).mpr (ae_of_all _ fun s hs => ?_)
      have hs1 : (1:ℝ) < s := hs
      have hs0 : 0 < s := lt_trans one_pos hs1
      simp only [mt, hs0, if_true, Real.norm_eq_abs]
      rw [abs_of_nonneg (hnn s hs0)]
      have h1 : 1 ≤ 2 * (s / (1 + s)) := by
        rw [mul_div_assoc', le_div_iff₀ (by positivity)]; linarith
      nlinarith [hnn s hs0]
  have hH : Hyp m := ⟨hc, hnn, hint0, hint1⟩
  refine ⟨hH, fun t ht => ?_⟩
  unfold bernsteinRate
  rw [hmu, integral_withDensity_eq_integral_toReal_smul hmeas.ennreal_ofReal hlt]
  simp only [ENNReal.toReal_ofReal (hmtnn _), smul_eq_mul]
  have e : ∀ s, mt m s * min (s / t) 1 = (min s t * mt m s) / t := by
    intro s
    rw [show (1:ℝ) = t / t from (div_self ht.ne').symm, min_div_div_right ht.le]
    ring
  simp only [e]
  rw [integral_div]
  unfold F
  field_simp

end X7R


open Set Filter MeasureTheory
open scoped Topology ContDiff

noncomputable section
namespace X7R

open QAlgorithms.Papers.Independent.Gap48.P07
open QAlgorithms.Papers.Independent.Renew46.P11 (Bernstein CompletelyMonotone)

variable {m : ℝ → ℝ}

lemma hasDerivAt_F (hm : Hyp m) {t : ℝ} (ht : 0 < t) : HasDerivAt (F m) (G m t) t := by
  have h1 := (hasDerivAt_P hm ht).add ((hasDerivAt_id t).mul (hasDerivAt_G hm ht))
  have e : t * m t + (1 * G m t + id t * -m t) = G m t := by simp
  rw [e] at h1
  refine h1.congr_of_eventuallyEq ?_
  filter_upwards [Ioi_mem_nhds ht] with u hu
  exact F_eq hm hu

lemma F_nonneg (hm : Hyp m) (t : ℝ) (ht : 0 ≤ t) : 0 ≤ F m t := by
  unfold F
  refine integral_nonneg fun s => ?_
  by_cases hs : 0 < s
  · exact mul_nonneg (le_min hs.le ht) (mt_nonneg hm s)
  · simp [mt, hs]

lemma repr_bernstein (hm : Hyp m) (hmCM : CompletelyMonotone m) {A B : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B)
    (h : ℝ → ℝ) (hh : ∀ t, 0 < t → h t = A * t + B + F m t) : Bernstein h := by
  have hhd : ∀ t, 0 < t → HasDerivAt h (A + G m t) t := by
    intro t ht
    have h1 := (((hasDerivAt_id t).const_mul A).add_const B).add (hasDerivAt_F hm ht)
    simp only [mul_one] at h1
    refine h1.congr_of_eventuallyEq ?_
    filter_upwards [Ioi_mem_nhds ht] with u hu
    simp [hh u hu]
  have hGd : ∀ t, 0 < t → HasDerivAt (fun u => A + G m u) (-m t) t :=
    fun t ht => (hasDerivAt_G hm ht).const_add A
  have hdh : EqOn (deriv h) (fun u => A + G m u) (Ioi 0) := fun t ht => (hhd t ht).deriv
  have hdG : EqOn (deriv (fun u => A + G m u)) (fun u => -m u) (Ioi 0) := fun t ht => (hGd t ht).deriv
  have hGs : ContDiffOn ℝ ∞ (fun u => A + G m u) (Ioi 0) :=
    (contDiffOn_infty_iff_deriv_of_isOpen isOpen_Ioi).mpr
      ⟨fun t ht => (hGd t ht).differentiableAt.differentiableWithinAt, hmCM.1.neg.congr hdG⟩
  have hdhs : ContDiffOn ℝ ∞ (deriv h) (Ioi 0) := hGs.congr hdh
  have hhs : ContDiffOn ℝ ∞ h (Ioi 0) :=
    (contDiffOn_infty_iff_deriv_of_isOpen isOpen_Ioi).mpr
      ⟨fun t ht => (hhd t ht).differentiableAt.differentiableWithinAt, hdhs⟩
  have hddh : EqOn (deriv (deriv h)) (fun u => -m u) (Ioi 0) := by
    intro t ht
    have he : deriv h =ᶠ[𝓝 t] (fun u => A + G m u) := Filter.eventually_of_mem (Ioi_mem_nhds ht) hdh
    rw [he.deriv_eq]
    exact hdG ht
  refine ⟨hhs, fun x hx => ?_, hdhs, fun n x hx => ?_⟩
  · rw [hh x hx]
    have := F_nonneg hm x hx.le
    positivity
  · cases n with
    | zero =>
      simp only [pow_zero, one_mul, iteratedDeriv_zero]
      rw [hdh hx]
      have := G_nonneg hm (le_of_lt hx)
      linarith
    | succ k =>
      rw [iteratedDeriv_succ', eqOn_iteratedDeriv isOpen_Ioi hddh k hx, iteratedDeriv_fun_neg]
      have := hmCM.2 k x hx
      rw [pow_succ]
      linarith

lemma fwd (r : ℝ → ℝ) (g : BernsteinData) (hg : CompleteBernstein g)
    (hrg : ∀ t, 0 < t → r t = bernsteinRate g t) : Bernstein (fun t => t * r t) := by
  obtain ⟨m, hmCM, hmu⟩ := hg
  have hmu' : g.mu = volume.withDensity (fun s => ENNReal.ofReal (mt m s)) := by
    rw [hmu]
    rfl
  obtain ⟨hH, hrate⟩ := cb_data g m hmCM hmu'
  refine repr_bernstein hH hmCM (A := g.a / 2) (B := g.b) (by linarith [g.a_nonneg]) g.b_nonneg _ ?_
  intro t ht
  rw [hrg t ht, hrate t ht]

end X7R


open Set Filter MeasureTheory
open scoped Topology ContDiff

noncomputable section
namespace X7R

open QAlgorithms.Papers.Independent.Gap48.P07
open QAlgorithms.Papers.Independent.Renew46.P11 (Bernstein CompletelyMonotone)

section back
variable {h : ℝ → ℝ} (hB : Bernstein h)
include hB

lemma b_h1_smooth : ContDiffOn ℝ ∞ (deriv h) (Ioi 0) := hB.2.2.1

lemma b_hd {t : ℝ} (ht : 0 < t) : HasDerivAt h (deriv h t) t :=
  ((hB.1.differentiableOn (by simp)) t ht |>.differentiableAt (Ioi_mem_nhds ht)).hasDerivAt

lemma b_h1d {t : ℝ} (ht : 0 < t) : HasDerivAt (deriv h) (-(-deriv (deriv h) t)) t := by
  rw [neg_neg]
  exact ((b_h1_smooth hB).differentiableOn (by simp) t ht |>.differentiableAt (Ioi_mem_nhds ht)).hasDerivAt

lemma b_mCM : CompletelyMonotone (fun s => -deriv (deriv h) s) := by
  have h2 : ContDiffOn ℝ ∞ (deriv (deriv h)) (Ioi 0) :=
    ((contDiffOn_infty_iff_deriv_of_isOpen isOpen_Ioi).mp (b_h1_smooth hB)).2
  refine ⟨h2.neg, fun n x hx => ?_⟩
  rw [iteratedDeriv_fun_neg, ← iteratedDeriv_succ']
  have := hB.2.2.2 (n+1) x hx
  rw [pow_succ] at this
  linarith

lemma b_m_nonneg {s : ℝ} (hs : 0 < s) : 0 ≤ -deriv (deriv h) s := by
  simpa using (b_mCM hB).2 0 s hs

lemma b_h1_nonneg {s : ℝ} (hs : 0 < s) : 0 ≤ deriv h s := by
  simpa using hB.2.2.2 0 s hs

lemma b_h1_anti : AntitoneOn (deriv h) (Ioi 0) := by
  refine antitoneOn_of_deriv_nonpos (convex_Ioi 0) (b_h1_smooth hB).continuousOn ?_ ?_
  · rw [interior_Ioi]; exact (b_h1_smooth hB).differentiableOn (by simp)
  · rw [interior_Ioi]; intro x hx; linarith [b_m_nonneg hB hx]

lemma b_h_mono : MonotoneOn h (Ioi 0) := by
  refine monotoneOn_of_deriv_nonneg (convex_Ioi 0) hB.1.continuousOn ?_ ?_
  · rw [interior_Ioi]; exact hB.1.differentiableOn (by simp)
  · rw [interior_Ioi]; intro x hx; exact b_h1_nonneg hB hx

/-- the limit at infinity of `h'` -/
def Alim (h : ℝ → ℝ) : ℝ := ⨅ t : ℝ, deriv h (max t 1)

lemma b_A_tendsto : Tendsto (deriv h) atTop (𝓝 (Alim h)) := by
  have hanti : Antitone (fun t : ℝ => deriv h (max t 1)) := by
    intro x y hxy
    exact b_h1_anti hB (lt_of_lt_of_le one_pos (le_max_right _ _) : (0:ℝ) < max x 1)
      (lt_of_lt_of_le one_pos (le_max_right _ _) : (0:ℝ) < max y 1) (max_le_max hxy le_rfl)
  have hbdd : BddBelow (range (fun t : ℝ => deriv h (max t 1))) :=
    ⟨0, by rintro _ ⟨t, rfl⟩; exact b_h1_nonneg hB (lt_of_lt_of_le one_pos (le_max_right _ _))⟩
  have := tendsto_atTop_ciInf hanti hbdd
  refine this.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with t ht
  rw [max_eq_left ht]

lemma b_A_nonneg : 0 ≤ Alim h :=
  le_ciInf fun t => b_h1_nonneg hB (lt_of_lt_of_le one_pos (le_max_right _ _))

lemma b_A_le {t : ℝ} (ht : 0 < t) : Alim h ≤ deriv h t := by
  have := b_A_tendsto hB
  refine le_of_tendsto this ?_
  filter_upwards [eventually_ge_atTop t] with u hu
  exact b_h1_anti hB ht (lt_of_lt_of_le ht hu) hu

/-- the limit at zero of `h` -/
def Blim (h : ℝ → ℝ) : ℝ := sInf (h '' Ioi 0)

lemma b_B_tendsto : Tendsto h (𝓝[>] 0) (𝓝 (Blim h)) :=
  (b_h_mono hB).tendsto_nhdsGT ⟨0, by rintro _ ⟨t, ht, rfl⟩; exact hB.2.1 t ht⟩

lemma b_B_nonneg : 0 ≤ Blim h :=
  le_csInf ⟨h 1, 1, mem_Ioi.mpr one_pos, rfl⟩ (by rintro _ ⟨t, ht, rfl⟩; exact hB.2.1 t ht)

end back

end X7R


open Set Filter MeasureTheory
open scoped Topology ContDiff

noncomputable section
namespace X7R

open QAlgorithms.Papers.Independent.Gap48.P07
open QAlgorithms.Papers.Independent.Renew46.P11 (Bernstein CompletelyMonotone)

def mB (h : ℝ → ℝ) (s : ℝ) : ℝ := -deriv (deriv h) s

section back
variable {h : ℝ → ℝ} (hB : Bernstein h)
include hB

lemma b_mcont : ContinuousOn (mB h) (Ioi 0) := (b_mCM hB).1.continuousOn

lemma b_ftc1 {t T : ℝ} (ht : 0 < t) (htT : t ≤ T) :
    ∫ s in t..T, mB h s = deriv h t - deriv h T := by
  have hd : ∀ x ∈ uIcc t T, HasDerivAt (fun s => -deriv h s) (mB h x) x := by
    intro x hx
    rw [uIcc_of_le htT] at hx
    have := (b_h1d hB (lt_of_lt_of_le ht hx.1)).neg
    rw [neg_neg] at this
    exact this
  have hi : IntervalIntegrable (mB h) volume t T :=
    ((b_mcont hB).mono (fun x hx => by
      rw [uIcc_of_le htT] at hx; exact lt_of_lt_of_le ht hx.1)).intervalIntegrable
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd hi]
  ring

lemma b_int1 : IntegrableOn (mB h) (Ioi 1) := by
  refine integrableOn_Ioi_of_intervalIntegral_norm_bounded (deriv h 1) 1 (b := id) (l := atTop)
    (fun i => ?_) tendsto_id ?_
  · exact ((b_mcont hB).mono (fun x hx => lt_of_lt_of_le one_pos hx.1)).integrableOn_compact
      isCompact_Icc |>.mono_set Ioc_subset_Icc_self
  · filter_upwards [eventually_ge_atTop 1] with i hi
    have e : ∫ x in (1:ℝ)..id i, ‖mB h x‖ = ∫ x in (1:ℝ)..id i, mB h x := by
      refine intervalIntegral.integral_congr fun x hx => ?_
      simp only [id] at hx
      rw [uIcc_of_le hi] at hx
      exact Real.norm_of_nonneg (b_m_nonneg hB (lt_of_lt_of_le one_pos hx.1))
    rw [e, id, b_ftc1 hB one_pos hi]
    linarith [b_h1_nonneg hB (lt_of_lt_of_le one_pos hi)]

lemma b_phi {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) :
    ∫ s in ε..1, s * mB h s = (h 1 - 1 * deriv h 1) - (h ε - ε * deriv h ε) := by
  have hd : ∀ x ∈ uIcc ε 1, HasDerivAt (fun s => h s - s * deriv h s) (x * mB h x) x := by
    intro x hx
    rw [uIcc_of_le hε1] at hx
    have hx0 : 0 < x := lt_of_lt_of_le hε hx.1
    have := (b_hd hB hx0).sub ((hasDerivAt_id x).mul (b_h1d hB hx0))
    have e : x * mB h x = deriv h x - (1 * deriv h x + id x * -(-deriv (deriv h) x)) := by
      simp only [mB, id]; ring
    rw [e]; exact this
  have hi : IntervalIntegrable (fun s => s * mB h s) volume ε 1 :=
    ((continuousOn_id.mul (b_mcont hB)).mono (fun x hx => by
      rw [uIcc_of_le hε1] at hx; exact lt_of_lt_of_le hε hx.1)).intervalIntegrable
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd hi]

lemma b_eps {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) : ε * deriv h ε ≤ 2 * h 1 := by
  have hab : ε / 2 < ε := by linarith
  have hc : ContinuousOn h (Icc (ε / 2) ε) :=
    hB.1.continuousOn.mono (fun x hx => lt_of_lt_of_le (by linarith) hx.1)
  obtain ⟨c, hc1, hc2⟩ := exists_hasDerivAt_eq_slope h (deriv h) hab hc
    (fun x hx => b_hd hB (lt_trans (by linarith) hx.1))
  have hc0 : 0 < c := lt_trans (by linarith) hc1.1
  have h1 : deriv h ε ≤ deriv h c := b_h1_anti hB hc0 hε hc1.2.le
  have h2 : h (ε / 2) ≥ 0 := hB.2.1 _ (by linarith)
  have h3 : h ε ≤ h 1 := b_h_mono hB hε (mem_Ioi.mpr one_pos) hε1
  have e : ε * deriv h c = 2 * (h ε - h (ε / 2)) := by
    rw [hc2]; field_simp; ring
  nlinarith

lemma b_int0 : IntegrableOn (fun s => s * mB h s) (Ioc 0 1) := by
  refine integrableOn_Ioc_of_intervalIntegral_norm_bounded_left (I := 3 * h 1)
    (a := fun n : ℕ => 1 / ((n : ℝ) + 1)) (l := atTop) (fun n => ?_)
    tendsto_one_div_add_atTop_nhds_zero_nat (Eventually.of_forall fun n => ?_)
  · have hp : 0 < 1 / ((n : ℝ) + 1) := by positivity
    exact ((continuousOn_id.mul (b_mcont hB)).mono (fun x hx => lt_of_lt_of_le hp hx.1)).integrableOn_compact
      isCompact_Icc |>.mono_set Ioc_subset_Icc_self
  · have hp : 0 < 1 / ((n : ℝ) + 1) := by positivity
    have hp1 : 1 / ((n : ℝ) + 1) ≤ 1 := by
      rw [div_le_one (by positivity)]; linarith [(Nat.cast_nonneg n : (0:ℝ) ≤ n)]
    have e : ∫ x in Ioc (1 / ((n : ℝ) + 1)) 1, ‖x * mB h x‖ = ∫ x in (1 / ((n : ℝ) + 1))..1, x * mB h x := by
      rw [intervalIntegral.integral_of_le hp1]
      refine setIntegral_congr_fun measurableSet_Ioc fun x hx => ?_
      have hx0 : 0 < x := lt_trans hp hx.1
      exact Real.norm_of_nonneg (mul_nonneg hx0.le (b_m_nonneg hB hx0))
    rw [e, b_phi hB hp hp1]
    have := b_eps hB hp hp1
    have := b_h1_nonneg hB one_pos
    have := hB.2.1 _ hp
    nlinarith

lemma b_hyp : Hyp (mB h) := ⟨b_mcont hB, fun s hs => b_m_nonneg hB hs, b_int0 hB, b_int1 hB⟩

lemma b_G {t : ℝ} (ht : 0 < t) : G (mB h) t = deriv h t - Alim h := by
  have h1 := intervalIntegral_tendsto_integral_Ioi t (intOn_Ioi (b_hyp hB) ht) tendsto_id
  have h2 : Tendsto (fun T => ∫ s in t..id T, mB h s) atTop (𝓝 (deriv h t - Alim h)) := by
    have := (b_A_tendsto hB).const_sub (deriv h t)
    refine this.congr' ?_
    filter_upwards [eventually_ge_atTop t] with T hT
    rw [id, b_ftc1 hB ht hT]
  exact tendsto_nhds_unique h1 h2

lemma b_repr {t : ℝ} (ht : 0 < t) : h t = Alim h * t + Blim h + F (mB h) t := by
  set D := fun u => h u - (Alim h * u + Blim h + F (mB h) u) with hD
  have hDd : ∀ u, 0 < u → HasDerivAt D 0 u := by
    intro u hu
    have := (b_hd hB hu).sub ((((hasDerivAt_id u).const_mul (Alim h)).add_const (Blim h)).add
      (hasDerivAt_F (b_hyp hB) hu))
    have e : (0:ℝ) = deriv h u - (Alim h * 1 + G (mB h) u) := by rw [b_G hB hu]; ring
    rw [e]; exact this
  have hconst : ∀ u, 0 < u → D u = D t := fun u hu =>
    isOpen_Ioi.is_const_of_deriv_eq_zero isPreconnected_Ioi
      (fun x hx => (hDd x hx).differentiableAt.differentiableWithinAt)
      (fun x hx => (hDd x hx).deriv) hu ht
  have hlim : Tendsto D (𝓝[>] 0) (𝓝 (Blim h - (Alim h * 0 + Blim h + 0))) := by
    refine (b_B_tendsto hB).sub (Tendsto.add ?_ (F_lim (b_hyp hB)))
    exact ((continuous_const.mul continuous_id).add continuous_const).tendsto 0 |>.mono_left nhdsWithin_le_nhds
  have hlim2 : Tendsto D (𝓝[>] 0) (𝓝 (D t)) := by
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with u hu
    exact (hconst u hu).symm
  have := tendsto_nhds_unique hlim2 hlim
  simp only [mul_zero, zero_add, add_zero, sub_self] at this
  have e : D t = h t - (Alim h * t + Blim h + F (mB h) t) := rfl
  linarith

end back

end X7R


open Set Filter MeasureTheory
open scoped Topology ContDiff

noncomputable section
namespace X7R

open QAlgorithms.Papers.Independent.Gap48.P07
open QAlgorithms.Papers.Independent.Renew46.P11 (Bernstein CompletelyMonotone)

lemma bwd (r : ℝ → ℝ) (hB : Bernstein (fun t => t * r t)) :
    ∃ g : BernsteinData, CompleteBernstein g ∧ ∀ t, 0 < t → r t = bernsteinRate g t := by
  set h : ℝ → ℝ := fun t => t * r t with hh
  have hyp := b_hyp hB
  set m := mB h with hm
  have hmeas := mt_meas hyp
  have hlt : ∀ᵐ s ∂(volume : Measure ℝ), ENNReal.ofReal (mt m s) < ⊤ :=
    ae_of_all _ fun _ => ENNReal.ofReal_lt_top
  let g : BernsteinData :=
    { a := 2 * Alim h
      b := Blim h
      mu := volume.withDensity (fun s => ENNReal.ofReal (mt m s))
      a_nonneg := by linarith [b_A_nonneg hB]
      b_nonneg := b_B_nonneg hB
      support_positive := by
        rw [withDensity_apply _ measurableSet_Iic]
        rw [setLIntegral_congr_fun measurableSet_Iic (g := fun _ => 0) (fun s hs => by
          simp [mt, not_lt.mpr (show s ≤ 0 from hs)])]
        simp
      locally_finite_positive := by
        intro l r hl
        rw [withDensity_apply _ measurableSet_Icc]
        rw [setLIntegral_congr_fun measurableSet_Icc (g := fun s => ENNReal.ofReal (m s)) (fun s hs => by
          simp [mt, lt_of_lt_of_le hl hs.1])]
        exact (intOn_Icc hyp hl).setLIntegral_lt_top
      levy_integrable := by
        rw [integrable_withDensity_iff_integrable_smul' hmeas.ennreal_ofReal hlt]
        refine Integrable.mono' (F_int hyp one_pos) ?_ (ae_of_all _ fun s => ?_)
        · exact (hmeas.ennreal_ofReal.ennreal_toReal.smul
            (measurable_id.div (measurable_const.add measurable_id))).aestronglyMeasurable
        · simp only [smul_eq_mul, Real.norm_eq_abs, ENNReal.toReal_ofReal (mt_nonneg hyp s)]
          by_cases hs : 0 < s
          · have h1 : s / (1 + s) ≤ min s 1 := by
              refine le_min ?_ ?_
              · rw [div_le_iff₀ (by positivity)]; nlinarith
              · rw [div_le_one (by positivity)]; linarith
            rw [abs_of_nonneg (mul_nonneg (mt_nonneg hyp s) (by positivity))]
            nlinarith [mt_nonneg hyp s]
          · simp [mt, hs] }
  have hcb : CompleteBernstein g := ⟨m, b_mCM hB, rfl⟩
  refine ⟨g, hcb, fun t ht => ?_⟩
  obtain ⟨-, hrate⟩ := cb_data g m (b_mCM hB) rfl
  have e1 := hrate t ht
  have e2 := b_repr hB ht
  have e3 : h t = t * r t := rfl
  have : t * r t = t * bernsteinRate g t := by
    rw [← e3, e2, e1]
    show Alim h * t + Blim h + F (mB h) t = 2 * Alim h / 2 * t + Blim h + F m t
    ring
  exact mul_left_cancel₀ ht.ne' this

end X7R

open Set Filter MeasureTheory
open scoped Topology NNReal

attribute [local instance] Classical.propDecidable

open QAlgorithms.Papers.Independent.Gap48.P07 QAlgorithms.Papers.Independent.Next46.P06
  QAlgorithms.Papers.Independent.Renew46.P11 in
theorem solution (r : ℝ → ℝ) (hr : ∀ t, 0 < t → 0 < r t) :
    (∃ g : BernsteinData, CompleteBernstein g ∧ ∀ t, 0 < t → r t = bernsteinRate g t) ↔
      Bernstein (fun t => t * r t) := by
  constructor
  · rintro ⟨g, hg, hrg⟩
    exact X7R.fwd r g hg hrg
  · exact X7R.bwd r

