-- Prove2me | solution 1 for XuMannorRobust.WeakRobust.theorem8_generalizes_iff_weakly_robust
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-30T08:21:32.015216+00:00
-- url     : https://prove2.me/submissions/1186ad43-2aba-48b1-903b-0a33c6c1ab5a

import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Tactic
import Definitions.Def_XuMannorRobust_WeakRobust_Generalizes
import Definitions.Def_XuMannorRobust_WeakRobust_WeaklyRobust
import Mathlib.Probability.Moments.Variance
import Mathlib.Analysis.SpecificLimits.Basic
import Definitions.Def_XuMannorRobust_WeakRobust_Setup
open MeasureTheory Filter Topology XuMannorRobust.WeakRobust
open scoped BigOperators
noncomputable section

private theorem loss_integrable {Z H : Type*} [MeasurableSpace Z] (μ : Measure Z)
    [IsProbabilityMeasure μ] (l : H → Z → ℝ) (M : ℝ)
    (hl_bound : ∀ h z, 0 ≤ l h z ∧ l h z ≤ M) (hl_meas : ∀ h, Measurable (l h))
    (h : H) : Integrable (l h) μ := by
  apply (integrable_const M).mono' (hl_meas h).aestronglyMeasurable
  exact Eventually.of_forall fun z => by simpa only [Real.norm_eq_abs, abs_of_nonneg (hl_bound h z).1] using (hl_bound h z).2

private theorem avg_integrable {Z H : Type*} [MeasurableSpace Z] (μ : Measure Z)
    [IsProbabilityMeasure μ] (l : H → Z → ℝ) (M : ℝ)
    (hl_bound : ∀ h z, 0 ≤ l h z ∧ l h z ≤ M) (hl_meas : ∀ h, Measurable (l h))
    {n : ℕ} (h : H) : Integrable (avgLoss (n := n) l h) (Measure.pi fun _ : Fin n => μ) := by
  unfold avgLoss
  apply Integrable.const_mul
  apply integrable_finset_sum
  intro i _
  exact integrable_comp_eval (loss_integrable μ l M hl_bound hl_meas h)

private theorem avg_mean {Z H : Type*} [MeasurableSpace Z] (μ : Measure Z)
    [IsProbabilityMeasure μ] (l : H → Z → ℝ) (M : ℝ)
    (hl_bound : ∀ h z, 0 ≤ l h z ∧ l h z ≤ M) (hl_meas : ∀ h, Measurable (l h))
    {n : ℕ} (hn : 0 < n) (h : H) :
    ∫ t, avgLoss l h t ∂(Measure.pi fun _ : Fin n => μ) = expectedLoss μ l h := by
  unfold avgLoss expectedLoss
  rw [integral_const_mul, integral_finset_sum]
  · simp_rw [integral_comp_eval (μ := fun _ : Fin n => μ) (hl_meas h).aestronglyMeasurable]
    simp [ne_of_gt hn]
  · intro i _
    exact integrable_comp_eval (loss_integrable μ l M hl_bound hl_meas h)

private theorem avg_bounds {Z H : Type*} (l : H → Z → ℝ) (M : ℝ)
    (hl_bound : ∀ h z, 0 ≤ l h z ∧ l h z ≤ M)
    {n : ℕ} (hn : 0 < n) (h : H) (t : Fin n → Z) :
    0 ≤ avgLoss l h t ∧ avgLoss l h t ≤ M := by
  have hn' : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  unfold avgLoss
  constructor
  · exact mul_nonneg (by positivity) (Finset.sum_nonneg fun i _ => (hl_bound h (t i)).1)
  · have hh := Finset.sum_le_sum (s := Finset.univ) (fun i _ => (hl_bound h (t i)).2)
    have hh' : ∑ i, l h (t i) ≤ (n : ℝ) * M := by simpa using hh
    rw [one_div, ← div_eq_inv_mul, div_le_iff₀ hn']
    simpa only [mul_comm] using hh'

private theorem avg_measurable {Z H : Type*} [MeasurableSpace Z] (l : H → Z → ℝ)
    (hl_meas : ∀ h, Measurable (l h)) {n : ℕ} (h : H) :
    Measurable (avgLoss (n := n) l h) := by
  unfold avgLoss
  fun_prop

open ProbabilityTheory
private theorem sample_tail {Z H : Type*} [MeasurableSpace Z] (μ : Measure Z)
    [IsProbabilityMeasure μ] (l : H → Z → ℝ) (M : ℝ)
    (hl_bound : ∀ h z, 0 ≤ l h z ∧ l h z ≤ M) (hl_meas : ∀ h, Measurable (l h))
    {n : ℕ} (hn : 0 < n) (h : H) (ε : ℝ) (hε : 0 < ε) :
    (Measure.pi (fun _ : Fin n => μ))
      {t | ε ≤ |avgLoss l h t - expectedLoss μ l h|} ≤ ENNReal.ofReal ((M^2 / ε^2) / n) := by
  let P := Measure.pi (fun _ : Fin n => μ)
  have hlp : MemLp (l h) 2 μ :=
    memLp_of_bounded (Eventually.of_forall fun z => hl_bound h z) (hl_meas h).aestronglyMeasurable 2
  have hap : MemLp (avgLoss (n := n) l h) 2 P :=
    memLp_of_bounded (Eventually.of_forall fun t => avg_bounds l M hl_bound hn h t)
      (avg_measurable l hl_meas h).aestronglyMeasurable 2
  have hv : variance (l h) μ ≤ M^2 := by
    have hh := variance_le_sq_of_bounded (μ := μ) (Eventually.of_forall fun z => hl_bound h z) (hl_meas h).aemeasurable
    simp only [sub_zero] at hh
    nlinarith [sq_nonneg M]
  have hvar : variance (avgLoss (n := n) l h) P = (1 / (n : ℝ))^2 * ((n : ℝ) * variance (l h) μ) := by
    unfold avgLoss
    rw [variance_const_mul]
    have heq : (fun t : Fin n → Z => ∑ i, l h (t i)) = ∑ i : Fin n, (fun t : Fin n → Z => l h (t i)) := by
      ext t
      simp only [Finset.sum_apply]
    rw [heq, variance_sum_pi (fun _ => hlp)]
    simp
  have hh := meas_ge_le_variance_div_sq hap hε
  rw [avg_mean μ l M hl_bound hl_meas hn h] at hh
  apply hh.trans
  apply ENNReal.ofReal_le_ofReal
  rw [hvar]
  have hn' : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  have he' : 0 < ε^2 := sq_pos_of_pos hε
  have hv' := mul_le_mul_of_nonneg_left hv (show 0 ≤ (1 / (n : ℝ))^2 * (n : ℝ) by positivity)
  apply (div_le_iff₀ he').2
  have heq : (M^2 / ε^2 / (n : ℝ)) * ε^2 = M^2 / n := by field_simp
  rw [heq]
  have heq' : (1 / (n : ℝ))^2 * ((n : ℝ) * variance (l h) μ) = variance (l h) μ / n := by field_simp
  rw [heq']
  exact div_le_div_of_nonneg_right hv hn'.le

private theorem concentration {Z H : Type*} [MeasurableSpace Z] (μ : Measure Z)
    [IsProbabilityMeasure μ] (l : H → Z → ℝ) (M : ℝ)
    (hl_bound : ∀ h z, 0 ≤ l h z ∧ l h z ≤ M) (hl_meas : ∀ h, Measurable (l h))
    (A : (n : ℕ) → (Fin n → Z) → H) (sStar : ℕ → Z) :
    ∀ ε > 0, Tendsto
      (fun n => Measure.pi (fun _ : Fin n => μ)
        {t | ε ≤ |avgLoss l (A n (firstN sStar n)) t - expectedLoss μ l (A n (firstN sStar n))|})
      atTop (𝓝 0) := by
  intro ε hε
  have hlim : Tendsto (fun n : ℕ => ENNReal.ofReal ((M^2 / ε^2) / n)) atTop (𝓝 0) := by
    have hh : Tendsto (fun n : ℕ => (M^2 / ε^2) / (n : ℝ)) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
    simpa using ENNReal.tendsto_ofReal hh
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlim
    (Eventually.of_forall fun n => bot_le)
  filter_upwards [eventually_ge_atTop 1] with n hn
  exact sample_tail μ l M hl_bound hl_meas (by omega) (A n (firstN sStar n)) ε hε

private theorem diagonal_cutoff (N : ℕ → ℕ) : ∃ K : ℕ → ℕ,
    Tendsto K atTop atTop ∧ ∀ᶠ n in atTop, N (K n) ≤ n := by
  classical
  let S (n : ℕ) := (Finset.range (n+1)).filter (fun k => N k ≤ n)
  let K (n : ℕ) := (S n).sup id
  refine ⟨K, ?_, ?_⟩
  · apply tendsto_atTop.2
    intro k
    filter_upwards [eventually_ge_atTop (max k (N k))] with n hn
    change id k ≤ (S n).sup id
    apply Finset.le_sup
    simp only [S, Finset.mem_filter, Finset.mem_range]
    exact ⟨by omega, by omega⟩
  · filter_upwards [eventually_ge_atTop (N 0)] with n hn
    have hs : (S n).Nonempty := ⟨0, by simp [S, hn]⟩
    have hk : K n ∈ S n := by simpa [K] using (Finset.sup_mem_of_nonempty (f := id) hs)
    exact (Finset.mem_filter.mp hk).2

private theorem notrobust {Z H : Type*} [MeasurableSpace Z] (μ : Measure Z)
    [IsProbabilityMeasure μ] (l : H → Z → ℝ) (M : ℝ)
    (hl_bound : ∀ h z, 0 ≤ l h z ∧ l h z ≤ M) (hl_meas : ∀ h, Measurable (l h))
    (A : (n : ℕ) → (Fin n → Z) → H) (sStar : ℕ → Z)
    (hnot : ¬ WeaklyRobust μ l A sStar) :
    ∃ ε > 0, ∃ δ > 0, ∃ᶠ n in atTop,
      ENNReal.ofReal δ ≤ Measure.pi (fun _ : Fin n => μ)
        {t | ε ≤ |avgLoss l (A n (firstN sStar n)) t
          - avgLoss l (A n (firstN sStar n)) (firstN sStar n)|} := by
  classical
  by_contra hno
  push_neg at hno
  let P (n : ℕ) := Measure.pi (fun _ : Fin n => μ)
  let g (n : ℕ) (t : Fin n → Z) :=
    |avgLoss l (A n (firstN sStar n)) t - avgLoss l (A n (firstN sStar n)) (firstN sStar n)|
  let e (k : ℕ) : ℝ := 1 / (k + 1 : ℝ)
  have hepos (k : ℕ) : 0 < e k := by dsimp [e]; positivity
  have he0 : Tendsto e atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  have hN (k : ℕ) : ∃ N : ℕ, ∀ n ≥ N, P n {t | e k ≤ g n t} < ENNReal.ofReal (e k) := by
    exact eventually_atTop.1 (hno (e k) (hepos k) (e k) (hepos k))
  choose N hN using hN
  obtain ⟨K, hK, hKN⟩ := diagonal_cutoff N
  let D (n : ℕ) := {t | g n t < e (K n)}
  have hbad : Tendsto (fun n => P n (D n)ᶜ) atTop (𝓝 0) := by
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds
      (show Tendsto (fun n => ENNReal.ofReal (e (K n))) atTop (𝓝 0) from by simpa using ENNReal.tendsto_ofReal (he0.comp hK))
      (Eventually.of_forall fun n => bot_le)
      (show ∀ᶠ n in atTop, P n (D n)ᶜ ≤ ENNReal.ofReal (e (K n)) from ?_)
    filter_upwards [hKN] with n hn
    simpa [D, Set.compl_setOf, not_lt] using (hN (K n) n hn).le
  apply hnot
  refine ⟨D, fun n => e (K n), ?_, he0.comp hK, ?_⟩
  · have hD (n : ℕ) : MeasurableSet (D n) := by
      have hm := avg_measurable l hl_meas (n := n) (A n (firstN sStar n))
      apply measurableSet_lt ?_ measurable_const
      dsimp [g]
      fun_prop
    have heq (n : ℕ) : P n (D n) = 1 - P n (D n)ᶜ := by
      rw [← prob_compl_eq_one_sub (hD n).compl]
      simp
    change Tendsto (fun n => P n (D n)) atTop (𝓝 1)
    simp_rw [heq]
    simpa using ENNReal.Tendsto.sub tendsto_const_nhds hbad (Or.inl ENNReal.one_ne_top)
  · intro n t ht
    exact ht.le

theorem _root_.solution {Z H : Type*} [MeasurableSpace Z] (μ : Measure Z)
    [IsProbabilityMeasure μ] (l : H → Z → ℝ) (M : ℝ)
    (hl_bound : ∀ h z, 0 ≤ l h z ∧ l h z ≤ M) (hl_meas : ∀ h, Measurable (l h))
    (A : (n : ℕ) → (Fin n → Z) → H) (sStar : ℕ → Z) :
    Generalizes μ l A sStar ↔ WeaklyRobust μ l A sStar := by
  classical
  let P (n : ℕ) := Measure.pi (fun _ : Fin n => μ)
  let a (n : ℕ) := avgLoss (n := n) l (A n (firstN sStar n))
  let b (n : ℕ) := expectedLoss μ l (A n (firstN sStar n))
  let c (n : ℕ) := a n (firstN sStar n)
  have hcon (ε : ℝ) (hε : 0 < ε) : Tendsto
      (fun n => P n {t | ε ≤ |a n t - b n|}) atTop (𝓝 0) :=
    concentration μ l M hl_bound hl_meas A sStar ε hε
  constructor
  · intro hg
    by_contra hn
    obtain ⟨ε, hε, δ, hδ, hfreq⟩ := notrobust μ l M hl_bound hl_meas A sStar hn
    have hgap : ∀ᶠ n in atTop, |b n - c n| < ε/2 := hg.eventually (gt_mem_nhds (half_pos hε))
    have hlim := hcon (ε/2) (half_pos hε)
    have hp : ∀ᶠ n in atTop, P n {t | ε/2 ≤ |a n t - b n|} < ENNReal.ofReal δ :=
      hlim.eventually (gt_mem_nhds (ENNReal.ofReal_pos.mpr hδ))
    obtain ⟨n, hnf, hng, hnp⟩ := (hfreq.and_eventually (hgap.and hp)).exists
    have hsub : {t | ε ≤ |a n t - c n|} ⊆ {t | ε/2 ≤ |a n t - b n|} := by
      intro t ht
      have ht' := abs_sub_le (a n t) (b n) (c n)
      change ε ≤ |a n t - c n| at ht
      change ε/2 ≤ |a n t - b n|
      linarith
    have hle := measure_mono (μ := P n) hsub
    exact (not_le_of_gt hnp) (hnf.trans hle)
  · rintro ⟨D, η, hD, hη, herr⟩
    apply Metric.tendsto_nhds.mpr
    intro ε hε
    have hη' : ∀ᶠ n in atTop, η n < ε/2 := hη.eventually (gt_mem_nhds (half_pos hε))
    have hhalf : (1/2 : ENNReal) < 1 := by norm_num
    have hD' : ∀ᶠ n in atTop, (1/2 : ENNReal) < P n (D n) := hD.eventually (lt_mem_nhds hhalf)
    have hp : ∀ᶠ n in atTop, P n {t | ε/2 ≤ |a n t - b n|} < (1/2 : ENNReal) :=
      (hcon (ε/2) (half_pos hε)).eventually (gt_mem_nhds (by norm_num))
    filter_upwards [hη', hD', hp] with n hn hDn hpn
    have he : ∃ t ∈ D n, |a n t - b n| < ε/2 := by
      by_contra hno
      push_neg at hno
      have hs : D n ⊆ {t | ε/2 ≤ |a n t - b n|} := hno
      have hle := measure_mono (μ := P n) hs
      exact (not_lt_of_ge hle) (hpn.trans hDn)
    obtain ⟨t, ht, htn⟩ := he
    have her := herr n t ht
    have htri := abs_sub_le (b n) (a n t) (c n)
    have hgap : |b n - c n| < ε := by
      rw [abs_sub_comm (b n) (a n t)] at htri
      change |a n t - c n| ≤ η n at her
      linarith
    simpa only [Real.dist_eq, sub_zero, abs_abs] using hgap
