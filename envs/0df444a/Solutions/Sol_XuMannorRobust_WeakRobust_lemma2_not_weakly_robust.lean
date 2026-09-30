-- Prove2me | solution 1 for XuMannorRobust.WeakRobust.lemma2_not_weakly_robust
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-30T08:16:49.169041+00:00
-- url     : https://prove2.me/submissions/4d278c13-e710-434a-899d-40ec7156a1af

import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Tactic
import Definitions.Def_XuMannorRobust_WeakRobust_WeaklyRobust
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

theorem _root_.solution {Z H : Type*} [MeasurableSpace Z] (μ : Measure Z)
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
