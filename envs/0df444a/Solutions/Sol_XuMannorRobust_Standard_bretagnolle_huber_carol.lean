-- Prove2me | solution 1 for XuMannorRobust.Standard.bretagnolle_huber_carol
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-30T08:33:51.927184+00:00
-- url     : https://prove2.me/submissions/dbd881f1-9459-42c7-9cbe-761990301da5

import Mathlib.Probability.Moments.SubGaussian
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.Tactic
import Definitions.Def_XuMannorRobust_Standard_CellCount
open MeasureTheory ProbabilityTheory XuMannorRobust.Standard
open scoped BigOperators
noncomputable section

private theorem bounded_average_tail {Z : Type*} [MeasurableSpace Z] (μ : Measure Z)
    [IsProbabilityMeasure μ] (f : Z → ℝ) (hf : Measurable f)
    (hb : ∀ z, f z ∈ Set.Icc (-1) 1) {n : ℕ} (hn : 0 < n)
    (lam : ℝ) (hlam : 0 ≤ lam) :
    (Measure.pi (fun _ : Fin n => μ)) {s | lam ≤ (∑ j, f (s j)) / (n : ℝ) - ∫ z, f z ∂μ} ≤
      ENNReal.ofReal (Real.exp (-((n : ℝ)*lam^2)/2)) := by
  let P := Measure.pi (fun _ : Fin n => μ)
  let X (j : Fin n) (s : Fin n → Z) := f (s j) - ∫ z, f z ∂μ
  have hind : iIndepFun X P := iIndepFun_pi (fun _ => (hf.sub_const _).aemeasurable)
  have hsub (j : Fin n) : HasSubgaussianMGF (X j) 1 P := by
    have hh := hasSubgaussianMGF_of_mem_Icc (μ := P)
      (X := fun s : Fin n → Z => f (s j)) (hf.comp (measurable_pi_apply j)).aemeasurable
      (Filter.Eventually.of_forall fun s => hb (s j))
    rw [integral_comp_eval (μ := fun _ : Fin n => μ) hf.aestronglyMeasurable] at hh
    norm_num at hh
    exact hh
  have hn' : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  have hh := HasSubgaussianMGF.measure_sum_ge_le_of_iIndepFun hind
    (s := Finset.univ) (c := fun _ => (1 : NNReal)) (fun j _ => hsub j)
    (show 0 ≤ (n : ℝ)*lam from mul_nonneg hn'.le hlam)
  have heq : {s : Fin n → Z | lam ≤ (∑ j, f (s j))/(n : ℝ) - ∫ z, f z ∂μ} =
      {s | (n : ℝ)*lam ≤ ∑ j, X j s} := by
    ext s
    simp only [Set.mem_setOf_eq, X, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    have hc : (∑ j, f (s j))/(n : ℝ)*(n : ℝ) = ∑ j, f (s j) := div_mul_cancel₀ _ hn'.ne'
    constructor <;> intro h <;> nlinarith
  rw [heq]
  rw [← ofReal_measureReal (μ := P)]
  apply ENNReal.ofReal_le_ofReal
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one, NNReal.coe_natCast] at hh
  have he : -((n : ℝ)*lam)^2/(2*(n : ℝ)) = -((n : ℝ)*lam^2)/2 := by field_simp
  simpa only [he] using hh

theorem _root_.solution {Z : Type*} [MeasurableSpace Z] (μ : Measure Z)
    [IsProbabilityMeasure μ] {K : ℕ} (C : Fin K → Set Z) (hC_meas : ∀ i, MeasurableSet (C i))
    (hC_disj : Pairwise (Function.onFun Disjoint C)) (hC_cover : (⋃ i, C i) = Set.univ)
    {n : ℕ} (hn : 0 < n) (lam : ℝ) (hlam : 0 ≤ lam) :
    (Measure.pi fun _ : Fin n => μ)
        {s | lam ≤ ∑ i, |(cellCount C s i : ℝ) / (n : ℝ) - (μ (C i)).toReal|}
      ≤ ENNReal.ofReal ((2 : ℝ) ^ K * Real.exp (-((n : ℝ) * lam ^ 2) / 2)) := by
  classical
  let P := Measure.pi (fun _ : Fin n => μ)
  let sign (σ : Fin K → Bool) (i : Fin K) : ℝ := if σ i then 1 else -1
  let g (σ : Fin K → Bool) (z : Z) := ∑ i, (C i).indicator (fun _ => sign σ i) z
  have hg (σ : Fin K → Bool) : Measurable (g σ) := by
    apply Finset.measurable_sum
    intro i _
    exact measurable_const.indicator (hC_meas i)
  have hgi (σ : Fin K → Bool) (z : Z) (i : Fin K) (hi : z ∈ C i) : g σ z = sign σ i := by
    dsimp only [g]
    rw [Finset.sum_eq_single i]
    · exact Set.indicator_of_mem hi _
    · intro j _ hji
      have hj : z ∉ C j := fun hj => Set.disjoint_left.mp (hC_disj hji) hj hi
      exact Set.indicator_of_notMem hj _
    · simp
  have hgb (σ : Fin K → Bool) (z : Z) : g σ z ∈ Set.Icc (-1) 1 := by
    obtain ⟨i, hi⟩ : ∃ i, z ∈ C i := by
      apply Set.mem_iUnion.mp
      rw [hC_cover]
      trivial
    rw [hgi σ z i hi]
    dsimp [sign]
    split <;> norm_num
  have hmean (σ : Fin K → Bool) : ∫ z, g σ z ∂μ = ∑ i, μ.real (C i) * sign σ i := by
    rw [show g σ = fun z => ∑ i, (C i).indicator (fun _ => sign σ i) z from rfl, integral_finsetSum]
    · apply Finset.sum_congr rfl
      intro i _
      simpa using integral_indicator_const (μ := μ) (sign σ i) (hC_meas i)
    · intro i _
      exact (integrable_const _).indicator (hC_meas i)
  have hsample (σ : Fin K → Bool) (s : Fin n → Z) :
      (∑ j, g σ (s j))/(n : ℝ) - ∫ z, g σ z ∂μ =
      ∑ i, sign σ i * ((cellCount C s i : ℝ)/(n : ℝ) - μ.real (C i)) := by
    dsimp only [g]
    rw [Finset.sum_comm]
    have hh (i : Fin K) : (∑ j, (C i).indicator (fun _ => sign σ i) (s j)) =
        (cellCount C s i : ℝ) * sign σ i := by
      simp only [Set.indicator_apply, ← Finset.sum_filter]
      simp [cellCount]
    simp_rw [hh]
    change (∑ i, (cellCount C s i : ℝ)*sign σ i)/(n : ℝ) - ∫ z, g σ z ∂μ = _
    rw [hmean, Finset.sum_div, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i _
    ring
  let E (σ : Fin K → Bool) := {s : Fin n → Z | lam ≤ (∑ j, g σ (s j))/(n : ℝ) - ∫ z, g σ z ∂μ}
  have hsub : {s : Fin n → Z | lam ≤ ∑ i, |(cellCount C s i : ℝ)/(n : ℝ) - (μ (C i)).toReal|} ⊆ ⋃ σ, E σ := by
    intro s hs
    let σ (i : Fin K) : Bool := decide (0 ≤ (cellCount C s i : ℝ)/(n : ℝ) - μ.real (C i))
    apply Set.mem_iUnion.mpr
    refine ⟨σ, ?_⟩
    change lam ≤ (∑ j, g σ (s j))/(n : ℝ) - ∫ z, g σ z ∂μ
    rw [hsample]
    change lam ≤ ∑ i, |(cellCount C s i : ℝ)/(n : ℝ) - (μ (C i)).toReal| at hs
    convert hs using 1
    congr 1
    funext i
    dsimp only [sign, σ]
    split <;> rename_i hi
    · have hh : 0 ≤ (cellCount C s i : ℝ)/(n : ℝ) - μ.real (C i) := of_decide_eq_true hi
      change 0 ≤ (cellCount C s i : ℝ)/(n : ℝ) - (μ (C i)).toReal at hh
      rw [one_mul, abs_of_nonneg hh]
      rfl
    · have hh : ¬0 ≤ (cellCount C s i : ℝ)/(n : ℝ) - μ.real (C i) := fun h => hi (by simp [h])
      change ¬0 ≤ (cellCount C s i : ℝ)/(n : ℝ) - (μ (C i)).toReal at hh
      rw [neg_one_mul, abs_of_neg (lt_of_not_ge hh)]
      rfl
  calc
    _ ≤ P (⋃ σ, E σ) := measure_mono hsub
    _ ≤ ∑' σ, P (E σ) := measure_iUnion_le _
    _ = ∑ σ, P (E σ) := tsum_fintype _
    _ ≤ ∑ σ : Fin K → Bool, ENNReal.ofReal (Real.exp (-((n : ℝ)*lam^2)/2)) := by
      apply Finset.sum_le_sum
      intro σ _
      exact bounded_average_tail μ (g σ) (hg σ) (hgb σ) hn lam hlam
    _ = _ := by
      rw [← ENNReal.ofReal_sum_of_nonneg]
      · congr 1
        simp [Fintype.card_fun, Fintype.card_fin]
      · intro σ _
        exact (Real.exp_pos _).le
