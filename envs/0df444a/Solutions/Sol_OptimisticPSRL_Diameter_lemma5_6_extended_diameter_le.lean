-- Prove2me | solution 1 for OptimisticPSRL.Diameter.lemma5_6_extended_diameter_le
-- status  : ACCEPTED   (prove)
-- author  : @sometik179
-- created : 2026-10-22T12:17:35.7028+00:00
-- url     : https://prove2.me/submissions/f877cb8f-e311-438a-b5e5-9c35d63bc32f

import Mathlib
import Definitions.Def_FiniteMDPLearning
import Definitions.Def_OptimisticPSRL_Diameter_Setting
open BanditAlgorithm NNReal ENNReal
noncomputable section
open scoped BigOperators ENNReal NNReal
open MeasureTheory ProbabilityTheory BanditAlgorithm OptimisticPSRL.Diameter
namespace OptimisticDiameterProof

noncomputable def killedStep {S A : ℕ} (M : FiniteMDP S A)
    (f : Fin S → Fin A) (tgt : Fin S) (v : Fin S → ℝ≥0∞) (s : Fin S) : ℝ≥0∞ :=
  if s = tgt then 0 else ∑ i, (M.P s (f s) i : ℝ≥0∞) * v i

end OptimisticDiameterProof

open MeasureTheory ProbabilityTheory BanditAlgorithm
open scoped ENNReal BigOperators

namespace OptimisticDiameterProof

lemma distribution_lintegral {S : ℕ} (d : MDPStateDistribution S)
    (g : Fin S → ℝ≥0∞) :
    ∫⁻ s, g s ∂d.toMeasure = ∑ s, (d.prob s : ℝ≥0∞) * g s := by
  rw [MDPStateDistribution.toMeasure, lintegral_finsetSum_measure]
  simp only [lintegral_smul_measure, lintegral_dirac, smul_eq_mul]

lemma trajectory_snoc {S A : ℕ} (M : FiniteMDP S A)
    (μ : MDPStateDistribution S) (f : Fin S → Fin A) (n : ℕ)
    (F : MDPTrajectory S A (n + 1) → ℝ≥0∞) :
    (∫⁻ h, F h ∂mdpMeasure M μ (mdpMemorylessDetPolicy f) (n + 1)) =
      ∫⁻ h, ∫⁻ s, F (Fin.snoc h (s, f s)) ∂mdpStateKernel M μ n h
        ∂mdpMeasure M μ (mdpMemorylessDetPolicy f) n := by
  rw [mdpMeasure, lintegral_map (measurable_of_countable _) measurable_mdpTrajectorySnoc,
    Measure.lintegral_compProd (measurable_of_countable _)]
  apply lintegral_congr
  intro h
  rw [mdpStepKernel, Kernel.lintegral_compProd _ _ _ (measurable_of_countable _)]
  simp only [mdpMemorylessDetPolicy, Kernel.lintegral_deterministic]

lemma trajectory_one {S A : ℕ} (M : FiniteMDP S A)
    (f : Fin S → Fin A) (src : Fin S)
    (F : MDPTrajectory S A 1 → ℝ≥0∞) :
    (∫⁻ h, F h ∂mdpMeasure M (mdpStateDirac src) (mdpMemorylessDetPolicy f) 1) =
      F (Fin.snoc (fun t : Fin 0 ↦ t.elim0) (src, f src)) := by
  rw [trajectory_snoc]
  simp [mdpMeasure, mdpStateKernel, distribution_lintegral, mdpStateDirac, apply_ite]

lemma trajectory_last_action {S A : ℕ} (M : FiniteMDP S A)
    (μ : MDPStateDistribution S) (f : Fin S → Fin A) (n : ℕ) :
    ∀ᵐ h ∂mdpMeasure M μ (mdpMemorylessDetPolicy f) (n + 1),
      (h (Fin.last n)).2 = f (h (Fin.last n)).1 := by
  have hz : (∫⁻ h, if (h (Fin.last n)).2 = f (h (Fin.last n)).1 then
      (0 : ℝ≥0∞) else 1 ∂mdpMeasure M μ (mdpMemorylessDetPolicy f) (n + 1)) = 0 := by
    rw [trajectory_snoc]
    simp
  have he := (lintegral_eq_zero_iff (measurable_of_countable _)).mp hz
  filter_upwards [he] with h hh
  by_contra hn
  simp [hn] at hh

lemma trajectory_row {S A : ℕ} (M : FiniteMDP S A)
    (μ : MDPStateDistribution S) (f : Fin S → Fin A) (n : ℕ)
    (F : MDPTrajectory S A (n + 2) → ℝ≥0∞) :
    (∫⁻ h, F h ∂mdpMeasure M μ (mdpMemorylessDetPolicy f) (n + 2)) =
      ∫⁻ h, ∑ s, (M.P (h (Fin.last n)).1 (f (h (Fin.last n)).1) s : ℝ≥0∞) *
        F (Fin.snoc h (s, f s)) ∂mdpMeasure M μ (mdpMemorylessDetPolicy f) (n + 1) := by
  rw [trajectory_snoc]
  apply lintegral_congr_ae
  filter_upwards [trajectory_last_action M μ f n] with h hh
  change (∫⁻ s, F (Fin.snoc h (s, f s))
    ∂(M.transitionDist (h (Fin.last n)).1 (h (Fin.last n)).2).toMeasure) = _
  rw [distribution_lintegral]
  simp only [FiniteMDP.transitionDist]
  rw [hh]

end OptimisticDiameterProof

open MeasureTheory ProbabilityTheory BanditAlgorithm
open scoped ENNReal BigOperators

namespace OptimisticDiameterProof

noncomputable def avoidWeighted {S A n : ℕ} (tgt : Fin S) (v : Fin S → ℝ≥0∞)
    (h : MDPTrajectory S A (n + 1)) : ℝ≥0∞ :=
  if ∀ t, (h t).1 ≠ tgt then v (h (Fin.last n)).1 else 0

lemma avoid_snoc {S A n : ℕ} (f : Fin S → Fin A) (tgt : Fin S)
    (v : Fin S → ℝ≥0∞) (hv : v tgt = 0) (h : MDPTrajectory S A (n + 1))
    (s : Fin S) :
    avoidWeighted tgt v (Fin.snoc h (s, f s)) =
      if ∀ t, (h t).1 ≠ tgt then v s else 0 := by
  have hc : (∀ t, ((Fin.snoc (α := fun _ ↦ Fin S × Fin A) h (s, f s)) t).1 ≠ tgt) ↔
      s ≠ tgt ∧ ∀ t, (h t).1 ≠ tgt := by
    rw [Fin.forall_iff_castSucc]
    simp only [Fin.snoc_last, Fin.snoc_castSucc]
  unfold avoidWeighted
  simp only [hc]
  simp only [Fin.snoc_last]
  by_cases hh : ∀ t, (h t).1 ≠ tgt
  · by_cases hs : s = tgt
    · simp [hh, hs, hv]
    · simp [hh, hs]
  · simp [hh]

lemma avoid_step {S A n : ℕ} (M : FiniteMDP S A) (f : Fin S → Fin A)
    (tgt : Fin S) (v : Fin S → ℝ≥0∞) (hv : v tgt = 0)
    (h : MDPTrajectory S A (n + 1)) :
    (∑ s, (M.P (h (Fin.last n)).1 (f (h (Fin.last n)).1) s : ℝ≥0∞) *
      avoidWeighted tgt v (Fin.snoc h (s, f s))) =
      avoidWeighted tgt (killedStep M f tgt v) h := by
  simp_rw [avoid_snoc f tgt v hv]
  by_cases hh : ∀ t, (h t).1 ≠ tgt
  · simp only [avoidWeighted, if_pos hh, killedStep, if_neg (hh (Fin.last n))]
  · simp only [avoidWeighted, if_neg hh, mul_zero, Finset.sum_const_zero]

theorem avoidance_iterate {S A : ℕ} (M : FiniteMDP S A) (f : Fin S → Fin A)
    (src tgt : Fin S) (n : ℕ) (v : Fin S → ℝ≥0∞) (hv : v tgt = 0) :
    (∫⁻ h, avoidWeighted tgt v h
      ∂mdpMeasure M (mdpStateDirac src) (mdpMemorylessDetPolicy f) (n + 1)) =
      ((killedStep M f tgt)^[n]) v src := by
  induction n generalizing v with
  | zero =>
      rw [trajectory_one]
      by_cases hs : src = tgt
      · subst src
        simp [avoidWeighted, Fin.snoc_zero, hv]
      · simp [avoidWeighted, Fin.snoc_zero, hs]
  | succ n ih =>
      rw [trajectory_row]
      simp_rw [avoid_step M f tgt v hv]
      rw [ih _ (by simp [killedStep])]
      rw [Function.iterate_succ_apply]

noncomputable def survival {S A : ℕ} (M : FiniteMDP S A)
    (f : Fin S → Fin A) (tgt : Fin S) (n : ℕ) : Fin S → ℝ≥0∞ :=
  ((killedStep M f tgt)^[n]) (fun s ↦ if s = tgt then 0 else 1)

theorem avoidance_probability {S A : ℕ} (M : FiniteMDP S A)
    (f : Fin S → Fin A) (src tgt : Fin S) (n : ℕ) :
    mdpMeasure M (mdpStateDirac src) (mdpMemorylessDetPolicy f) (n + 1)
      {h | ∀ t, (h t).1 ≠ tgt} = survival M f tgt n src := by
  unfold survival
  rw [← avoidance_iterate M f src tgt n _ (by simp)]
  have he : (avoidWeighted tgt (fun s ↦ if s = tgt then 0 else 1) :
      MDPTrajectory S A (n + 1) → ℝ≥0∞) =
      {h : MDPTrajectory S A (n + 1) | ∀ t, (h t).1 ≠ tgt}.indicator (fun _ ↦ 1) := by
    funext h
    by_cases hh : ∀ t, (h t).1 ≠ tgt
    · simp [avoidWeighted, hh]
    · simp [avoidWeighted, hh]
  rw [he, lintegral_indicator_const (Set.to_countable _).measurableSet (1 : ℝ≥0∞), one_mul]

lemma survival_zero {S A : ℕ} (M : FiniteMDP S A) (f : Fin S → Fin A)
    (tgt s : Fin S) : survival M f tgt 0 s = if s = tgt then 0 else 1 := rfl

lemma survival_succ {S A : ℕ} (M : FiniteMDP S A) (f : Fin S → Fin A)
    (tgt : Fin S) (n : ℕ) :
    survival M f tgt (n + 1) = killedStep M f tgt (survival M f tgt n) := by
  exact Function.iterate_succ_apply' _ _ _

lemma survival_self {S A : ℕ} (M : FiniteMDP S A) (f : Fin S → Fin A)
    (tgt : Fin S) (n : ℕ) : survival M f tgt n tgt = 0 := by
  cases n with
  | zero => simp [survival_zero]
  | succ n => simp [survival_succ, killedStep]

theorem travel_eq_survival {S A : ℕ} (M : FiniteMDP S A)
    (f : Fin S → Fin A) (src tgt : Fin S) :
    mdpTravelTime M f src tgt = ∑' n, survival M f tgt n src := by
  unfold mdpTravelTime
  simp_rw [avoidance_probability]

end OptimisticDiameterProof

open MeasureTheory ProbabilityTheory BanditAlgorithm
open scoped ENNReal BigOperators

namespace OptimisticDiameterProof

theorem travel_self {S A : ℕ} (M : FiniteMDP S A)
    (f : Fin S → Fin A) (tgt : Fin S) :
    mdpTravelTime M f tgt tgt = 0 := by
  rw [travel_eq_survival]
  simp only [survival_self, tsum_zero]

theorem travel_first {S A : ℕ} (M : FiniteMDP S A)
    (f : Fin S → Fin A) (src tgt : Fin S) (hne : src ≠ tgt) :
    mdpTravelTime M f src tgt =
      1 + ∑ i, (M.P src (f src) i : ℝ≥0∞) * mdpTravelTime M f i tgt := by
  simp_rw [travel_eq_survival]
  rw [tsum_eq_zero_add' ENNReal.summable]
  simp only [survival_zero, if_neg hne, survival_succ, killedStep]
  congr 1
  calc
    (∑' n, ∑ i, (M.P src (f src) i : ℝ≥0∞) * survival M f tgt n i) =
        ∑ i, ∑' n, (M.P src (f src) i : ℝ≥0∞) * survival M f tgt n i := by
      simpa only [tsum_fintype] using
        (ENNReal.tsum_comm (f := fun n i ↦ (M.P src (f src) i : ℝ≥0∞) * survival M f tgt n i))
    _ = _ := by simp only [ENNReal.tsum_mul_left]

lemma survival_partial_succ {S A : ℕ} (M : FiniteMDP S A)
    (f : Fin S → Fin A) (tgt : Fin S) (n : ℕ) (s : Fin S) :
    (∑ k ∈ Finset.range (n + 1), survival M f tgt k s) =
      survival M f tgt 0 s +
        killedStep M f tgt (fun i ↦ ∑ k ∈ Finset.range n, survival M f tgt k i) s := by
  rw [Finset.sum_range_succ', add_comm]
  congr 1
  simp only [survival_succ, killedStep]
  by_cases hs : s = tgt
  · simp [hs]
  · simp only [if_neg hs]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    rw [Finset.mul_sum]

theorem travel_le_of_ennreal_supersolution {S A : ℕ} (M : FiniteMDP S A)
    (f : Fin S → Fin A) (tgt : Fin S) (W : Fin S → ℝ≥0∞)
    (hzero : W tgt = 0)
    (hsuper : ∀ s, s ≠ tgt → 1 + ∑ i, (M.P s (f s) i : ℝ≥0∞) * W i ≤ W s) :
    ∀ src, mdpTravelTime M f src tgt ≤ W src := by
  have hpartial : ∀ n src, (∑ k ∈ Finset.range n, survival M f tgt k src) ≤ W src := by
    intro n
    induction n with
    | zero => intro src; simp
    | succ n ih =>
        intro src
        rw [survival_partial_succ]
        by_cases hs : src = tgt
        · subst src
          simp [survival_zero, killedStep, hzero]
        · simp only [survival_zero, killedStep, if_neg hs]
          refine (add_le_add le_rfl (Finset.sum_le_sum fun i _ ↦ ?_)).trans (hsuper src hs)
          gcongr
          exact ih i
  intro src
  rw [travel_eq_survival]
  exact ENNReal.tsum_le_of_sum_range_le (fun n ↦ hpartial n src)

theorem travel_le_of_supersolution {S A : ℕ} (M : FiniteMDP S A)
    (f : Fin S → Fin A) (tgt : Fin S) (V : Fin S → ℝ)
    (hV : ∀ s, 0 ≤ V s) (hzero : V tgt = 0)
    (hsuper : ∀ s, s ≠ tgt →
      1 + ∑ i, (M.P s (f s) i : ℝ) * V i ≤ V s) :
    ∀ src, mdpTravelTime M f src tgt ≤ ENNReal.ofReal (V src) := by
  apply travel_le_of_ennreal_supersolution M f tgt (fun s ↦ ENNReal.ofReal (V s))
  · simp [hzero]
  · intro s hs
    have hn : 0 ≤ ∑ i, (M.P s (f s) i : ℝ) * V i :=
      Finset.sum_nonneg fun i _ ↦ mul_nonneg (NNReal.coe_nonneg _) (hV i)
    have hsum : ENNReal.ofReal (∑ i, (M.P s (f s) i : ℝ) * V i) =
        ∑ i, (M.P s (f s) i : ℝ≥0∞) * ENNReal.ofReal (V i) := by
      rw [ENNReal.ofReal_sum_of_nonneg (fun i _ ↦
        mul_nonneg (NNReal.coe_nonneg _) (hV i))]
      apply Finset.sum_congr rfl
      intro i _
      rw [ENNReal.ofReal_mul (NNReal.coe_nonneg _), ENNReal.ofReal_coe_nnreal]
    have hc := ENNReal.ofReal_le_ofReal (hsuper s hs)
    rw [ENNReal.ofReal_add zero_le_one hn, ENNReal.ofReal_one, hsum] at hc
    exact hc

end OptimisticDiameterProof

noncomputable section
open scoped BigOperators ENNReal NNReal Topology
open MeasureTheory ProbabilityTheory BanditAlgorithm OptimisticPSRL.Diameter Filter
namespace OptimisticDiameterProof

variable {S A : ℕ}

def rowValue (M : FiniteMDP S A) (v : Fin S → ℝ) (s : Fin S) (a : Fin A) : ℝ :=
  ∑ i, (M.P s a i : ℝ) * v i

theorem rowValue_nonneg (M : FiniteMDP S A) {v : Fin S → ℝ}
    (hv : ∀ i, 0 ≤ v i) (s : Fin S) (a : Fin A) : 0 ≤ rowValue M v s a := by
  exact Finset.sum_nonneg fun i _ => mul_nonneg (NNReal.coe_nonneg _) (hv i)

theorem rowValue_mono (M : FiniteMDP S A) {v w : Fin S → ℝ}
    (h : v ≤ w) (s : Fin S) (a : Fin A) : rowValue M v s a ≤ rowValue M w s a := by
  exact Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (h i) (NNReal.coe_nonneg _)

theorem ofReal_rowValue (M : FiniteMDP S A) {v : Fin S → ℝ}
    (hv : ∀ i, 0 ≤ v i) (s : Fin S) (a : Fin A) :
    ENNReal.ofReal (rowValue M v s a) =
      ∑ i, (M.P s a i : ℝ≥0∞) * ENNReal.ofReal (v i) := by
  rw [rowValue, ENNReal.ofReal_sum_of_nonneg fun i _ =>
    mul_nonneg (NNReal.coe_nonneg _) (hv i)]
  simp only [ENNReal.ofReal_mul (NNReal.coe_nonneg _), ENNReal.ofReal_coe_nnreal]

variable [NeZero A]

def bellmanStep (M : FiniteMDP S A) (tgt : Fin S) (v : Fin S → ℝ) (s : Fin S) : ℝ :=
  if s = tgt then 0 else 1 + Finset.univ.inf' Finset.univ_nonempty (rowValue M v s)

def bellmanIter (M : FiniteMDP S A) (tgt : Fin S) : ℕ → Fin S → ℝ
  | 0 => 0
  | n + 1 => bellmanStep M tgt (bellmanIter M tgt n)

theorem bellmanStep_nonneg (M : FiniteMDP S A) (tgt : Fin S)
    {v : Fin S → ℝ} (hv : ∀ i, 0 ≤ v i) (s : Fin S) :
    0 ≤ bellmanStep M tgt v s := by
  unfold bellmanStep
  split_ifs
  · exact le_rfl
  · exact add_nonneg zero_le_one (Finset.le_inf' _ _ fun a _ => rowValue_nonneg M hv s a)

theorem bellmanStep_mono (M : FiniteMDP S A) (tgt : Fin S) :
    Monotone (bellmanStep M tgt) := by
  intro v w h s
  unfold bellmanStep
  split_ifs
  · exact le_rfl
  · apply add_le_add le_rfl
    apply Finset.le_inf'
    intro a ha
    exact (Finset.inf'_le _ ha).trans (rowValue_mono M h s a)

theorem bellmanStep_le_row (M : FiniteMDP S A) (tgt s : Fin S)
    (hne : s ≠ tgt) (v : Fin S → ℝ) (a : Fin A) :
    bellmanStep M tgt v s ≤ 1 + rowValue M v s a := by
  simp only [bellmanStep, if_neg hne]
  exact add_le_add le_rfl (Finset.inf'_le _ (Finset.mem_univ a))

theorem bellmanIter_nonneg (M : FiniteMDP S A) (tgt : Fin S) (n : ℕ) :
    ∀ s, 0 ≤ bellmanIter M tgt n s := by
  induction n with
  | zero => intro s; exact le_rfl
  | succ n ih => exact bellmanStep_nonneg M tgt ih

theorem bellmanIter_target (M : FiniteMDP S A) (tgt : Fin S) (n : ℕ) :
    bellmanIter M tgt n tgt = 0 := by
  cases n <;> simp [bellmanIter, bellmanStep]

theorem bellmanIter_mono (M : FiniteMDP S A) (tgt : Fin S) :
    Monotone (bellmanIter M tgt) := by
  apply monotone_nat_of_le_succ
  intro n
  induction n with
  | zero => exact bellmanIter_nonneg M tgt 1
  | succ n ih => exact bellmanStep_mono M tgt ih

theorem bellmanStep_tendsto (M : FiniteMDP S A) (tgt : Fin S)
    {v : ℕ → Fin S → ℝ} {V : Fin S → ℝ}
    (hv : ∀ s, Tendsto (fun n => v n s) atTop (𝓝 (V s))) (s : Fin S) :
    Tendsto (fun n => bellmanStep M tgt (v n) s) atTop
      (𝓝 (bellmanStep M tgt V s)) := by
  by_cases hs : s = tgt
  · simp only [bellmanStep, if_pos hs]
    exact tendsto_const_nhds
  · simp only [bellmanStep, if_neg hs]
    apply Tendsto.const_add
    apply Filter.Tendsto.finset_inf'_nhds_apply
    intro a _
    exact tendsto_finsetSum Finset.univ fun i _ => (hv i).const_mul (M.P s a i : ℝ)

def bellmanLimit (M : FiniteMDP S A) (tgt : Fin S) (s : Fin S) : ℝ :=
  ⨆ n, bellmanIter M tgt n s

theorem bellman_limit (M : FiniteMDP S A) (tgt : Fin S)
    (hb : ∀ s, BddAbove (Set.range fun n => bellmanIter M tgt n s)) :
    (∀ s, Tendsto (fun n => bellmanIter M tgt n s) atTop (𝓝 (bellmanLimit M tgt s))) ∧
    (∀ s, 0 ≤ bellmanLimit M tgt s) ∧ bellmanLimit M tgt tgt = 0 ∧
    bellmanStep M tgt (bellmanLimit M tgt) = bellmanLimit M tgt := by
  have ht s : Tendsto (fun n => bellmanIter M tgt n s) atTop
      (𝓝 (bellmanLimit M tgt s)) :=
    tendsto_atTop_ciSup (fun n m h => bellmanIter_mono M tgt h s) (hb s)
  refine ⟨ht, ?_, ?_, ?_⟩
  · intro s
    exact le_of_tendsto_of_tendsto tendsto_const_nhds (ht s)
      (Filter.Eventually.of_forall fun n => bellmanIter_nonneg M tgt n s)
  · exact tendsto_nhds_unique (ht tgt) (by
      simp only [bellmanIter_target]
      exact tendsto_const_nhds)
  · funext s
    have hn := (ht s).comp (tendsto_add_atTop_nat 1)
    exact tendsto_nhds_unique (bellmanStep_tendsto M tgt ht s) hn

theorem bellman_choice (M : FiniteMDP S A) (tgt : Fin S) (V : Fin S → ℝ)
    (hfix : bellmanStep M tgt V = V) :
    ∃ f : Fin S → Fin A, ∀ s, s ≠ tgt → V s = 1 + rowValue M V s (f s) := by
  classical
  have hex s : ∃ a : Fin A,
      Finset.univ.inf' Finset.univ_nonempty (rowValue M V s) = rowValue M V s a := by
    obtain ⟨a, _, ha⟩ := Finset.exists_mem_eq_inf' Finset.univ_nonempty (rowValue M V s)
    exact ⟨a, ha⟩
  choose f hf using hex
  refine ⟨f, fun s hs => ?_⟩
  have h := congrFun hfix s
  simpa only [bellmanStep, if_neg hs, hf s] using h.symm

end OptimisticDiameterProof

noncomputable section
open scoped BigOperators ENNReal NNReal Topology
open MeasureTheory ProbabilityTheory BanditAlgorithm OptimisticPSRL.Diameter Filter
namespace OptimisticDiameterProof

variable {S A : ℕ}

theorem minTravel_le_diameter (M : FiniteMDP S A) (src tgt : Fin S) (hne : src ≠ tgt) :
    minTravel M tgt src ≤ mdpDiameterENN M := by
  exact le_iSup_of_le src (le_iSup_of_le tgt (le_iSup_of_le hne le_rfl))

variable [NeZero A]

theorem minTravel_self (M : FiniteMDP S A) (tgt : Fin S) : minTravel M tgt tgt = 0 := by
  apply le_antisymm _ zero_le
  exact (iInf_le_of_le (fun _ => (0 : Fin A)) le_rfl).trans (travel_self M _ tgt).le

theorem bellmanIter_le_travel (M : FiniteMDP S A) (tgt : Fin S)
    (f : Fin S → Fin A) (n : ℕ) :
    ∀ src, ENNReal.ofReal (bellmanIter M tgt n src) ≤ mdpTravelTime M f src tgt := by
  induction n with
  | zero => intro src; simp [bellmanIter]
  | succ n ih =>
    intro src
    by_cases hs : src = tgt
    · subst src
      simp only [bellmanIter_target, ENNReal.ofReal_zero, zero_le]
    · calc
        ENNReal.ofReal (bellmanIter M tgt (n+1) src) ≤
            ENNReal.ofReal (1 + rowValue M (bellmanIter M tgt n) src (f src)) :=
          ENNReal.ofReal_le_ofReal (bellmanStep_le_row M tgt src hs _ _)
        _ = 1 + ∑ i, (M.P src (f src) i : ℝ≥0∞) *
            ENNReal.ofReal (bellmanIter M tgt n i) := by
          rw [ENNReal.ofReal_add zero_le_one (rowValue_nonneg M (bellmanIter_nonneg M tgt n) _ _),
            ENNReal.ofReal_one, ofReal_rowValue M (bellmanIter_nonneg M tgt n)]
        _ ≤ 1 + ∑ i, (M.P src (f src) i : ℝ≥0∞) * mdpTravelTime M f i tgt := by
          gcongr with i
          exact ih i
        _ = mdpTravelTime M f src tgt := (travel_first M f src tgt hs).symm

theorem bellmanIter_le_minTravel (M : FiniteMDP S A) (tgt : Fin S) (n : ℕ) (src : Fin S) :
    ENNReal.ofReal (bellmanIter M tgt n src) ≤ minTravel M tgt src := by
  exact le_iInf fun f => bellmanIter_le_travel M tgt f n src

theorem minTravel_le_finite_diameter (M : FiniteMDP S A) (tgt src : Fin S) :
    minTravel M tgt src ≤ mdpDiameterENN M := by
  by_cases hs : src = tgt
  · subst src
    rw [minTravel_self]
    exact zero_le
  · exact minTravel_le_diameter M src tgt hs

theorem exists_bellman_value (M : FiniteMDP S A) (tgt : Fin S)
    (hD : mdpDiameterENN M ≠ ⊤) :
    ∃ (V : Fin S → ℝ) (f : Fin S → Fin A),
      (∀ s, 0 ≤ V s) ∧ V tgt = 0 ∧
      (∀ s, ENNReal.ofReal (V s) = minTravel M tgt s) ∧
      (∀ s, s ≠ tgt → V s = 1 + ∑ i, (M.P s (f s) i : ℝ) * V i) := by
  have hb s : BddAbove (Set.range fun n => bellmanIter M tgt n s) := by
    refine ⟨(mdpDiameterENN M).toReal, ?_⟩
    rintro _ ⟨n, rfl⟩
    exact (ENNReal.ofReal_le_iff_le_toReal hD).mp
      ((bellmanIter_le_minTravel M tgt n s).trans (minTravel_le_finite_diameter M tgt s))
  obtain ⟨ht, hv, hz, hfix⟩ := bellman_limit M tgt hb
  obtain ⟨f, hf⟩ := bellman_choice M tgt (bellmanLimit M tgt) hfix
  have hlow s : ENNReal.ofReal (bellmanLimit M tgt s) ≤ minTravel M tgt s :=
    le_of_tendsto' (ENNReal.tendsto_ofReal (ht s)) fun n => bellmanIter_le_minTravel M tgt n s
  have hu := travel_le_of_supersolution M f tgt (bellmanLimit M tgt) hv hz
    (fun s hs => (hf s hs).ge)
  refine ⟨bellmanLimit M tgt, f, hv, hz, ?_, hf⟩
  intro s
  exact le_antisymm (hlow s) ((iInf_le_of_le f le_rfl).trans (hu s))

end OptimisticDiameterProof

noncomputable section
open scoped BigOperators ENNReal NNReal
open MeasureTheory ProbabilityTheory BanditAlgorithm OptimisticPSRL.Diameter
namespace OptimisticDiameterProof

theorem extended_diameter_finite {S A ψ : ℕ} [NeZero A] [NeZero ψ]
    (M : FiniteMDP S A) (Q : Fin S → Fin A → Fin ψ → Fin S → ℝ≥0)
    (hQ : ∀ s a j, ∑ i, Q s a j i = 1) (δ : ℝ≥0) (hδ : δ < 1)
    (hD : mdpDiameterENN M ≠ ⊤)
    (h16 : ∀ tgt s : Fin S, ∀ a : Fin A, ∃ j : Fin ψ,
      ∑ i, (Q s a j i : ℝ≥0∞) * minTravel M tgt i ≤
        ∑ i, (M.P s a i : ℝ≥0∞) * minTravel M tgt i + δ) :
    mdpDiameterENN (extendedMDP M Q hQ) ≤
      mdpDiameterENN M / ((1 - δ : ℝ≥0) : ℝ≥0∞) := by
  classical
  have _ := NeZero.ne ψ
  let d : ℝ := 1 - (δ : ℝ)
  have hd : 0 < d := sub_pos.mpr (by exact_mod_cast hδ)
  have hden : ENNReal.ofReal d = ((1 - δ : ℝ≥0) : ℝ≥0∞) := by
    have hc : ((1 - δ : ℝ≥0) : ℝ) = d := by simp [NNReal.coe_sub hδ.le, d]
    rw [← hc, ENNReal.ofReal_coe_nnreal]
  refine iSup_le fun src => iSup_le fun tgt => iSup_le fun hne => ?_
  obtain ⟨V, f, hv, hz, hvalue, hf⟩ := exists_bellman_value M tgt hD
  choose j hj using fun s => h16 tgt s (f s)
  let g : Fin S → Fin (A * ψ) := fun s => extendedAction (f s) (j s)
  have hsample s : rowValue (extendedMDP M Q hQ) V s (g s) ≤
      rowValue M V s (f s) + (δ : ℝ) := by
    apply (ENNReal.ofReal_le_ofReal_iff
      (add_nonneg (rowValue_nonneg M hv s (f s)) δ.coe_nonneg)).mp
    rw [ofReal_rowValue _ hv, ENNReal.ofReal_add (rowValue_nonneg M hv _ _) δ.coe_nonneg,
      ofReal_rowValue _ hv, ENNReal.ofReal_coe_nnreal]
    simpa only [g, extendedMDP_P_extendedAction, hvalue] using hj s
  have hsuper s (hs : s ≠ tgt) :
      1 + ∑ i, ((extendedMDP M Q hQ).P s (g s) i : ℝ) * (V i / d) ≤ V s / d := by
    have hb : d + rowValue (extendedMDP M Q hQ) V s (g s) ≤ V s := by
      have hm := hf s hs
      have hq := hsample s
      dsimp only [d]
      change V s = 1 + rowValue M V s (f s) at hm
      linarith
    calc
      1 + ∑ i, ((extendedMDP M Q hQ).P s (g s) i : ℝ) * (V i / d) =
          (d + rowValue (extendedMDP M Q hQ) V s (g s)) / d := by
        simp only [rowValue, ← mul_div_assoc, ← Finset.sum_div]
        field_simp [hd.ne']
      _ ≤ V s / d := div_le_div_of_nonneg_right hb hd.le
  have hu := travel_le_of_supersolution (extendedMDP M Q hQ) g tgt
    (fun s => V s / d) (fun s => div_nonneg (hv s) hd.le) (by rw [hz, zero_div]) hsuper
  calc
    (⨅ f', mdpTravelTime (extendedMDP M Q hQ) f' src tgt) ≤
        mdpTravelTime (extendedMDP M Q hQ) g src tgt := iInf_le _ g
    _ ≤ ENNReal.ofReal (V src / d) := hu src
    _ = minTravel M tgt src / ((1 - δ : ℝ≥0) : ℝ≥0∞) := by
      rw [ENNReal.ofReal_div_of_pos hd, hvalue, hden]
    _ ≤ mdpDiameterENN M / ((1 - δ : ℝ≥0) : ℝ≥0∞) :=
      ENNReal.div_le_div_right (minTravel_le_diameter M src tgt hne) _

end OptimisticDiameterProof

open BanditAlgorithm NNReal ENNReal
namespace OptimisticPSRL.Diameter
theorem lemma5_6_extended_diameter_le {S A ψ : ℕ} (M : FiniteMDP S A)
    (Q : Fin S → Fin A → Fin ψ → Fin S → ℝ≥0) (hQ : ∀ s a j, ∑ i, Q s a j i = 1)
    (δ : ℝ≥0) (hδ : δ < 1)
    (h16 : ∀ tgt s : Fin S, ∀ a : Fin A, ∃ j : Fin ψ,
      ∑ i, (Q s a j i : ℝ≥0∞) * minTravel M tgt i ≤
        ∑ i, (M.P s a i : ℝ≥0∞) * minTravel M tgt i + δ) :
    mdpDiameterENN (extendedMDP M Q hQ) ≤ mdpDiameterENN M / ((1 - δ : ℝ≥0) : ℝ≥0∞) := by
  classical
  by_cases hpair : ∃ src tgt : Fin S, src ≠ tgt
  · by_cases hD : mdpDiameterENN M = ⊤
    · simp only [hD, ENNReal.top_div_coe, le_top]
    · obtain ⟨src, tgt, hne⟩ := hpair
      have hA : A ≠ 0 := by
        intro hz
        subst A
        let : IsEmpty (Fin S → Fin 0) := ⟨fun f => Fin.elim0 (f src)⟩
        have hi : (⨅ f : Fin S → Fin 0, mdpTravelTime M f src tgt) = ⊤ := by simp
        have ht : (⊤ : ℝ≥0∞) ≤ mdpDiameterENN M := by
          rw [← hi]
          exact le_iSup_of_le src (le_iSup_of_le tgt (le_iSup_of_le hne le_rfl))
        exact hD (top_unique ht)
      let : NeZero A := ⟨hA⟩
      have hψ : ψ ≠ 0 := by
        intro hz
        subst ψ
        obtain ⟨j, _⟩ := h16 tgt src (0 : Fin A)
        exact Fin.elim0 j
      let : NeZero ψ := ⟨hψ⟩
      exact OptimisticDiameterProof.extended_diameter_finite M Q hQ δ hδ hD h16
  · have hz : mdpDiameterENN (extendedMDP M Q hQ) = 0 := by
      apply le_antisymm _ zero_le
      refine iSup_le fun src => iSup_le fun tgt => iSup_le fun hne => ?_
      exact False.elim (hpair ⟨src, tgt, hne⟩)
    rw [hz]
    exact zero_le
end OptimisticPSRL.Diameter

open OptimisticPSRL.Diameter

theorem solution {S A ψ : ℕ} (M : FiniteMDP S A)
    (Q : Fin S → Fin A → Fin ψ → Fin S → ℝ≥0) (hQ : ∀ s a j, ∑ i, Q s a j i = 1)
    (δ : ℝ≥0) (hδ : δ < 1)
    (h16 : ∀ tgt s : Fin S, ∀ a : Fin A, ∃ j : Fin ψ,
      ∑ i, (Q s a j i : ℝ≥0∞) * minTravel M tgt i ≤
        ∑ i, (M.P s a i : ℝ≥0∞) * minTravel M tgt i + δ) :
    mdpDiameterENN (extendedMDP M Q hQ) ≤ mdpDiameterENN M / ((1 - δ : ℝ≥0) : ℝ≥0∞) := by
  exact OptimisticPSRL.Diameter.lemma5_6_extended_diameter_le M Q hQ δ hδ h16
