-- Prove2me | solution 1 for WeberGittins.Suboptimality.theorem2_suboptimality_bound
-- status  : ACCEPTED   (prove)
-- author  : @sometik179
-- created : 2026-10-25T04:18:12.532241+00:00
-- url     : https://prove2.me/submissions/bd7ba155-1a53-4ab5-8e86-b1c71ccfd120

import Mathlib
import Definitions.Def_WeberGittins_Suboptimality_Model

-- BEGIN GittinsProof.StoppingBounds
open MeasureTheory ProbabilityTheory BanditAlgorithm
namespace GittinsProof
variable {S : Type*} [MeasurableSpace S]

theorem stopping_event_measurable {τ : (ℕ → S) → ℕ∞}
    (hτ : IsTrajStoppingTime τ) (n : ℕ) :
    MeasurableSet {ω | (n : ℕ∞) < τ ω} := by
  have h : MeasurableSet {ω | τ ω ≤ (n : ℕ∞)} := by
    obtain ⟨s, hs, heq⟩ := MeasurableSpace.measurableSet_comap.mp (hτ n)
    rw [← heq]
    exact (measurable_pi_lambda _ fun i => measurable_pi_apply i.val) hs
  simpa only [Set.compl_ofPred, not_le] using h.compl

theorem stopped_measurable {f : S → ℝ} (hf : Measurable f)
    (β : ℝ) {τ : (ℕ → S) → ℕ∞} (hτ : IsTrajStoppingTime τ) :
    Measurable (discountedStoppedSum β f τ) := by
  apply Measurable.tsum
  intro n
  exact Measurable.ite (stopping_event_measurable hτ n)
    (measurable_const.mul (hf.comp (measurable_pi_apply n))) measurable_const

omit [MeasurableSpace S] in
theorem stopped_term_bound {f : S → ℝ} {M β : ℝ} (hM : 0 ≤ M)
    (hf : ∀ x, |f x| ≤ M) (hβ : 0 ≤ β)
    (τ : (ℕ → S) → ℕ∞) (ω : ℕ → S) (n : ℕ) :
    ‖if (n : ℕ∞) < τ ω then β ^ n * f (ω n) else 0‖ ≤ M * β ^ n := by
  split_ifs
  · simpa only [Real.norm_eq_abs, abs_mul, abs_of_nonneg (pow_nonneg hβ n),
      mul_comm] using mul_le_mul_of_nonneg_left (hf (ω n)) (pow_nonneg hβ n)
  · simp only [norm_zero]
    positivity

omit [MeasurableSpace S] in
theorem stopped_summable {f : S → ℝ} {M β : ℝ} (hM : 0 ≤ M)
    (hf : ∀ x, |f x| ≤ M) (hβ : 0 ≤ β) (hβ1 : β < 1)
    (τ : (ℕ → S) → ℕ∞) (ω : ℕ → S) :
    Summable (fun n : ℕ => if (n : ℕ∞) < τ ω then β ^ n * f (ω n) else 0) := by
  exact ((summable_geometric_of_abs_lt_one (by rwa [abs_of_nonneg hβ])).mul_left M).of_norm_bounded
    (stopped_term_bound hM hf hβ τ ω)

omit [MeasurableSpace S] in
theorem stopped_bound {f : S → ℝ} {M β : ℝ} (hM : 0 ≤ M)
    (hf : ∀ x, |f x| ≤ M) (hβ : 0 ≤ β) (hβ1 : β < 1)
    (τ : (ℕ → S) → ℕ∞) (ω : ℕ → S) :
    |discountedStoppedSum β f τ ω| ≤ M / (1 - β) := by
  have hs := stopped_summable hM hf hβ hβ1 τ ω
  have hg := (summable_geometric_of_abs_lt_one (by rwa [abs_of_nonneg hβ])).mul_left M
  calc
    |discountedStoppedSum β f τ ω| ≤
        ∑' n : ℕ, ‖if (n : ℕ∞) < τ ω then β ^ n * f (ω n) else 0‖ :=
      norm_tsum_le_tsum_norm hs.norm
    _ ≤ ∑' n : ℕ, M * β ^ n :=
      Summable.tsum_le_tsum (stopped_term_bound hM hf hβ τ ω) hs.norm hg
    _ = M / (1 - β) := by
      rw [tsum_mul_left, tsum_geometric_of_abs_lt_one (by rwa [abs_of_nonneg hβ])]
      rfl

theorem stopped_integrable {f : S → ℝ} {M β : ℝ} (hM : 0 ≤ M)
    (hf : ∀ x, |f x| ≤ M) (hm : Measurable f) (hβ : 0 ≤ β) (hβ1 : β < 1)
    {τ : (ℕ → S) → ℕ∞} (hτ : IsTrajStoppingTime τ)
    (μ : Measure (ℕ → S)) [IsFiniteMeasure μ] :
    Integrable (discountedStoppedSum β f τ) μ := by
  refine (integrable_const (M / (1 - β))).mono'
    (stopped_measurable hm β hτ).aestronglyMeasurable ?_
  exact Filter.Eventually.of_forall fun ω => stopped_bound hM hf hβ hβ1 τ ω

theorem stopped_expectation_bound {f : S → ℝ} {M β : ℝ} (hM : 0 ≤ M)
    (hf : ∀ x, |f x| ≤ M) (hβ : 0 ≤ β) (hβ1 : β < 1)
    (τ : (ℕ → S) → ℕ∞) (μ : Measure (ℕ → S)) [IsProbabilityMeasure μ] :
    |∫ ω, discountedStoppedSum β f τ ω ∂μ| ≤ M / (1 - β) := by
  simpa using
    (norm_integral_le_of_norm_le_const (μ := μ) (f := discountedStoppedSum β f τ)
      (C := M / (1 - β))
      (Filter.Eventually.of_forall fun ω => stopped_bound hM hf hβ hβ1 τ ω))

omit [MeasurableSpace S] in
theorem reward_charge_bound {r : S → ℝ} {C : ℝ}
    (hr : ∀ x, 0 ≤ r x ∧ r x ≤ C) (c : ℝ) (x : S) :
    |r x - c| ≤ C + |c| := by
  calc
    |r x - c| ≤ |r x| + |c| := abs_sub (r x) c
    _ ≤ C + |c| := by rw [abs_of_nonneg (hr x).1]; linarith [(hr x).2]
end GittinsProof
-- END GittinsProof.StoppingBounds

-- BEGIN GittinsProof.StoppingTail
open MeasureTheory ProbabilityTheory BanditAlgorithm
namespace GittinsProof
variable {S : Type*}

theorem stopped_tail_bound {f : S → ℝ} {M β : ℝ} (hM : 0 ≤ M)
    (hf : ∀ x, |f x| ≤ M) (hβ : 0 ≤ β) (hβ1 : β < 1)
    (τ : (ℕ → S) → ℕ∞) (ω : ℕ → S) (N : ℕ) :
    |discountedStoppedSum β f τ ω -
      ∑ t ∈ Finset.range N, if (t : ℕ∞) < τ ω then β ^ t * f (ω t) else 0| ≤
      M * β ^ N / (1 - β) := by
  let a := fun n : ℕ => if (n : ℕ∞) < τ ω then β ^ n * f (ω n) else 0
  have hs : Summable a := stopped_summable hM hf hβ hβ1 τ ω
  have hb (n : ℕ) : ‖a (n + N)‖ ≤ (M * β ^ N) * β ^ n := by
    calc
      ‖a (n + N)‖ ≤ M * β ^ (n + N) := stopped_term_bound hM hf hβ τ ω (n + N)
      _ = (M * β ^ N) * β ^ n := by rw [pow_add]; ring
  have hg := (summable_geometric_of_abs_lt_one (by rwa [abs_of_nonneg hβ])).mul_left (M * β ^ N)
  have htail := hg.of_norm_bounded hb
  have heq : discountedStoppedSum β f τ ω - ∑ t ∈ Finset.range N, a t =
      ∑' n : ℕ, a (n + N) := by
    have h := Summable.sum_add_tsum_nat_add N hs
    change ∑' n, a n - _ = _
    linarith
  change |discountedStoppedSum β f τ ω - ∑ t ∈ Finset.range N, a t| ≤ _
  rw [heq]
  calc
    |∑' n : ℕ, a (n + N)| ≤ ∑' n : ℕ, ‖a (n + N)‖ := norm_tsum_le_tsum_norm htail.norm
    _ ≤ ∑' n : ℕ, (M * β ^ N) * β ^ n := Summable.tsum_le_tsum hb htail.norm hg
    _ = M * β ^ N / (1 - β) := by
      rw [tsum_mul_left, tsum_geometric_of_abs_lt_one (by rwa [abs_of_nonneg hβ])]
      rfl

theorem stopped_nonneg {f : S → ℝ} (hf : ∀ x, 0 ≤ f x) {β : ℝ} (hβ : 0 ≤ β)
    (τ : (ℕ → S) → ℕ∞) (ω : ℕ → S) : 0 ≤ discountedStoppedSum β f τ ω := by
  apply tsum_nonneg
  intro n
  split_ifs
  · exact mul_nonneg (pow_nonneg hβ _) (hf _)
  · exact le_rfl

theorem stopped_duration_ge_one {β : ℝ} (hβ : 0 ≤ β) (hβ1 : β < 1)
    (τ : (ℕ → S) → ℕ∞) (hτ1 : ∀ ω, 1 ≤ τ ω) (ω : ℕ → S) :
    1 ≤ discountedStoppedSum β (fun _ : S => (1 : ℝ)) τ ω := by
  have hs := stopped_summable (f := fun _ : S => (1 : ℝ)) (M := 1) (by norm_num) (fun _ => by norm_num) hβ hβ1 τ ω
  have h0 : (0 : ℕ∞) < τ ω := lt_of_lt_of_le (by norm_num) (hτ1 ω)
  have ht : 0 ≤ ∑' n : ℕ, if ((n + 1 : ℕ) : ℕ∞) < τ ω then β ^ (n + 1) * (1 : ℝ) else 0 := by
    apply tsum_nonneg
    intro n
    split_ifs <;> positivity
  have heq := hs.tsum_eq_zero_add
  simp only [Nat.cast_zero, h0, ↓reduceIte, pow_zero, mul_one] at heq
  change 1 ≤ ∑' n : ℕ, if (n : ℕ∞) < τ ω then β ^ n * 1 else 0
  simp only [mul_one] at ht ⊢
  linarith

variable [MeasurableSpace S]

theorem stopping_one : IsTrajStoppingTime (fun _ : ℕ → S => (1 : ℕ∞)) := by
  intro n
  by_cases hn : (1 : ℕ∞) ≤ n <;> simp [hn]

theorem stopped_duration_expectation_bounds {β : ℝ} (hβ : 0 ≤ β) (hβ1 : β < 1)
    {τ : (ℕ → S) → ℕ∞} (hτ : IsTrajStoppingTime τ) (hτ1 : ∀ ω, 1 ≤ τ ω)
    (μ : Measure (ℕ → S)) [IsProbabilityMeasure μ] :
    1 ≤ ∫ ω, discountedStoppedSum β (fun _ : S => (1 : ℝ)) τ ω ∂μ ∧
    (∫ ω, discountedStoppedSum β (fun _ : S => (1 : ℝ)) τ ω ∂μ) ≤ 1 / (1 - β) := by
  have hi := stopped_integrable (f := fun _ : S => (1 : ℝ)) (M := 1) (by norm_num) (fun _ : S => by norm_num)
    measurable_const hβ hβ1 hτ μ
  constructor
  · simpa using integral_mono (integrable_const (1 : ℝ)) hi (stopped_duration_ge_one hβ hβ1 τ hτ1)
  · exact le_trans (le_abs_self _) (stopped_expectation_bound (f := fun _ : S => (1 : ℝ)) (M := 1) (by norm_num)
      (fun _ : S => by norm_num) hβ hβ1 τ μ)
end GittinsProof
-- END GittinsProof.StoppingTail

-- BEGIN GittinsProof.ChainBasics
open MeasureTheory ProbabilityTheory BanditAlgorithm
namespace GittinsProof
variable {S : Type*} [MeasurableSpace S]

instance chain_probability (P : Kernel S S) [IsMarkovKernel P] (x : S) :
    IsProbabilityMeasure (markovChainMeasure P x) := by
  unfold markovChainMeasure
  infer_instance

theorem chain_eq_traj (P : Kernel S S) [IsMarkovKernel P] (x : S) :
    markovChainMeasure P x = Kernel.traj (markovChainStep P) 0 (fun _ => x) := by
  rw [markovChainMeasure, Kernel.trajMeasure, Measure.map_dirac' (by fun_prop)]
  change (Measure.dirac _).bind _ = _
  rw [Measure.dirac_bind (Kernel.measurable _)]
  rfl

theorem chain_prefix (P : Kernel S S) [IsMarkovKernel P] (x : S) (n : ℕ) :
    (markovChainMeasure P x).map (Preorder.frestrictLe n) =
      Kernel.partialTraj (X := fun _ => S) (markovChainStep P) 0 n (fun _ => x) := by
  rw [chain_eq_traj, Kernel.traj_map_frestrictLe_apply]

theorem chain_prefix_next (P : Kernel S S) [IsMarkovKernel P] (x : S) (n : ℕ) :
    ((markovChainMeasure P x).map (Preorder.frestrictLe n)).compProd (markovChainStep P n) =
      (markovChainMeasure P x).map (fun ω => (Preorder.frestrictLe n ω, ω (n + 1))) :=
  Kernel.map_frestrictLe_trajMeasure_compProd_eq_map_trajMeasure
end GittinsProof
-- END GittinsProof.ChainBasics

-- BEGIN GittinsProof.StoppedAlgebra
open MeasureTheory ProbabilityTheory BanditAlgorithm
namespace GittinsProof
variable {S : Type*}

theorem stopped_const (β c : ℝ) (τ : (ℕ → S) → ℕ∞) (ω : ℕ → S) :
    discountedStoppedSum β (fun _ : S => c) τ ω =
      c * discountedStoppedSum β (fun _ : S => (1 : ℝ)) τ ω := by
  rw [discountedStoppedSum, discountedStoppedSum, ← tsum_mul_left]
  apply tsum_congr
  intro n
  split_ifs <;> ring

theorem stopped_sub_const {f : S → ℝ} {M β : ℝ} (hM : 0 ≤ M)
    (hf : ∀ x, |f x| ≤ M) (hβ : 0 ≤ β) (hβ1 : β < 1)
    (c : ℝ) (τ : (ℕ → S) → ℕ∞) (ω : ℕ → S) :
    discountedStoppedSum β (fun y => f y - c) τ ω =
      discountedStoppedSum β f τ ω - c * discountedStoppedSum β (fun _ : S => (1 : ℝ)) τ ω := by
  rw [← stopped_const β c τ ω]
  have hs := stopped_summable hM hf hβ hβ1 τ ω
  have hc := stopped_summable (f := fun _ : S => c) (abs_nonneg c) (fun _ => le_rfl) hβ hβ1 τ ω
  rw [discountedStoppedSum, discountedStoppedSum, discountedStoppedSum, ← hs.tsum_sub hc]
  apply tsum_congr
  intro n
  split_ifs <;> ring

theorem stopped_reward_le_duration {r : S → ℝ} {C β : ℝ} (hC : 0 ≤ C)
    (hr : ∀ x, 0 ≤ r x ∧ r x ≤ C) (hβ : 0 ≤ β) (hβ1 : β < 1)
    (τ : (ℕ → S) → ℕ∞) (ω : ℕ → S) :
    discountedStoppedSum β r τ ω ≤ C * discountedStoppedSum β (fun _ : S => (1 : ℝ)) τ ω := by
  rw [← stopped_const β C τ ω]
  have hs := stopped_summable hC (fun x => by rw [abs_of_nonneg (hr x).1]; exact (hr x).2) hβ hβ1 τ ω
  have hc := stopped_summable (f := fun _ : S => C) hC (fun _ => by rw [abs_of_nonneg hC]) hβ hβ1 τ ω
  apply Summable.tsum_le_tsum _ hs hc
  intro n
  split_ifs
  · exact mul_le_mul_of_nonneg_left (hr _).2 (pow_nonneg hβ _)
  · exact le_rfl
end GittinsProof
-- END GittinsProof.StoppedAlgebra

-- BEGIN GittinsProof.RetirementBounds
open MeasureTheory ProbabilityTheory BanditAlgorithm
namespace GittinsProof
variable {S : Type*} [MeasurableSpace S]

theorem retirement_set_bdd (P : Kernel S S) [IsMarkovKernel P] (r : S → ℝ)
    {β c M : ℝ} (hβ : 0 ≤ β) (hβ1 : β < 1) (hM : 0 ≤ M)
    (hr : ∀ y, |r y - c| ≤ M) (x : S) :
    BddAbove (insert 0 {v : ℝ | ∃ τ : (ℕ → S) → ℕ∞,
      IsTrajStoppingTime τ ∧ (∀ ω, 1 ≤ τ ω) ∧
      v = ∫ ω, discountedStoppedSum β (fun y => r y - c) τ ω ∂markovChainMeasure P x}) := by
  refine ⟨M / (1 - β), ?_⟩
  intro v hv
  rcases hv with rfl | ⟨τ, _, _, rfl⟩
  · positivity
  · exact (le_abs_self _).trans (stopped_expectation_bound hM hr hβ hβ1 τ (markovChainMeasure P x))

theorem retirement_nonneg (P : Kernel S S) [IsMarkovKernel P] (r : S → ℝ)
    {β c M : ℝ} (hβ : 0 ≤ β) (hβ1 : β < 1) (hM : 0 ≤ M)
    (hr : ∀ y, |r y - c| ≤ M) (x : S) :
    0 ≤ gittinsRetirementValue P r β c x :=
  le_csSup (retirement_set_bdd P r hβ hβ1 hM hr x) (Set.mem_insert _ _)

theorem retirement_bound (P : Kernel S S) [IsMarkovKernel P] (r : S → ℝ)
    {β c M : ℝ} (hβ : 0 ≤ β) (hβ1 : β < 1) (hM : 0 ≤ M)
    (hr : ∀ y, |r y - c| ≤ M) (x : S) :
    gittinsRetirementValue P r β c x ≤ M / (1 - β) := by
  apply csSup_le (Set.insert_nonempty _ _)
  intro v hv
  rcases hv with rfl | ⟨τ, _, _, rfl⟩
  · positivity
  · exact (le_abs_self _).trans (stopped_expectation_bound hM hr hβ hβ1 τ (markovChainMeasure P x))

theorem stopped_le_retirement (P : Kernel S S) [IsMarkovKernel P] (r : S → ℝ)
    {β c M : ℝ} (hβ : 0 ≤ β) (hβ1 : β < 1) (hM : 0 ≤ M)
    (hr : ∀ y, |r y - c| ≤ M) (x : S)
    {τ : (ℕ → S) → ℕ∞} (hτ : IsTrajStoppingTime τ) (hτ1 : ∀ ω, 1 ≤ τ ω) :
    (∫ ω, discountedStoppedSum β (fun y => r y - c) τ ω ∂markovChainMeasure P x) ≤
      gittinsRetirementValue P r β c x :=
  le_csSup (retirement_set_bdd P r hβ hβ1 hM hr x) (Set.mem_insert_of_mem 0 ⟨τ, hτ, hτ1, rfl⟩)
end GittinsProof
-- END GittinsProof.RetirementBounds

-- BEGIN GittinsProof.IndexBounds
open MeasureTheory ProbabilityTheory BanditAlgorithm
namespace GittinsProof
variable {S : Type*} [MeasurableSpace S]

theorem stopped_net_integral (P : Kernel S S) [IsMarkovKernel P] (x : S)
    {r : S → ℝ} (hrm : Measurable r) {β C : ℝ} (hβ : 0 ≤ β) (hβ1 : β < 1)
    (hC : 0 ≤ C) (hr : ∀ y, |r y| ≤ C) (c : ℝ)
    {τ : (ℕ → S) → ℕ∞} (hτ : IsTrajStoppingTime τ) :
    (∫ ω, discountedStoppedSum β (fun y => r y - c) τ ω ∂markovChainMeasure P x) =
      (∫ ω, discountedStoppedSum β r τ ω ∂markovChainMeasure P x) -
      c * ∫ ω, discountedStoppedSum β (fun _ : S => (1 : ℝ)) τ ω ∂markovChainMeasure P x := by
  simp_rw [stopped_sub_const hC hr hβ hβ1 c τ]
  rw [integral_sub (stopped_integrable hC hr hrm hβ hβ1 hτ _)
    ((stopped_integrable (f := fun _ : S => (1 : ℝ)) (M := 1) (by norm_num) (fun _ => by norm_num)
      measurable_const hβ hβ1 hτ _).const_mul c), integral_const_mul]

theorem stopping_ratio_bounds (P : Kernel S S) [IsMarkovKernel P] (x : S)
    {r : S → ℝ} (hrm : Measurable r) {β C : ℝ} (hβ : 0 ≤ β) (hβ1 : β < 1)
    (hC : 0 ≤ C) (hr : ∀ y, 0 ≤ r y ∧ r y ≤ C)
    {τ : (ℕ → S) → ℕ∞} (hτ : IsTrajStoppingTime τ) (hτ1 : ∀ ω, 1 ≤ τ ω) :
    0 ≤ (∫ ω, discountedStoppedSum β r τ ω ∂markovChainMeasure P x) /
      (∫ ω, discountedStoppedSum β (fun _ : S => (1 : ℝ)) τ ω ∂markovChainMeasure P x) ∧
    (∫ ω, discountedStoppedSum β r τ ω ∂markovChainMeasure P x) /
      (∫ ω, discountedStoppedSum β (fun _ : S => (1 : ℝ)) τ ω ∂markovChainMeasure P x) ≤ C := by
  have hd := stopped_duration_expectation_bounds hβ hβ1 hτ hτ1 (markovChainMeasure P x)
  have hp : 0 < ∫ ω, discountedStoppedSum β (fun _ : S => (1 : ℝ)) τ ω ∂markovChainMeasure P x := by linarith
  constructor
  · exact div_nonneg (integral_nonneg (stopped_nonneg (fun y => (hr y).1) hβ τ)) hp.le
  · apply (div_le_iff₀ hp).mpr
    have hi := integral_mono
      (stopped_integrable hC (fun y => by rw [abs_of_nonneg (hr y).1]; exact (hr y).2) hrm hβ hβ1 hτ (markovChainMeasure P x))
      ((stopped_integrable (f := fun _ : S => (1 : ℝ)) (M := 1) (by norm_num) (fun _ => by norm_num)
        measurable_const hβ hβ1 hτ (markovChainMeasure P x)).const_mul C)
      (stopped_reward_le_duration hC hr hβ hβ1 τ)
    rwa [integral_const_mul] at hi

theorem index_bounds (P : Kernel S S) [IsMarkovKernel P] (x : S)
    {r : S → ℝ} (hrm : Measurable r) {β C : ℝ} (hβ : 0 ≤ β) (hβ1 : β < 1)
    (hC : 0 ≤ C) (hr : ∀ y, 0 ≤ r y ∧ r y ≤ C) :
    0 ≤ gittinsIndex P r β x ∧ gittinsIndex P r β x ≤ C := by
  let A : Set ℝ := {g | ∃ τ : (ℕ → S) → ℕ∞, IsTrajStoppingTime τ ∧ (∀ ω, 1 ≤ τ ω) ∧
    g = (∫ ω, discountedStoppedSum β r τ ω ∂markovChainMeasure P x) /
      (∫ ω, discountedStoppedSum β (fun _ : S => (1 : ℝ)) τ ω ∂markovChainMeasure P x)}
  have hb : ∀ g ∈ A, 0 ≤ g ∧ g ≤ C := by
    rintro g ⟨τ, hτ, hτ1, rfl⟩
    exact stopping_ratio_bounds P x hrm hβ hβ1 hC hr hτ hτ1
  have hn : A.Nonempty := ⟨_, ⟨fun _ => 1, stopping_one, fun _ => le_rfl, rfl⟩⟩
  have hbd : BddAbove A := ⟨C, fun g hg => (hb g hg).2⟩
  change 0 ≤ sSup A ∧ sSup A ≤ C
  constructor
  · obtain ⟨g, hg⟩ := hn
    exact (hb g hg).1.trans (le_csSup hbd hg)
  · exact csSup_le hn (fun g hg => (hb g hg).2)
end GittinsProof
-- END GittinsProof.IndexBounds

-- BEGIN GittinsProof.FiniteBellman
open MeasureTheory ProbabilityTheory BanditAlgorithm
namespace GittinsProof
variable {S : Type*} [MeasurableSpace S]

theorem finite_bellman_nonneg (P : Kernel S S) (r : S → ℝ) (β c : ℝ) (N : ℕ) (x : S) :
    0 ≤ gittinsFiniteRetirementValue P r β c N x := by
  cases N with
  | zero => exact le_rfl
  | succ N => exact le_max_left _ _

theorem finite_bellman_bound (P : Kernel S S) [IsMarkovKernel P]
    (r : S → ℝ) {β c M : ℝ} (hβ : 0 ≤ β) (hβ1 : β < 1)
    (hM : 0 ≤ M) (hr : ∀ x, |r x - c| ≤ M) (N : ℕ) (x : S) :
    gittinsFiniteRetirementValue P r β c N x ≤ M / (1 - β) := by
  induction N generalizing x with
  | zero => simp only [gittinsFiniteRetirementValue]; positivity
  | succ N ih =>
    have hi : (∫ y, gittinsFiniteRetirementValue P r β c N y ∂P x) ≤ M / (1 - β) := by
      have hb : ∀ y, ‖gittinsFiniteRetirementValue P r β c N y‖ ≤ M / (1 - β) := by
        intro y
        rw [Real.norm_eq_abs, abs_of_nonneg (finite_bellman_nonneg P r β c N y)]
        exact ih y
      have hz := norm_integral_le_of_norm_le_const (μ := P x) (Filter.Eventually.of_forall hb)
      simp only [Real.norm_eq_abs] at hz
      simp at hz
      exact le_trans (le_abs_self _) hz
    apply max_le (by positivity)
    calc
      r x - c + β * (∫ y, gittinsFiniteRetirementValue P r β c N y ∂P x) ≤
          M + β * (M / (1 - β)) := add_le_add (le_trans (le_abs_self _) (hr x))
            (mul_le_mul_of_nonneg_left hi hβ)
      _ = M / (1 - β) := by field_simp [ne_of_gt (sub_pos.mpr hβ1)]; ring

theorem finite_bellman_joint_measurable (P : Kernel S S) [IsMarkovKernel P]
    {r : S → ℝ} (hr : Measurable r) (β : ℝ) (N : ℕ) :
    Measurable (fun z : ℝ × S => gittinsFiniteRetirementValue P r β z.1 N z.2) := by
  induction N with
  | zero => exact measurable_const
  | succ N ih =>
    have hm : StronglyMeasurable (fun z : (ℝ × S) × S =>
        gittinsFiniteRetirementValue P r β z.1.1 N z.2) :=
      (ih.comp ((measurable_fst.comp measurable_fst).prodMk measurable_snd)).stronglyMeasurable
    have hi : Measurable (fun z : ℝ × S =>
        ∫ y, gittinsFiniteRetirementValue P r β z.1 N y ∂P z.2) :=
      (hm.integral_kernel_prod_right' (κ := P.comap Prod.snd measurable_snd)).measurable
    exact measurable_const.max (((hr.comp measurable_snd).sub measurable_fst).add
      (measurable_const.mul hi))

theorem finite_bellman_measurable (P : Kernel S S) [IsMarkovKernel P]
    {r : S → ℝ} (hr : Measurable r) (β c : ℝ) (N : ℕ) :
    Measurable (gittinsFiniteRetirementValue P r β c N) :=
  (finite_bellman_joint_measurable P hr β N).comp (measurable_const.prodMk measurable_id)

theorem finite_bellman_integrable (P : Kernel S S) [IsMarkovKernel P]
    {r : S → ℝ} (hrm : Measurable r) {β c M : ℝ} (hβ : 0 ≤ β) (hβ1 : β < 1)
    (hM : 0 ≤ M) (hr : ∀ x, |r x - c| ≤ M) (N : ℕ)
    (μ : Measure S) [IsFiniteMeasure μ] :
    Integrable (gittinsFiniteRetirementValue P r β c N) μ := by
  refine (integrable_const (M / (1 - β))).mono'
    (finite_bellman_measurable P hrm β c N).aestronglyMeasurable ?_
  filter_upwards [] with x
  rw [Real.norm_eq_abs, abs_of_nonneg (finite_bellman_nonneg P r β c N x)]
  exact finite_bellman_bound P r hβ hβ1 hM hr N x
end GittinsProof
-- END GittinsProof.FiniteBellman

-- BEGIN GittinsProof.FiniteStop
open MeasureTheory ProbabilityTheory BanditAlgorithm
namespace GittinsProof
variable {S : Type*} [MeasurableSpace S]

noncomputable def finiteStop (P : Kernel S S) (r : S → ℝ) (β c : ℝ) (N : ℕ)
    (ω : ℕ → S) : ℕ := by
  classical
  exact Nat.find (show ∃ t, gittinsFiniteRetirementValue P r β c (N - t) (ω t) = 0 from
    ⟨N, by simp [gittinsFiniteRetirementValue]⟩)

theorem finiteStop_zero (P : Kernel S S) (r : S → ℝ) (β c : ℝ) (N : ℕ) (ω : ℕ → S) :
    gittinsFiniteRetirementValue P r β c (N - finiteStop P r β c N ω)
      (ω (finiteStop P r β c N ω)) = 0 := by
  classical
  unfold finiteStop
  exact Nat.find_spec (p := fun t => gittinsFiniteRetirementValue P r β c (N - t) (ω t) = 0) _

theorem finiteStop_le_iff (P : Kernel S S) (r : S → ℝ) (β c : ℝ) (N n : ℕ) (ω : ℕ → S) :
    finiteStop P r β c N ω ≤ n ↔ ∃ t ≤ n, gittinsFiniteRetirementValue P r β c (N - t) (ω t) = 0 := by
  classical
  unfold finiteStop
  exact Nat.find_le_iff (p := fun t => gittinsFiniteRetirementValue P r β c (N - t) (ω t) = 0) _ _

theorem finiteStop_le (P : Kernel S S) (r : S → ℝ) (β c : ℝ) (N : ℕ) (ω : ℕ → S) :
    finiteStop P r β c N ω ≤ N :=
  (finiteStop_le_iff P r β c N N ω).mpr ⟨N, le_rfl, by simp [gittinsFiniteRetirementValue]⟩

theorem finiteStop_pos_value (P : Kernel S S) (r : S → ℝ) (β c : ℝ) (N t : ℕ) (ω : ℕ → S)
    (ht : t < finiteStop P r β c N ω) :
    0 < gittinsFiniteRetirementValue P r β c (N - t) (ω t) := by
  have hn : gittinsFiniteRetirementValue P r β c (N - t) (ω t) ≠ 0 := by
    intro hz
    have := (finiteStop_le_iff P r β c N t ω).mpr ⟨t, le_rfl, hz⟩
    omega
  exact lt_of_le_of_ne (finite_bellman_nonneg P r β c (N - t) (ω t)) (Ne.symm hn)

theorem finiteStop_stopping (P : Kernel S S) [IsMarkovKernel P]
    {r : S → ℝ} (hr : Measurable r) (β c : ℝ) (N : ℕ) :
    IsTrajStoppingTime (fun ω => (finiteStop P r β c N ω : ℕ∞)) := by
  classical
  intro n
  let E : Set ((i : Finset.Iic n) → S) := {w | ∃ t : Finset.Iic n,
    gittinsFiniteRetirementValue P r β c (N - t.1) (w t) = 0}
  have hE : MeasurableSet E := by
    change MeasurableSet {w : ((i : Finset.Iic n) → S) | ∃ t : Finset.Iic n, gittinsFiniteRetirementValue P r β c (N - t.1) (w t) = 0}
    simp only [Set.ofPred_exists]
    apply MeasurableSet.iUnion
    intro t
    exact measurableSet_eq_fun ((finite_bellman_measurable P hr β c (N - t.1)).comp
      (measurable_pi_apply t)) measurable_const
  apply MeasurableSpace.measurableSet_comap.mpr
  refine ⟨E, hE, ?_⟩
  ext ω
  simp only [Set.mem_preimage, E, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨t, ht⟩
    have hn := (finiteStop_le_iff P r β c N n ω).mpr ⟨t.1, Finset.mem_Iic.mp t.2, ht⟩
    exact_mod_cast hn
  · intro hn
    have hn' : finiteStop P r β c N ω ≤ n := by exact_mod_cast hn
    obtain ⟨t, ht, hz⟩ := (finiteStop_le_iff P r β c N n ω).mp hn'
    exact ⟨⟨t, by simpa using ht⟩, hz⟩
end GittinsProof
-- END GittinsProof.FiniteStop

-- BEGIN GittinsProof.ChainTower
open MeasureTheory ProbabilityTheory BanditAlgorithm
namespace GittinsProof
variable {S : Type*} [MeasurableSpace S]

theorem chain_step_integral (P : Kernel S S) [IsMarkovKernel P] (x : S) (n : ℕ)
    (F : ((i : Finset.Iic n) → S) × S → ℝ) (hF : Measurable F)
    (C : ℝ) (hbound : ∀ z, ‖F z‖ ≤ C) :
    (∫ ω, F (Preorder.frestrictLe n ω, ω (n + 1)) ∂markovChainMeasure P x) =
      ∫ ω, ∫ y, F (Preorder.frestrictLe n ω, y) ∂P (ω n) ∂markovChainMeasure P x := by
  let μ := markovChainMeasure P x
  have hm : Measurable (fun ω : ℕ → S => (Preorder.frestrictLe n ω, ω (n + 1))) := by fun_prop
  have hp : Measurable (Preorder.frestrictLe (π := fun _ : ℕ => S) n) := by fun_prop
  have hi : Integrable F ((μ.map (Preorder.frestrictLe n)).compProd (markovChainStep P n)) := by
    refine (integrable_const C).mono' hF.aestronglyMeasurable ?_
    exact Filter.Eventually.of_forall hbound
  rw [← integral_map hm.aemeasurable hF.aestronglyMeasurable,
    ← chain_prefix_next P x n, Measure.integral_compProd hi]
  have hmi : Measurable (fun z : (i : Finset.Iic n) → S =>
      ∫ y, F (z, y) ∂markovChainStep P n z) :=
    (hF.stronglyMeasurable.integral_kernel_prod_right').measurable
  rw [integral_map hp.aemeasurable hmi.aestronglyMeasurable]
  rfl
end GittinsProof
-- END GittinsProof.ChainTower

-- BEGIN GittinsProof.StoppedTower
open MeasureTheory ProbabilityTheory BanditAlgorithm
namespace GittinsProof
variable {S : Type*} [MeasurableSpace S]

theorem survival_prefix {τ : (ℕ → S) → ℕ∞} (hτ : IsTrajStoppingTime τ) (n : ℕ) :
    ∃ E : Set ((i : Finset.Iic n) → S), MeasurableSet E ∧
      ∀ ω, ((n : ℕ∞) < τ ω ↔ Preorder.frestrictLe n ω ∈ E) := by
  obtain ⟨E, hE, heq⟩ := MeasurableSpace.measurableSet_comap.mp (hτ n)
  refine ⟨Eᶜ, hE.compl, ?_⟩
  intro ω
  have h : (Preorder.frestrictLe n ω ∈ E) ↔ τ ω ≤ (n : ℕ∞) := by
    exact Set.ext_iff.mp heq ω
  simpa only [Set.mem_compl_iff, not_le] using not_congr h.symm

theorem stopped_step_integral (P : Kernel S S) [IsMarkovKernel P] (x : S) (n : ℕ)
    {τ : (ℕ → S) → ℕ∞} (hτ : IsTrajStoppingTime τ)
    {f : S → ℝ} (hf : Measurable f) {M : ℝ} (hM : 0 ≤ M) (hb : ∀ y, ‖f y‖ ≤ M) :
    (∫ ω, if (n : ℕ∞) < τ ω then f (ω (n + 1)) else 0 ∂markovChainMeasure P x) =
      ∫ ω, if (n : ℕ∞) < τ ω then ∫ y, f y ∂P (ω n) else 0 ∂markovChainMeasure P x := by
  classical
  obtain ⟨E, hE, heq⟩ := survival_prefix hτ n
  let F := fun z : ((i : Finset.Iic n) → S) × S => if z.1 ∈ E then f z.2 else 0
  have hFm : Measurable F := Measurable.ite (measurable_fst hE)
    (hf.comp measurable_snd) measurable_const
  have hFb : ∀ z, ‖F z‖ ≤ M := by
    intro z
    dsimp [F]
    split_ifs
    · exact hb _
    · simpa using hM
  have h := chain_step_integral P x n F hFm M hFb
  calc
    (∫ ω, if (n : ℕ∞) < τ ω then f (ω (n + 1)) else 0 ∂markovChainMeasure P x) =
        ∫ ω, F (Preorder.frestrictLe n ω, ω (n + 1)) ∂markovChainMeasure P x := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun ω => by simp only [F, heq ω]
    _ = _ := h
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [] with ω
      dsimp [F]
      simp only [heq ω]
      by_cases hm : Preorder.frestrictLe n ω ∈ E <;> simp [hm]
end GittinsProof
-- END GittinsProof.StoppedTower

-- BEGIN GittinsProof.AliveStep
open MeasureTheory ProbabilityTheory BanditAlgorithm
namespace GittinsProof
variable {S : Type*} [MeasurableSpace S]

theorem alive_integrable (μ : Measure (ℕ → S)) [IsFiniteMeasure μ]
    {τ : (ℕ → S) → ℕ∞} (hτ : IsTrajStoppingTime τ) (n t : ℕ)
    {f : S → ℝ} (hf : Measurable f) {C : ℝ} (hC : 0 ≤ C) (hb : ∀ y, ‖f y‖ ≤ C) :
    Integrable (fun ω => if (n : ℕ∞) < τ ω then f (ω t) else 0) μ := by
  have hm : Measurable (fun ω => if (n : ℕ∞) < τ ω then f (ω t) else 0) := Measurable.ite (stopping_event_measurable hτ n)
    (hf.comp (measurable_pi_apply t)) measurable_const
  refine (integrable_const C).mono' hm.aestronglyMeasurable ?_
  filter_upwards [] with ω
  split_ifs
  · exact hb _
  · simpa using hC

theorem alive_step_le (P : Kernel S S) [IsMarkovKernel P] (x : S)
    {τ : (ℕ → S) → ℕ∞} (hτ : IsTrajStoppingTime τ) (n : ℕ)
    {f V W : S → ℝ} (hf : Measurable f) (hV : Measurable V) (hW : Measurable W)
    {C M β : ℝ} (hC : 0 ≤ C) (hM : 0 ≤ M) (hβ : 0 ≤ β)
    (hfb : ∀ y, ‖f y‖ ≤ C) (hVb : ∀ y, ‖V y‖ ≤ M) (hWb : ∀ y, ‖W y‖ ≤ M)
    (hW0 : ∀ y, 0 ≤ W y) (hstep : ∀ y, f y + β * ∫ z, W z ∂P y ≤ V y) :
    (∫ ω, if (n : ℕ∞) < τ ω then f (ω n) else 0 ∂markovChainMeasure P x) +
      β * (∫ ω, if ((n + 1 : ℕ) : ℕ∞) < τ ω then W (ω (n + 1)) else 0
        ∂markovChainMeasure P x) ≤
    ∫ ω, if (n : ℕ∞) < τ ω then V (ω n) else 0 ∂markovChainMeasure P x := by
  let μ := markovChainMeasure P x
  have hfi := alive_integrable μ hτ n n hf hC hfb
  have hvi := alive_integrable μ hτ n n hV hM hVb
  have hwi := alive_integrable μ hτ (n + 1) (n + 1) hW hM hWb
  have hwpi := alive_integrable μ hτ n (n + 1) hW hM hWb
  have hpW : Measurable (fun y => ∫ z, W z ∂P y) := hW.stronglyMeasurable.integral_kernel.measurable
  have hpWb : ∀ y, ‖∫ z, W z ∂P y‖ ≤ M := by
    intro y
    simpa using norm_integral_le_of_norm_le_const (μ := P y) (Filter.Eventually.of_forall hWb)
  have hpwi := alive_integrable μ hτ n n hpW hM hpWb
  have hmono : (∫ ω, if ((n + 1 : ℕ) : ℕ∞) < τ ω then W (ω (n + 1)) else 0 ∂μ) ≤
      ∫ ω, if (n : ℕ∞) < τ ω then W (ω (n + 1)) else 0 ∂μ := by
    apply integral_mono hwi hwpi
    intro ω
    by_cases ha : ((n + 1 : ℕ) : ℕ∞) < τ ω
    · have hb : (n : ℕ∞) < τ ω := lt_of_le_of_lt (by exact_mod_cast Nat.le_succ n) ha
      simp only [ha, hb, ↓reduceIte]
      exact le_rfl
    · simp only [ha, ↓reduceIte]
      split_ifs
      · exact hW0 _
      · exact le_rfl
  rw [stopped_step_integral P x n hτ hW hM hWb] at hmono
  have hi := integral_mono (hfi.add (hpwi.const_mul β)) hvi (fun ω => by
    by_cases ha : (n : ℕ∞) < τ ω
    · simpa only [Pi.add_apply, ha, ↓reduceIte] using hstep (ω n)
    · simp [ha])
  simp only [Pi.add_apply] at hi
  rw [integral_add hfi (hpwi.const_mul β), integral_const_mul] at hi
  have hm := mul_le_mul_of_nonneg_left hmono hβ
  dsimp [μ] at hi hm
  linarith
end GittinsProof
-- END GittinsProof.AliveStep

-- BEGIN GittinsProof.AliveEquality
open MeasureTheory ProbabilityTheory BanditAlgorithm
namespace GittinsProof
variable {S : Type*} [MeasurableSpace S]

theorem alive_step_eq (P : Kernel S S) [IsMarkovKernel P] (x : S)
    {τ : (ℕ → S) → ℕ∞} (hτ : IsTrajStoppingTime τ) (n : ℕ)
    {f V W : S → ℝ} (hf : Measurable f) (hW : Measurable W)
    {C M β : ℝ} (hC : 0 ≤ C) (hM : 0 ≤ M)
    (hfb : ∀ y, ‖f y‖ ≤ C) (hWb : ∀ y, ‖W y‖ ≤ M)
    (hpath : ∀ ω, (if ((n + 1 : ℕ) : ℕ∞) < τ ω then W (ω (n + 1)) else 0) =
      if (n : ℕ∞) < τ ω then W (ω (n + 1)) else 0)
    (hstep : ∀ ω, (n : ℕ∞) < τ ω → f (ω n) + β * ∫ z, W z ∂P (ω n) = V (ω n)) :
    (∫ ω, if (n : ℕ∞) < τ ω then f (ω n) else 0 ∂markovChainMeasure P x) +
      β * (∫ ω, if ((n + 1 : ℕ) : ℕ∞) < τ ω then W (ω (n + 1)) else 0
        ∂markovChainMeasure P x) =
    ∫ ω, if (n : ℕ∞) < τ ω then V (ω n) else 0 ∂markovChainMeasure P x := by
  have he : (∫ ω, if ((n + 1 : ℕ) : ℕ∞) < τ ω then W (ω (n + 1)) else 0 ∂markovChainMeasure P x) =
      ∫ ω, if (n : ℕ∞) < τ ω then ∫ z, W z ∂P (ω n) else 0 ∂markovChainMeasure P x := by
    rw [show (fun ω => if ((n + 1 : ℕ) : ℕ∞) < τ ω then W (ω (n + 1)) else 0) =
      (fun ω => if (n : ℕ∞) < τ ω then W (ω (n + 1)) else 0) from funext hpath]
    exact stopped_step_integral P x n hτ hW hM hWb
  rw [he]
  have hfi := alive_integrable (markovChainMeasure P x) hτ n n hf hC hfb
  have hpW : Measurable (fun y => ∫ z, W z ∂P y) := hW.stronglyMeasurable.integral_kernel.measurable
  have hpWb : ∀ y, ‖∫ z, W z ∂P y‖ ≤ M := by
    intro y
    simpa using norm_integral_le_of_norm_le_const (μ := P y) (Filter.Eventually.of_forall hWb)
  have hpi := alive_integrable (markovChainMeasure P x) hτ n n hpW hM hpWb
  rw [← integral_const_mul, ← integral_add hfi (hpi.const_mul β)]
  apply integral_congr_ae
  filter_upwards [] with ω
  by_cases ha : (n : ℕ∞) < τ ω
  · simpa only [ha, ↓reduceIte] using hstep ω ha
  · simp [ha]
end GittinsProof
-- END GittinsProof.AliveEquality

-- BEGIN GittinsProof.FiniteStoppedIntegral
open MeasureTheory ProbabilityTheory BanditAlgorithm
namespace GittinsProof
variable {S : Type*} [MeasurableSpace S]

omit [MeasurableSpace S] in
theorem stopped_eq_finite {τ : (ℕ → S) → ℕ∞} (N : ℕ) (hτ : ∀ ω, τ ω ≤ (N : ℕ∞))
    (β : ℝ) (f : S → ℝ) (ω : ℕ → S) :
    discountedStoppedSum β f τ ω =
      ∑ t ∈ Finset.range N, β ^ t * (if (t : ℕ∞) < τ ω then f (ω t) else 0) := by
  unfold discountedStoppedSum
  rw [tsum_eq_sum (s := Finset.range N) (fun t ht => by
    have hn : N ≤ t := by simpa only [Finset.mem_range, not_lt] using ht
    have hnt : (N : ℕ∞) ≤ t := by exact_mod_cast hn
    simp [not_lt.mpr ((hτ ω).trans hnt)])]
  apply Finset.sum_congr rfl
  intro t ht
  split_ifs <;> simp

theorem stopped_integral_finite (μ : Measure (ℕ → S)) [IsFiniteMeasure μ]
    {τ : (ℕ → S) → ℕ∞} (hτ : IsTrajStoppingTime τ) (N : ℕ) (hN : ∀ ω, τ ω ≤ (N : ℕ∞))
    (β : ℝ) {f : S → ℝ} (hf : Measurable f) {M : ℝ} (hM : 0 ≤ M) (hb : ∀ y, ‖f y‖ ≤ M) :
    (∫ ω, discountedStoppedSum β f τ ω ∂μ) =
      ∑ t ∈ Finset.range N, β ^ t * ∫ ω, if (t : ℕ∞) < τ ω then f (ω t) else 0 ∂μ := by
  simp_rw [stopped_eq_finite N hN β f]
  rw [integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro t ht
    exact integral_const_mul _ _
  · intro t ht
    exact (alive_integrable μ hτ t t hf hM hb).const_mul _
end GittinsProof
-- END GittinsProof.FiniteStoppedIntegral

-- BEGIN GittinsProof.ChainInitial
open MeasureTheory ProbabilityTheory BanditAlgorithm
namespace GittinsProof
variable {S : Type*} [MeasurableSpace S]

theorem chain_initial_map (P : Kernel S S) [IsMarkovKernel P] (x : S) :
    (markovChainMeasure P x).map (fun ω => ω 0) = Measure.dirac x := by
  have hp := chain_prefix P x 0
  rw [Kernel.partialTraj_self, Kernel.id_apply] at hp
  have hm : Measurable (fun w : (i : Finset.Iic 0) → S => w ⟨0, by simp⟩) :=
    measurable_pi_apply _
  have h := congrArg (fun μ => μ.map (fun w : (i : Finset.Iic 0) → S => w ⟨0, by simp⟩)) hp
  rw [Measure.map_map hm (by fun_prop), Measure.map_dirac' hm] at h
  exact h

theorem integral_chain_initial (P : Kernel S S) [IsMarkovKernel P] (x : S)
    {f : S → ℝ} (hf : Measurable f) :
    (∫ ω, f (ω 0) ∂markovChainMeasure P x) = f x := by
  rw [← integral_map (measurable_pi_apply 0).aemeasurable hf.aestronglyMeasurable,
    chain_initial_map, integral_dirac' f x hf.stronglyMeasurable]
end GittinsProof
-- END GittinsProof.ChainInitial

-- BEGIN GittinsProof.SnellUpper
open MeasureTheory ProbabilityTheory BanditAlgorithm
namespace GittinsProof

theorem discounted_telescope_le {β : ℝ} (hβ : 0 ≤ β) (a v : ℕ → ℝ) (N : ℕ)
    (hs : ∀ t < N, a t + β * v (t + 1) ≤ v t) :
    (∑ t ∈ Finset.range N, β ^ t * a t) + β ^ N * v N ≤ v 0 := by
  induction N with
  | zero => simp
  | succ N ih =>
    have hi := ih (fun t ht => hs t (by omega))
    have hn := mul_le_mul_of_nonneg_left (hs N (by omega)) (pow_nonneg hβ N)
    rw [Finset.sum_range_succ, pow_succ]
    nlinarith

variable {S : Type*} [MeasurableSpace S]
theorem finite_stopped_upper (P : Kernel S S) [IsMarkovKernel P] (x : S)
    {r : S → ℝ} (hrm : Measurable r) {β c M : ℝ}
    (hβ : 0 ≤ β) (hβ1 : β < 1) (hM : 0 ≤ M) (hr : ∀ y, |r y - c| ≤ M)
    {τ : (ℕ → S) → ℕ∞} (hτ : IsTrajStoppingTime τ) (N : ℕ) :
    (∑ t ∈ Finset.range N, β ^ t *
      ∫ ω, if (t : ℕ∞) < τ ω then r (ω t) - c else 0 ∂markovChainMeasure P x) ≤
      gittinsFiniteRetirementValue P r β c N x := by
  let μ := markovChainMeasure P x
  let a := fun (t : ℕ) => ∫ ω, if (t : ℕ∞) < τ ω then r (ω t) - c else 0 ∂μ
  let v := fun (t : ℕ) => ∫ ω, if (t : ℕ∞) < τ ω then
    gittinsFiniteRetirementValue P r β c (N - t) (ω t) else 0 ∂μ
  have hbound (n : ℕ) (y : S) : ‖gittinsFiniteRetirementValue P r β c n y‖ ≤ M / (1 - β) := by
    rw [Real.norm_eq_abs, abs_of_nonneg (finite_bellman_nonneg P r β c n y)]
    exact finite_bellman_bound P r hβ hβ1 hM hr n y
  have hs : ∀ t < N, a t + β * v (t + 1) ≤ v t := by
    intro t ht
    have hn : N - t = (N - (t + 1)) + 1 := by omega
    apply alive_step_le P x hτ t (f := fun y => r y - c) (hrm.sub measurable_const)
      (finite_bellman_measurable P hrm β c (N - t))
      (finite_bellman_measurable P hrm β c (N - (t + 1))) hM (by positivity) hβ
      (fun y => by simpa only [Real.norm_eq_abs, Pi.sub_apply] using hr y) (hbound _) (hbound _)
      (finite_bellman_nonneg P r β c _)
    intro y
    rw [hn, gittinsFiniteRetirementValue]
    exact le_max_right _ _
  have hvN : v N = 0 := by simp [v, gittinsFiniteRetirementValue]
  have hh := discounted_telescope_le hβ a v N hs
  rw [hvN, mul_zero, add_zero] at hh
  have hvi := alive_integrable μ hτ 0 0 (finite_bellman_measurable P hrm β c N)
    (show 0 ≤ M / (1 - β) by positivity) (hbound N)
  have hi : v 0 ≤ ∫ ω, gittinsFiniteRetirementValue P r β c N (ω 0) ∂μ := by
    apply integral_mono (by simpa [v] using hvi)
      (by
        refine (integrable_const (M / (1 - β))).mono'
          ((finite_bellman_measurable P hrm β c N).comp (measurable_pi_apply 0)).aestronglyMeasurable ?_
        exact Filter.Eventually.of_forall (fun ω => hbound N (ω 0)))
    intro ω
    simp only [Nat.sub_zero]
    split_ifs
    · exact le_rfl
    · exact finite_bellman_nonneg P r β c N _
  have he := integral_chain_initial P x (finite_bellman_measurable P hrm β c N)
  exact hh.trans (hi.trans_eq he)
end GittinsProof
-- END GittinsProof.SnellUpper

-- BEGIN GittinsProof.OptimalFinite
open MeasureTheory ProbabilityTheory BanditAlgorithm
namespace GittinsProof

theorem discounted_telescope_eq (β : ℝ) (a v : ℕ → ℝ) (N : ℕ)
    (hs : ∀ t < N, a t + β * v (t + 1) = v t) :
    (∑ t ∈ Finset.range N, β ^ t * a t) + β ^ N * v N = v 0 := by
  induction N with
  | zero => simp
  | succ N ih =>
    have hi := ih (fun t ht => hs t (by omega))
    have hn := congrArg (fun z => β ^ N * z) (hs N (by omega))
    rw [Finset.sum_range_succ, pow_succ]
    nlinarith

variable {S : Type*} [MeasurableSpace S]
theorem finite_optimal_value (P : Kernel S S) [IsMarkovKernel P] (x : S)
    {r : S → ℝ} (hrm : Measurable r) {β c M : ℝ}
    (hβ : 0 ≤ β) (hβ1 : β < 1) (hM : 0 ≤ M) (hr : ∀ y, |r y - c| ≤ M) (N : ℕ) :
    (∫ ω, discountedStoppedSum β (fun y => r y - c)
      (fun ω => (finiteStop P r β c N ω : ℕ∞)) ω ∂markovChainMeasure P x) =
      gittinsFiniteRetirementValue P r β c N x := by
  let τ := fun ω => (finiteStop P r β c N ω : ℕ∞)
  have hτ : IsTrajStoppingTime τ := finiteStop_stopping P hrm β c N
  let μ := markovChainMeasure P x
  let a := fun (t : ℕ) => ∫ ω, if (t : ℕ∞) < τ ω then r (ω t) - c else 0 ∂μ
  let v := fun (t : ℕ) => ∫ ω, if (t : ℕ∞) < τ ω then
    gittinsFiniteRetirementValue P r β c (N - t) (ω t) else 0 ∂μ
  have hbound (n : ℕ) (y : S) : ‖gittinsFiniteRetirementValue P r β c n y‖ ≤ M / (1 - β) := by
    rw [Real.norm_eq_abs, abs_of_nonneg (finite_bellman_nonneg P r β c n y)]
    exact finite_bellman_bound P r hβ hβ1 hM hr n y
  have hs : ∀ t < N, a t + β * v (t + 1) = v t := by
    intro t ht
    apply alive_step_eq P x hτ t (f := fun y => r y - c) (hrm.sub measurable_const)
      (finite_bellman_measurable P hrm β c (N - (t + 1))) hM (by positivity)
      (fun y => by simpa only [Real.norm_eq_abs] using hr y) (hbound _)
    · intro ω
      by_cases ha : ((t + 1 : ℕ) : ℕ∞) < τ ω
      · have hb : (t : ℕ∞) < τ ω := lt_of_le_of_lt (by exact_mod_cast Nat.le_succ t) ha
        simp only [ha, hb, ↓reduceIte]
      · by_cases hb : (t : ℕ∞) < τ ω
        · have he : finiteStop P r β c N ω = t + 1 := by
            have ha' : ¬ t + 1 < finiteStop P r β c N ω := by
              dsimp [τ] at ha
              exact_mod_cast ha
            have hb' : t < finiteStop P r β c N ω := by
              dsimp [τ] at hb
              exact_mod_cast hb
            omega
          have hz := finiteStop_zero P r β c N ω
          rw [he] at hz
          simpa only [ha, hb, ↓reduceIte] using hz.symm
        · simp only [ha, hb, ↓reduceIte]
    · intro ω ha
      have ha' : t < finiteStop P r β c N ω := by
              dsimp [τ] at ha
              exact_mod_cast ha
      have hz := finiteStop_pos_value P r β c N t ω ha'
      have hn : N - t = N - (t + 1) + 1 := by omega
      rw [hn, gittinsFiniteRetirementValue] at hz ⊢
      have hp : 0 < r (ω t) - c + β * ∫ y, gittinsFiniteRetirementValue P r β c (N - (t + 1)) y ∂P (ω t) :=
        (lt_max_iff.mp hz).resolve_left (lt_irrefl _)
      exact (max_eq_right hp.le).symm
  have hvN : v N = 0 := by simp [v, gittinsFiniteRetirementValue]
  have hh := discounted_telescope_eq β a v N hs
  rw [hvN, mul_zero, add_zero] at hh
  have hv0 : v 0 = gittinsFiniteRetirementValue P r β c N x := by
    calc
      v 0 = ∫ ω, gittinsFiniteRetirementValue P r β c N (ω 0) ∂μ := by
        apply integral_congr_ae
        filter_upwards [] with ω
        dsimp [v]
        by_cases ha : (0 : ℕ∞) < τ ω
        · simp [ha]
        · have he : finiteStop P r β c N ω = 0 := by
            have ha' : ¬ 0 < finiteStop P r β c N ω := by
              dsimp [τ] at ha
              exact_mod_cast ha
            omega
          have hz := finiteStop_zero P r β c N ω
          simpa [ha, he] using hz.symm
      _ = _ := integral_chain_initial P x (finite_bellman_measurable P hrm β c N)
  rw [stopped_integral_finite μ hτ N (fun ω => by
    dsimp [τ]
    exact_mod_cast finiteStop_le P r β c N ω)
    β (f := fun y => r y - c) (hrm.sub measurable_const) hM (fun y => by simpa only [Real.norm_eq_abs] using hr y)]
  exact hh.trans hv0
end GittinsProof
-- END GittinsProof.OptimalFinite

-- BEGIN GittinsProof.FiniteRetirementLower
open MeasureTheory ProbabilityTheory BanditAlgorithm
namespace GittinsProof
variable {S : Type*} [MeasurableSpace S]

theorem stopping_force_one {τ : (ℕ → S) → ℕ∞} (hτ : IsTrajStoppingTime τ) :
    IsTrajStoppingTime (fun ω => max 1 (τ ω)) := by
  intro n
  simp only [max_le_iff]
  by_cases hn : (1 : ℕ∞) ≤ n
  · simpa only [hn, true_and] using hτ n
  · simp only [hn, false_and]
    exact @MeasurableSet.empty (ℕ → S) (trajectoryFiltration S n)

theorem finite_le_retirement (P : Kernel S S) [IsMarkovKernel P] (x : S)
    {r : S → ℝ} (hrm : Measurable r) {β c M : ℝ}
    (hβ : 0 ≤ β) (hβ1 : β < 1) (hM : 0 ≤ M) (hr : ∀ y, |r y - c| ≤ M) (N : ℕ) :
    gittinsFiniteRetirementValue P r β c N x ≤ gittinsRetirementValue P r β c x := by
  by_cases hz : gittinsFiniteRetirementValue P r β c N x = 0
  · rw [hz]
    exact retirement_nonneg P r hβ hβ1 hM hr x
  let τ := fun ω => (finiteStop P r β c N ω : ℕ∞)
  have hτ : IsTrajStoppingTime τ := finiteStop_stopping P hrm β c N
  have hi : ∀ᵐ ω ∂markovChainMeasure P x,
      gittinsFiniteRetirementValue P r β c N (ω 0) = gittinsFiniteRetirementValue P r β c N x := by
    apply ae_of_ae_map (μ := markovChainMeasure P x) (f := fun ω : ℕ → S => ω 0)
      (p := fun y => gittinsFiniteRetirementValue P r β c N y = gittinsFiniteRetirementValue P r β c N x)
      (measurable_pi_apply 0).aemeasurable
    rw [chain_initial_map]
    apply (ae_dirac_iff (measurableSet_eq_fun (finite_bellman_measurable P hrm β c N) measurable_const)).mpr
    rfl
  have he : (∫ ω, discountedStoppedSum β (fun y => r y - c) (fun ω => max 1 (τ ω)) ω ∂markovChainMeasure P x) =
      ∫ ω, discountedStoppedSum β (fun y => r y - c) τ ω ∂markovChainMeasure P x := by
    apply integral_congr_ae
    filter_upwards [hi] with ω hω
    have hpos : 0 < finiteStop P r β c N ω := by
      by_contra hn
      have hn0 : finiteStop P r β c N ω = 0 := by omega
      have hs := finiteStop_zero P r β c N ω
      simp only [hn0, Nat.sub_zero] at hs
      rw [hω] at hs
      exact hz hs
    have hge : (1 : ℕ∞) ≤ τ ω := by
      dsimp [τ]
      exact_mod_cast (Nat.succ_le_iff.mpr hpos)
    have hsum : ∀ t : ℕ, (if (t : ℕ∞) < max 1 (τ ω) then β ^ t * (r (ω t) - c) else 0) =
        if (t : ℕ∞) < τ ω then β ^ t * (r (ω t) - c) else 0 := by
      intro t
      rw [max_eq_right hge]
    exact tsum_congr hsum
  have hl := stopped_le_retirement P r hβ hβ1 hM hr x (stopping_force_one hτ)
    (fun ω => le_max_left 1 (τ ω))
  rw [he] at hl
  rw [finite_optimal_value P x hrm hβ hβ1 hM hr N] at hl
  exact hl
end GittinsProof
-- END GittinsProof.FiniteRetirementLower

-- BEGIN GittinsProof.RetirementApprox
open MeasureTheory ProbabilityTheory BanditAlgorithm
namespace GittinsProof
variable {S : Type*} [MeasurableSpace S]

theorem stopped_approx_upper (P : Kernel S S) [IsMarkovKernel P] (x : S)
    {r : S → ℝ} (hrm : Measurable r) {β c M : ℝ}
    (hβ : 0 ≤ β) (hβ1 : β < 1) (hM : 0 ≤ M) (hr : ∀ y, |r y - c| ≤ M)
    {τ : (ℕ → S) → ℕ∞} (hτ : IsTrajStoppingTime τ) (N : ℕ) :
    (∫ ω, discountedStoppedSum β (fun y => r y - c) τ ω ∂markovChainMeasure P x) ≤
      gittinsFiniteRetirementValue P r β c N x + M * β ^ N / (1 - β) := by
  let μ := markovChainMeasure P x
  let a := fun (t : ℕ) (ω : ℕ → S) => β ^ t * (if (t : ℕ∞) < τ ω then r (ω t) - c else 0)
  have hai (t : ℕ) : Integrable (a t) μ :=
    (alive_integrable μ hτ t t (f := fun y => r y - c) (hrm.sub measurable_const) hM
      (fun y => by simpa only [Real.norm_eq_abs] using hr y)).const_mul _
  have hsi : Integrable (fun ω => ∑ t ∈ Finset.range N, a t ω) μ :=
    integrable_finsetSum _ (fun t _ => hai t)
  have hfi := stopped_integrable hM hr (hrm.sub measurable_const) hβ hβ1 hτ μ
  have hp : ∀ ω, discountedStoppedSum β (fun y => r y - c) τ ω ≤
      (∑ t ∈ Finset.range N, a t ω) + M * β ^ N / (1 - β) := by
    intro ω
    have hb := (le_abs_self _).trans (stopped_tail_bound hM hr hβ hβ1 τ ω N)
    have he : (∑ t ∈ Finset.range N, if (t : ℕ∞) < τ ω then β ^ t * (r (ω t) - c) else 0) =
        ∑ t ∈ Finset.range N, a t ω := by
      apply Finset.sum_congr rfl
      intro t ht
      dsimp [a]
      split_ifs <;> simp
    rw [he] at hb
    linarith
  have hi := integral_mono hfi (hsi.add (integrable_const _)) hp
  simp only [Pi.add_apply] at hi
  rw [integral_add hsi (integrable_const _), integral_finsetSum _ (fun t _ => hai t)] at hi
  simp only [integral_const] at hi
  simp at hi
  have he : (∑ t ∈ Finset.range N, ∫ ω, a t ω ∂μ) =
      ∑ t ∈ Finset.range N, β ^ t * ∫ ω, if (t : ℕ∞) < τ ω then r (ω t) - c else 0 ∂μ := by
    apply Finset.sum_congr rfl
    intro t ht
    exact integral_const_mul _ _
  rw [he] at hi
  have hu := finite_stopped_upper P x hrm hβ hβ1 hM hr hτ N
  dsimp [μ] at hi
  linarith

theorem retirement_approx_upper (P : Kernel S S) [IsMarkovKernel P] (x : S)
    {r : S → ℝ} (hrm : Measurable r) {β c M : ℝ}
    (hβ : 0 ≤ β) (hβ1 : β < 1) (hM : 0 ≤ M) (hr : ∀ y, |r y - c| ≤ M) (N : ℕ) :
    gittinsRetirementValue P r β c x ≤ gittinsFiniteRetirementValue P r β c N x + M * β ^ N / (1 - β) := by
  apply csSup_le (Set.insert_nonempty _ _)
  intro v hv
  rcases hv with rfl | ⟨τ, hτ, _, rfl⟩
  · exact add_nonneg (finite_bellman_nonneg P r β c N x) (by positivity)
  · exact stopped_approx_upper P x hrm hβ hβ1 hM hr hτ N
end GittinsProof
-- END GittinsProof.RetirementApprox

-- BEGIN GittinsProof.BellmanRetirement
open MeasureTheory ProbabilityTheory BanditAlgorithm Filter Topology
namespace GittinsProof
variable {S : Type*} [MeasurableSpace S]

theorem finite_tendsto_retirement (P : Kernel S S) [IsMarkovKernel P] (x : S)
    {r : S → ℝ} (hrm : Measurable r) {β c M : ℝ}
    (hβ : 0 ≤ β) (hβ1 : β < 1) (hM : 0 ≤ M) (hr : ∀ y, |r y - c| ≤ M) :
    Tendsto (fun N => gittinsFiniteRetirementValue P r β c N x) atTop
      (𝓝 (gittinsRetirementValue P r β c x)) := by
  have he : Tendsto (fun N : ℕ => M * β ^ N / (1 - β)) atTop (𝓝 0) := by
    simpa using ((tendsto_pow_atTop_nhds_zero_of_lt_one hβ hβ1).const_mul M).div_const (1 - β)
  have hl := (tendsto_const_nhds (x := gittinsRetirementValue P r β c x)).sub he
  simp only [sub_zero] at hl
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le hl tendsto_const_nhds
  · intro N
    have h := retirement_approx_upper P x hrm hβ hβ1 hM hr N
    linarith
  · exact fun N => finite_le_retirement P x hrm hβ hβ1 hM hr N

theorem retirement_measurable (P : Kernel S S) [IsMarkovKernel P]
    {r : S → ℝ} (hrm : Measurable r) {β c M : ℝ}
    (hβ : 0 ≤ β) (hβ1 : β < 1) (hM : 0 ≤ M) (hr : ∀ y, |r y - c| ≤ M) :
    Measurable (gittinsRetirementValue P r β c) :=
  measurable_of_tendsto_metrizable (fun N => finite_bellman_measurable P hrm β c N)
    (tendsto_pi_nhds.mpr (fun x => finite_tendsto_retirement P x hrm hβ hβ1 hM hr))

theorem retirement_joint_measurable (P : Kernel S S) [IsMarkovKernel P]
    {r : S → ℝ} (hrm : Measurable r) {β C : ℝ}
    (hβ : 0 ≤ β) (hβ1 : β < 1) (hC : 0 ≤ C) (hr : ∀ y, |r y| ≤ C) :
    Measurable (fun z : ℝ × S => gittinsRetirementValue P r β z.1 z.2) := by
  apply measurable_of_tendsto_metrizable (fun N => finite_bellman_joint_measurable P hrm β N)
  apply tendsto_pi_nhds.mpr
  intro z
  apply finite_tendsto_retirement P z.2 hrm hβ hβ1 (M := C + |z.1|) (by positivity)
  intro y
  exact (abs_sub (r y) z.1).trans (add_le_add (hr y) le_rfl)

theorem retirement_bellman (P : Kernel S S) [IsMarkovKernel P] (x : S)
    {r : S → ℝ} (hrm : Measurable r) {β c M : ℝ}
    (hβ : 0 ≤ β) (hβ1 : β < 1) (hM : 0 ≤ M) (hr : ∀ y, |r y - c| ≤ M) :
    gittinsRetirementValue P r β c x =
      max 0 (r x - c + β * ∫ y, gittinsRetirementValue P r β c y ∂P x) := by
  have hi : Tendsto (fun N => ∫ y, gittinsFiniteRetirementValue P r β c N y ∂P x) atTop
      (𝓝 (∫ y, gittinsRetirementValue P r β c y ∂P x)) := by
    apply tendsto_integral_of_dominated_convergence (fun _ => M / (1 - β))
    · exact fun N => (finite_bellman_measurable P hrm β c N).aestronglyMeasurable
    · exact integrable_const _
    · intro N
      filter_upwards [] with y
      rw [Real.norm_eq_abs, abs_of_nonneg (finite_bellman_nonneg P r β c N y)]
      exact finite_bellman_bound P r hβ hβ1 hM hr N y
    · exact Filter.Eventually.of_forall (fun y => finite_tendsto_retirement P y hrm hβ hβ1 hM hr)
  have hright := (tendsto_const_nhds (x := (0 : ℝ))).max
    ((tendsto_const_nhds (x := r x - c)).add (hi.const_mul β))
  have hleft := (finite_tendsto_retirement P x hrm hβ hβ1 hM hr).comp (tendsto_add_atTop_nat 1)
  exact tendsto_nhds_unique hleft hright
end GittinsProof
-- END GittinsProof.BellmanRetirement

-- BEGIN GittinsProof.IndexPositive
open MeasureTheory ProbabilityTheory BanditAlgorithm
namespace GittinsProof
variable {S : Type*} [MeasurableSpace S]

theorem retirement_pos_iff (P : Kernel S S) [IsMarkovKernel P] (x : S)
    {r : S → ℝ} (hrm : Measurable r) {β C : ℝ} (hβ : 0 ≤ β) (hβ1 : β < 1)
    (hC : 0 ≤ C) (hr : ∀ y, 0 ≤ r y ∧ r y ≤ C) (c : ℝ) :
    0 < gittinsRetirementValue P r β c x ↔ c < gittinsIndex P r β x := by
  have hab : ∀ y, |r y| ≤ C := fun y => by rw [abs_of_nonneg (hr y).1]; exact (hr y).2
  have hc : ∀ y, |r y - c| ≤ C + |c| := fun y =>
    (abs_sub (r y) c).trans (add_le_add (hab y) le_rfl)
  let A : Set ℝ := {g | ∃ τ : (ℕ → S) → ℕ∞, IsTrajStoppingTime τ ∧ (∀ ω, 1 ≤ τ ω) ∧
    g = (∫ ω, discountedStoppedSum β r τ ω ∂markovChainMeasure P x) /
      (∫ ω, discountedStoppedSum β (fun _ : S => (1 : ℝ)) τ ω ∂markovChainMeasure P x)}
  have hAb : BddAbove A := ⟨C, by
    rintro g ⟨τ, hτ, hτ1, rfl⟩
    exact (stopping_ratio_bounds P x hrm hβ hβ1 hC hr hτ hτ1).2⟩
  have hAn : A.Nonempty := ⟨_, ⟨fun _ => 1, stopping_one, fun _ => le_rfl, rfl⟩⟩
  have hUb := retirement_set_bdd P r hβ hβ1 (show 0 ≤ C + |c| by positivity) hc x
  have he {τ : (ℕ → S) → ℕ∞} (hτ : IsTrajStoppingTime τ) (hτ1 : ∀ ω, 1 ≤ τ ω) :
      (0 < ∫ ω, discountedStoppedSum β (fun y => r y - c) τ ω ∂markovChainMeasure P x) ↔
      c < (∫ ω, discountedStoppedSum β r τ ω ∂markovChainMeasure P x) /
        (∫ ω, discountedStoppedSum β (fun _ : S => (1 : ℝ)) τ ω ∂markovChainMeasure P x) := by
    have hd := (stopped_duration_expectation_bounds hβ hβ1 hτ hτ1 (markovChainMeasure P x)).1
    have hp : 0 < ∫ ω, discountedStoppedSum β (fun _ : S => (1 : ℝ)) τ ω ∂markovChainMeasure P x := by linarith
    rw [stopped_net_integral P x hrm hβ hβ1 hC hab c hτ, lt_div_iff₀ hp]
    constructor <;> intro h <;> linarith
  change 0 < sSup _ ↔ c < sSup A
  rw [lt_csSup_iff hUb (Set.insert_nonempty _ _), lt_csSup_iff hAb hAn]
  constructor
  · rintro ⟨v, hv, hp⟩
    rcases hv with rfl | ⟨τ, hτ, hτ1, rfl⟩
    · exact (lt_irrefl _ hp).elim
    · exact ⟨_, ⟨τ, hτ, hτ1, rfl⟩, (he hτ hτ1).mp hp⟩
  · rintro ⟨v, ⟨τ, hτ, hτ1, rfl⟩, hp⟩
    exact ⟨_, Set.mem_insert_of_mem 0 ⟨τ, hτ, hτ1, rfl⟩, (he hτ hτ1).mpr hp⟩

theorem retirement_zero (P : Kernel S S) [IsMarkovKernel P] (x : S)
    {r : S → ℝ} (hrm : Measurable r) {β C : ℝ} (hβ : 0 ≤ β) (hβ1 : β < 1)
    (hC : 0 ≤ C) (hr : ∀ y, 0 ≤ r y ∧ r y ≤ C) (c : ℝ)
    (hc : gittinsIndex P r β x ≤ c) : gittinsRetirementValue P r β c x = 0 := by
  have hn := retirement_nonneg P r hβ hβ1 (show 0 ≤ C + |c| by positivity)
    (fun y => (abs_sub (r y) c).trans (add_le_add (by simpa only [abs_of_nonneg (hr y).1] using (hr y).2) le_rfl)) x
  have hp : ¬ 0 < gittinsRetirementValue P r β c x := by
    rw [retirement_pos_iff P x hrm hβ hβ1 hC hr c]
    exact not_lt.mpr hc
  exact le_antisymm (not_lt.mp hp) hn

theorem index_measurable (P : Kernel S S) [IsMarkovKernel P]
    {r : S → ℝ} (hrm : Measurable r) {β C : ℝ} (hβ : 0 ≤ β) (hβ1 : β < 1)
    (hC : 0 ≤ C) (hr : ∀ y, 0 ≤ r y ∧ r y ≤ C) :
    Measurable (gittinsIndex P r β) := by
  apply measurable_of_Ioi
  intro c
  have hm := retirement_measurable P hrm hβ hβ1 (show 0 ≤ C + |c| by positivity)
    (fun y => (abs_sub (r y) c).trans (add_le_add (by simpa only [abs_of_nonneg (hr y).1] using (hr y).2) le_rfl))
  have he : (gittinsIndex P r β) ⁻¹' Set.Ioi c = {x | 0 < gittinsRetirementValue P r β c x} := by
    ext x
    exact (retirement_pos_iff P x hrm hβ hβ1 hC hr c).symm
  rw [he]
  exact measurableSet_lt measurable_const hm
end GittinsProof
-- END GittinsProof.IndexPositive

-- BEGIN GittinsProof.RetirementLipschitz
open MeasureTheory ProbabilityTheory BanditAlgorithm
namespace GittinsProof
variable {S : Type*} [MeasurableSpace S]

theorem retirement_le_add (P : Kernel S S) [IsMarkovKernel P] (x : S)
    {r : S → ℝ} (hrm : Measurable r) {β C : ℝ} (hβ : 0 ≤ β) (hβ1 : β < 1)
    (hC : 0 ≤ C) (hr : ∀ y, |r y| ≤ C) (c d : ℝ) :
    gittinsRetirementValue P r β c x ≤ gittinsRetirementValue P r β d x + |c-d| / (1-β) := by
  have hd : ∀ y, |r y-d| ≤ C+|d| := fun y => (abs_sub _ _).trans (add_le_add (hr y) le_rfl)
  have hM : 0 ≤ C+|d| := by positivity
  apply csSup_le (Set.insert_nonempty _ _)
  intro v hv
  rcases hv with rfl | ⟨τ, hτ, hτ1, rfl⟩
  · exact add_nonneg (retirement_nonneg P r hβ hβ1 hM hd x) (by positivity)
  · have hl := stopped_le_retirement P r hβ hβ1 hM hd x hτ hτ1
    have hD := stopped_duration_expectation_bounds hβ hβ1 hτ hτ1 (markovChainMeasure P x)
    rw [stopped_net_integral P x hrm hβ hβ1 hC hr d hτ] at hl
    rw [stopped_net_integral P x hrm hβ hβ1 hC hr c hτ]
    have hc : d-c ≤ |c-d| := by rw [abs_sub_comm]; exact le_abs_self _
    have hD0 : 0 ≤ ∫ ω, discountedStoppedSum β (fun _ : S => (1 : ℝ)) τ ω ∂markovChainMeasure P x := by linarith [hD.1]
    have h1 := mul_le_mul_of_nonneg_right hc hD0
    have h2 := mul_le_mul_of_nonneg_left hD.2 (abs_nonneg (c-d))
    have he : |c-d| * (1/(1-β)) = |c-d|/(1-β) := by ring
    rw [he] at h2
    nlinarith

theorem retirement_abs_sub (P : Kernel S S) [IsMarkovKernel P] (x : S)
    {r : S → ℝ} (hrm : Measurable r) {β C : ℝ} (hβ : 0 ≤ β) (hβ1 : β < 1)
    (hC : 0 ≤ C) (hr : ∀ y, |r y| ≤ C) (c d : ℝ) :
    |gittinsRetirementValue P r β c x - gittinsRetirementValue P r β d x| ≤ |c-d|/(1-β) := by
  have h1 := retirement_le_add P x hrm hβ hβ1 hC hr c d
  have h2 := retirement_le_add P x hrm hβ hβ1 hC hr d c
  rw [abs_sub_comm d c] at h2
  exact abs_le.mpr ⟨by linarith, by linarith⟩
end GittinsProof
-- END GittinsProof.RetirementLipschitz

-- BEGIN GittinsProof.IndexBridge
open MeasureTheory ProbabilityTheory BanditAlgorithm
namespace GittinsProof
variable {S : Type*} [MeasurableSpace S]

theorem retirement_integrable (P : Kernel S S) [IsMarkovKernel P]
    {r : S → ℝ} (hrm : Measurable r) {β C : ℝ} (hβ : 0 ≤ β) (hβ1 : β < 1)
    (hC : 0 ≤ C) (hr : ∀ y, |r y| ≤ C) (c : ℝ) (μ : Measure S) [IsFiniteMeasure μ] :
    Integrable (gittinsRetirementValue P r β c) μ := by
  have hc : ∀ y, |r y-c| ≤ C+|c| := fun y => (abs_sub _ _).trans (add_le_add (hr y) le_rfl)
  have hM : 0 ≤ C+|c| := by positivity
  refine (integrable_const ((C+|c|)/(1-β))).mono'
    (retirement_measurable P hrm hβ hβ1 hM hc).aestronglyMeasurable ?_
  filter_upwards [] with y
  rw [Real.norm_eq_abs, abs_of_nonneg (retirement_nonneg P r hβ hβ1 hM hc y)]
  exact retirement_bound P r hβ hβ1 hM hc y

theorem retirement_continue_lt (P : Kernel S S) [IsMarkovKernel P] (x : S)
    {r : S → ℝ} (hrm : Measurable r) {β C : ℝ} (hβ : 0 ≤ β) (hβ1 : β < 1)
    (hC : 0 ≤ C) (hr : ∀ y, 0 ≤ r y ∧ r y ≤ C) (c : ℝ)
    (hc : c < gittinsIndex P r β x) :
    gittinsRetirementValue P r β c x = r x-c+β*∫ y, gittinsRetirementValue P r β c y ∂P x := by
  have hab : ∀ y, |r y| ≤ C := fun y => by rw [abs_of_nonneg (hr y).1]; exact (hr y).2
  have hb := retirement_bellman P x hrm hβ hβ1 (show 0 ≤ C+|c| by positivity)
    (fun y => (abs_sub _ _).trans (add_le_add (hab y) le_rfl))
  have hp := (retirement_pos_iff P x hrm hβ hβ1 hC hr c).mpr hc
  rw [hb] at hp
  have hpos := (lt_max_iff.mp hp).resolve_left (lt_irrefl _)
  exact hb.trans (max_eq_right hpos.le)

theorem retirement_continue (P : Kernel S S) [IsMarkovKernel P] (x : S)
    {r : S → ℝ} (hrm : Measurable r) {β C : ℝ} (hβ : 0 ≤ β) (hβ1 : β < 1)
    (hC : 0 ≤ C) (hr : ∀ y, 0 ≤ r y ∧ r y ≤ C) (c : ℝ)
    (hc : c ≤ gittinsIndex P r β x) :
    gittinsRetirementValue P r β c x = r x-c+β*∫ y, gittinsRetirementValue P r β c y ∂P x := by
  rcases hc.lt_or_eq with hc | hc
  · exact retirement_continue_lt P x hrm hβ hβ1 hC hr c hc
  have hab : ∀ y, |r y| ≤ C := fun y => by rw [abs_of_nonneg (hr y).1]; exact (hr y).2
  have hzero := retirement_zero P x hrm hβ hβ1 hC hr c hc.symm.le
  have hb := retirement_bellman P x hrm hβ hβ1 (show 0 ≤ C+|c| by positivity)
    (fun y => (abs_sub _ _).trans (add_le_add (hab y) le_rfl))
  let F := r x-c+β*∫ y, gittinsRetirementValue P r β c y ∂P x
  have hFle : F ≤ 0 := by rw [hzero] at hb; exact (le_max_right _ _).trans hb.symm.le
  suffices hFge : 0 ≤ F by exact hzero.trans (le_antisymm hFle hFge).symm
  by_contra hn
  have hF : F < 0 := lt_of_not_ge hn
  let ε := -F*(1-β)/2
  have hε : 0 < ε := by
    exact div_pos (mul_pos (neg_pos.mpr hF) (sub_pos.mpr hβ1)) (by norm_num)
  have hct : c-ε < gittinsIndex P r β x := by rw [← hc]; linarith
  have hcont := retirement_continue_lt P x hrm hβ hβ1 hC hr (c-ε) hct
  have hpos := (retirement_pos_iff P x hrm hβ hβ1 hC hr (c-ε)).mpr hct
  have hint : (∫ y, gittinsRetirementValue P r β (c-ε) y ∂P x) ≤
      (∫ y, gittinsRetirementValue P r β c y ∂P x) + ε/(1-β) := by
    have hi := integral_mono (retirement_integrable P hrm hβ hβ1 hC hab (c-ε) (P x))
      ((retirement_integrable P hrm hβ hβ1 hC hab c (P x)).add (integrable_const (ε/(1-β))))
      (fun y => by
        have hh := retirement_le_add P y hrm hβ hβ1 hC hab (c-ε) c
        simpa only [sub_sub_cancel_left, abs_neg, abs_of_pos hε, Pi.add_apply] using hh)
    simp only [Pi.add_apply] at hi
    rw [integral_add (retirement_integrable P hrm hβ hβ1 hC hab c (P x)) (integrable_const _)] at hi
    simpa using hi
  have hm := mul_le_mul_of_nonneg_left hint hβ
  have he : ε/(1-β) = -F/2 := by
    dsimp [ε]
    field_simp [ne_of_gt (sub_pos.mpr hβ1)]
  have he2 : ε + β*(ε/(1-β)) = ε/(1-β) := by
    field_simp [ne_of_gt (sub_pos.mpr hβ1)]
    ring
  change 0 < gittinsRetirementValue P r β (c-ε) x at hpos
  rw [hcont] at hpos
  dsimp [F] at he
  nlinarith
end GittinsProof
-- END GittinsProof.IndexBridge

-- BEGIN GittinsProof.FiniteReplay
open MeasureTheory ProbabilityTheory BanditAlgorithm
namespace GittinsProof
universe u
variable {k N : ℕ} {S : Type u} [MeasurableSpace S]

def playCount (a : Fin N → Fin k) (t : ℕ) (i : Fin k) : ℕ :=
  ((Finset.univ : Finset (Fin N)).filter (fun s => s.val < t ∧ a s = i)).card

def arrayState (a : Fin N → Fin k) (w : Fin k → Fin (N+1) → S)
    (t : ℕ) (i : Fin k) : S :=
  w i ⟨playCount a t i, by
    have h := Finset.card_filter_le (s := (Finset.univ : Finset (Fin N)))
      (p := fun s => s.val < t ∧ a s = i)
    have hc : playCount a t i ≤ N := by simpa [playCount] using h
    omega⟩

def replayHistory (a : Fin N → Fin k) (w : Fin k → Fin (N+1) → S)
    (t : ℕ) (ht : t ≤ N) : MarkovBanditHistory k S t :=
  ((fun s => (arrayState a w s.val, a ⟨s.val, lt_of_lt_of_le s.isLt ht⟩)),
    arrayState a w t)

noncomputable def arrayLaw (P : Kernel S S) [IsMarkovKernel P] (x : Fin k → S) :
    Measure (Fin k → Fin (N+1) → S) :=
  Measure.pi (fun i => (markovChainMeasure P (x i)).map (fun w j => w j.val))

noncomputable def wordWeight (pi : MarkovBanditPolicy k S)
    (a : Fin N → Fin k) (w : Fin k → Fin (N+1) → S) : ℝ :=
  ∏ t : Fin N, ((pi.select t.val) (replayHistory a w t.val (Nat.le_of_lt t.isLt)) {a t}).toReal


theorem playCount_eq_sum (a : Fin N → Fin k) (t : ℕ) (i : Fin k) :
    playCount a t i = ∑ s : Fin N, if s.val < t ∧ a s = i then 1 else 0 := by
  simp [playCount]

theorem playCount_zero (a : Fin N → Fin k) (i : Fin k) : playCount a 0 i = 0 := by
  simp [playCount]

theorem playCount_le (a : Fin N → Fin k) (t : ℕ) (i : Fin k) : playCount a t i ≤ N := by
  simpa [playCount] using Finset.card_filter_le
    (s := (Finset.univ : Finset (Fin N))) (p := fun s => s.val < t ∧ a s = i)

theorem playCount_congr (a b : Fin N → Fin k) (t : ℕ)
    (h : ∀ s : Fin N, s.val < t → a s = b s) (i : Fin k) :
    playCount a t i = playCount b t i := by
  unfold playCount
  congr 1
  ext s
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  constructor <;> intro hs
  · exact ⟨hs.1, (h s hs.1).symm.trans hs.2⟩
  · exact ⟨hs.1, (h s hs.1).trans hs.2⟩

theorem playCount_succ (a : Fin N → Fin k) (t : ℕ) (ht : t < N) (i : Fin k) :
    playCount a (t+1) i = playCount a t i + if a ⟨t,ht⟩ = i then 1 else 0 := by
  rw [playCount_eq_sum, playCount_eq_sum]
  have he : ∀ s : Fin N, (if s.val < t+1 ∧ a s = i then 1 else 0) =
      (if s.val < t ∧ a s = i then 1 else 0) +
      (if s = ⟨t,ht⟩ then (if a ⟨t,ht⟩ = i then 1 else 0) else 0) := by
    intro s
    by_cases hs : s = ⟨t,ht⟩
    · subst s; simp
    · have hn : s.val ≠ t := by intro h; apply hs; exact Fin.ext h
      by_cases ha : a s = i <;> simp [hs, ha, show s.val < t+1 ↔ s.val < t by omega]
  simp_rw [he]
  rw [Finset.sum_add_distrib]
  simp

omit [MeasurableSpace S] in
theorem arrayState_zero (a : Fin N → Fin k) (w : Fin k → Fin (N+1) → S) :
    arrayState a w 0 = fun i => w i 0 := by
  funext i
  simp [arrayState, playCount_zero]

theorem measurable_arrayState (a : Fin N → Fin k) (t : ℕ) :
    Measurable (fun w : Fin k → Fin (N+1) → S => arrayState a w t) := by
  apply measurable_pi_lambda
  intro i
  exact (measurable_pi_apply _).comp (measurable_pi_apply i)

theorem measurable_replayHistory (a : Fin N → Fin k) (t : ℕ) (ht : t ≤ N) :
    Measurable (fun w : Fin k → Fin (N+1) → S => replayHistory a w t ht) := by
  apply Measurable.prodMk
  · apply measurable_pi_lambda
    intro s
    exact (measurable_arrayState a s.val).prodMk measurable_const
  · exact measurable_arrayState a t

theorem measurable_wordWeight (pi : MarkovBanditPolicy k S) (a : Fin N → Fin k) :
    Measurable (wordWeight pi a) := by
  apply Finset.measurable_prod
  intro t _
  exact (((pi.select t.val).measurable_coe (measurableSet_singleton (a t))).comp
    (measurable_replayHistory a t.val (Nat.le_of_lt t.isLt))).ennreal_toReal

theorem wordWeight_nonneg (pi : MarkovBanditPolicy k S) (a : Fin N → Fin k)
    (w : Fin k → Fin (N+1) → S) : 0 ≤ wordWeight pi a w := by
  exact Finset.prod_nonneg fun _ _ => ENNReal.toReal_nonneg

end GittinsProof
-- END GittinsProof.FiniteReplay

-- BEGIN GittinsProof.ReplayPrefix
open MeasureTheory ProbabilityTheory BanditAlgorithm
namespace GittinsProof
universe u
variable {k N : ℕ} {S : Type u}

def truncateArray (w : Fin k → Fin (N+2) → S) : Fin k → Fin (N+1) → S :=
  fun i j => w i j.castSucc

theorem playCount_snoc (a : Fin N → Fin k) (b : Fin k) (t : ℕ) (ht : t ≤ N) (i : Fin k) :
    playCount (Fin.snoc a b) t i = playCount a t i := by
  rw [playCount_eq_sum, playCount_eq_sum, Fin.sum_univ_castSucc]
  simp [Fin.snoc_castSucc, show ¬N < t by omega]

theorem arrayState_snoc (a : Fin N → Fin k) (b : Fin k)
    (w : Fin k → Fin (N+2) → S) (t : ℕ) (ht : t ≤ N) :
    arrayState (Fin.snoc a b) w t = arrayState a (truncateArray w) t := by
  funext i
  unfold arrayState truncateArray
  congr 1
  apply Fin.ext
  exact playCount_snoc a b t ht i

theorem replayHistory_snoc (a : Fin N → Fin k) (b : Fin k)
    (w : Fin k → Fin (N+2) → S) (t : ℕ) (ht : t ≤ N) :
    replayHistory (Fin.snoc a b) w t (by omega) = replayHistory a (truncateArray w) t ht := by
  apply Prod.ext
  · funext s
    apply Prod.ext
    · exact arrayState_snoc a b w s.val (by omega)
    · change Fin.snoc (α := fun _ => Fin k) a b (⟨s.val, lt_of_lt_of_le s.isLt ht⟩ : Fin N).castSucc = _
      exact Fin.snoc_castSucc _ _ _
  · exact arrayState_snoc a b w t ht

variable [MeasurableSpace S]

theorem wordWeight_snoc (pi : MarkovBanditPolicy k S) (a : Fin N → Fin k) (b : Fin k)
    (w : Fin k → Fin (N+2) → S) :
    wordWeight pi (Fin.snoc a b) w = wordWeight pi a (truncateArray w) *
      ((pi.select N) (replayHistory a (truncateArray w) N le_rfl) {b}).toReal := by
  unfold wordWeight
  rw [Fin.prod_univ_castSucc]
  congr 1
  · apply Finset.prod_congr rfl
    intro t _
    simp only [Fin.val_castSucc, Fin.snoc_castSucc]
    rw [replayHistory_snoc a b w t.val (Nat.le_of_lt t.isLt)]
  · simp only [Fin.val_last, Fin.snoc_last]
    rw [replayHistory_snoc a b w N le_rfl]

theorem selection_mass (pi : MarkovBanditPolicy k S) (t : ℕ) (h : MarkovBanditHistory k S t) :
    (∑ b : Fin k, ((pi.select t) h {b}).toReal) = 1 := by
  have he : (∑ b : Fin k, (pi.select t) h {b}) = 1 := by
    rw [sum_measure_singleton]
    simp
  rw [← ENNReal.toReal_sum (fun b _ => measure_ne_top _ _), he]
  simp

theorem wordWeight_sum (pi : MarkovBanditPolicy k S) (w : Fin k → Fin (N+1) → S) :
    (∑ a : Fin N → Fin k, wordWeight pi a w) = 1 := by
  induction N with
  | zero => simp [wordWeight]
  | succ N ih =>
    have he := Equiv.sum_comp (Fin.snocEquiv (fun _ : Fin (N+1) => Fin k))
      (fun a => wordWeight pi a w)
    rw [← he, Fintype.sum_prod_type]
    change (∑ b : Fin k, ∑ a : Fin N → Fin k, wordWeight pi (Fin.snoc a b) w) = 1
    simp_rw [wordWeight_snoc]
    rw [Finset.sum_comm]
    simp_rw [← Finset.mul_sum, selection_mass, mul_one]
    exact ih (truncateArray w)

end GittinsProof
-- END GittinsProof.ReplayPrefix

-- BEGIN GittinsProof.HistoryBasics
open MeasureTheory ProbabilityTheory BanditAlgorithm WeberGittins.Suboptimality
namespace GittinsProof
universe u
variable {k n : ℕ} {S : Type u} [MeasurableSpace S]

def historySnoc (h : MarkovBanditHistory k S n) (z : Fin k × S) :
    MarkovBanditHistory k S (n+1) :=
  (Fin.snoc (α := fun _ => (Fin k → S) × Fin k) h.1 (h.2,z.1),
    Function.update h.2 z.1 z.2)

theorem measurable_historySnoc :
    Measurable (fun z : MarkovBanditHistory k S n × (Fin k × S) => historySnoc z.1 z.2) :=
  measurable_markovBanditSnoc

theorem measurable_truncateHistory :
    Measurable (truncateMarkovBanditHistory : MarkovBanditHistory k S (n+1) → MarkovBanditHistory k S n) := by
  apply Measurable.prodMk
  · apply measurable_pi_lambda
    intro i
    exact (measurable_pi_apply i.castSucc).comp measurable_fst
  · exact measurable_fst.comp ((measurable_pi_apply (Fin.last n)).comp measurable_fst)

omit [MeasurableSpace S] in
theorem truncate_historySnoc (h : MarkovBanditHistory k S n) (z : Fin k × S) :
    truncateMarkovBanditHistory (historySnoc h z) = h := by
  simp [truncateMarkovBanditHistory, historySnoc]

theorem bounded_integrable {A : Type*} [MeasurableSpace A] (mu : Measure A) [IsFiniteMeasure mu]
    (f : A → ℝ) (hf : Measurable f) (C : ℝ) (hb : ∀ a, |f a| ≤ C) : Integrable f mu := by
  exact Integrable.of_bound hf.aestronglyMeasurable C (ae_of_all _ fun a => by simpa using hb a)

theorem history_integral_succ (P : Kernel S S) [IsMarkovKernel P]
    (pi : MarkovBanditPolicy k S) (x : Fin k → S)
    (F : MarkovBanditHistory k S (n+1) → ℝ) (hF : Measurable F)
    (C : ℝ) (hC : ∀ h, |F h| ≤ C) :
    (∫ h, F h ∂markovBanditMeasure P pi x (n+1)) =
      ∫ h, ∫ z, F (historySnoc h z) ∂markovBanditStepKernel P pi n h
        ∂markovBanditMeasure P pi x n := by
  rw [markovBanditMeasure]
  change (∫ h, F h ∂Measure.map (fun z : MarkovBanditHistory k S n × (Fin k × S) => historySnoc z.1 z.2) _) = _
  rw [integral_map measurable_historySnoc.aemeasurable hF.aestronglyMeasurable]
  apply Measure.integral_compProd
  exact bounded_integrable _ _ (hF.comp measurable_historySnoc) C (fun z => hC _)

theorem history_forget_integral (P : Kernel S S) [IsMarkovKernel P]
    (pi : MarkovBanditPolicy k S) (x : Fin k → S)
    (F : MarkovBanditHistory k S n → ℝ) (hF : Measurable F)
    (C : ℝ) (hC : ∀ h, |F h| ≤ C) :
    (∫ h, F (truncateMarkovBanditHistory h) ∂markovBanditMeasure P pi x (n+1)) =
      ∫ h, F h ∂markovBanditMeasure P pi x n := by
  change (∫ h, (F ∘ truncateMarkovBanditHistory) h ∂markovBanditMeasure P pi x (n+1)) = _
  rw [history_integral_succ P pi x _ (hF.comp measurable_truncateHistory) C (fun h => hC _)]
  simp only [Function.comp_apply]
  simp [truncate_historySnoc]

theorem roundExpectation_ignore_action (P : Kernel S S) [IsMarkovKernel P]
    (pi : MarkovBanditPolicy k S) (x : Fin k → S)
    (F : MarkovBanditHistory k S n → ℝ) (hF : Measurable F)
    (C : ℝ) (hC : ∀ h, |F h| ≤ C) :
    roundExpectation P pi x n (fun h _ => F h) = ∫ h, F h ∂markovBanditMeasure P pi x n :=
  history_forget_integral P pi x F hF C hC

end GittinsProof
-- END GittinsProof.HistoryBasics

-- BEGIN GittinsProof.ReplaySteps
open MeasureTheory ProbabilityTheory BanditAlgorithm
namespace GittinsProof
universe u
variable {k N : ℕ} {S : Type u}

theorem arrayState_succ (a : Fin N → Fin k) (w : Fin k → Fin (N+1) → S)
    (t : ℕ) (ht : t < N) :
    arrayState a w (t+1) = Function.update (arrayState a w t) (a ⟨t,ht⟩)
      (arrayState a w (t+1) (a ⟨t,ht⟩)) := by
  funext i
  by_cases hi : i = a ⟨t,ht⟩
  · subst i; simp
  · rw [Function.update_of_ne hi]
    unfold arrayState
    congr 1
    apply Fin.ext
    change playCount a (t+1) i = playCount a t i
    rw [playCount_succ a t ht]
    simp [Ne.symm hi]

variable [MeasurableSpace S]

omit [MeasurableSpace S] in
theorem replayHistory_step (a : Fin N → Fin k) (w : Fin k → Fin (N+1) → S)
    (t : ℕ) (ht : t < N) :
    replayHistory a w (t+1) (by omega) =
      historySnoc (replayHistory a w t (by omega))
        (a ⟨t,ht⟩, arrayState a w (t+1) (a ⟨t,ht⟩)) := by
  apply Prod.ext
  · funext j
    refine Fin.lastCases ?_ (fun i => ?_) j
    · simp [replayHistory, historySnoc]
    · simp [replayHistory, historySnoc]
  · exact arrayState_succ a w t ht

theorem wordWeight_le_one (pi : MarkovBanditPolicy k S) (a : Fin N → Fin k)
    (w : Fin k → Fin (N+1) → S) : wordWeight pi a w ≤ 1 := by
  rw [← wordWeight_sum pi w]
  exact Finset.single_le_sum (fun b _ => wordWeight_nonneg pi b w) (Finset.mem_univ a)

instance arrayLaw_probability (P : Kernel S S) [IsMarkovKernel P] (x : Fin k → S) :
    IsProbabilityMeasure (arrayLaw (N := N) P x) := by
  unfold arrayLaw
  have : ∀ i : Fin k, IsProbabilityMeasure
      ((markovChainMeasure P (x i)).map (fun w (j : Fin (N+1)) => w j.val)) := by
    intro i
    exact Measure.isProbabilityMeasure_map
      ((measurable_pi_lambda _ (fun j => measurable_pi_apply j.val)).aemeasurable)
  infer_instance

end GittinsProof
-- END GittinsProof.ReplaySteps

-- BEGIN GittinsProof.PathReplay
open MeasureTheory ProbabilityTheory BanditAlgorithm
namespace GittinsProof
universe u
variable {k N : ℕ} {S : Type u}

def pathArray (N : ℕ) (w : Fin k → ℕ → S) : Fin k → Fin (N+1) → S := fun i j => w i j.val

def pathHistory (a : Fin N → Fin k) (w : Fin k → ℕ → S) (t : ℕ) (ht : t ≤ N) :
    MarkovBanditHistory k S t := replayHistory a (pathArray N w) t ht

theorem playCount_mono (a : Fin N → Fin k) {s t : ℕ} (hst : s ≤ t) (i : Fin k) :
    playCount a s i ≤ playCount a t i := by
  apply Finset.card_le_card
  intro j hj
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj ⊢
  exact ⟨lt_of_lt_of_le hj.1 hst, hj.2⟩

theorem pathHistory_congr (a : Fin N → Fin k) (t : ℕ) (ht : t ≤ N)
    (w v : Fin k → ℕ → S)
    (h : ∀ i s, s ≤ playCount a t i → w i s = v i s) :
    pathHistory a w t ht = pathHistory a v t ht := by
  apply Prod.ext
  · funext j
    apply Prod.ext
    · funext i
      exact h i _ (playCount_mono a (Nat.le_of_lt j.isLt) i)
    · rfl
  · funext i
    exact h i _ le_rfl

theorem pathHistory_snoc (a : Fin N → Fin k) (b : Fin k) (w : Fin k → ℕ → S)
    (t : ℕ) (ht : t ≤ N) :
    pathHistory (Fin.snoc a b) w t (by omega) = pathHistory a w t ht :=
  replayHistory_snoc a b (pathArray (N+1) w) t ht

variable [MeasurableSpace S]

noncomputable def pathWeight (pi : MarkovBanditPolicy k S) (a : Fin N → Fin k)
    (w : Fin k → ℕ → S) : ℝ := wordWeight pi a (pathArray N w)

theorem measurable_pathArray : Measurable (pathArray (k := k) (S := S) N) := by
  apply measurable_pi_lambda
  intro i
  apply measurable_pi_lambda
  intro j
  exact (measurable_pi_apply j.val).comp (measurable_pi_apply i)

theorem measurable_pathHistory (a : Fin N → Fin k) (t : ℕ) (ht : t ≤ N) :
    Measurable (fun w : Fin k → ℕ → S => pathHistory a w t ht) :=
  (measurable_replayHistory a t ht).comp measurable_pathArray

theorem measurable_pathWeight (pi : MarkovBanditPolicy k S) (a : Fin N → Fin k) :
    Measurable (pathWeight pi a) := (measurable_wordWeight pi a).comp measurable_pathArray

theorem pathWeight_bounds (pi : MarkovBanditPolicy k S) (a : Fin N → Fin k)
    (w : Fin k → ℕ → S) : 0 ≤ pathWeight pi a w ∧ pathWeight pi a w ≤ 1 :=
  ⟨wordWeight_nonneg _ _ _, wordWeight_le_one _ _ _⟩

theorem pathWeight_congr (pi : MarkovBanditPolicy k S) (a : Fin N → Fin k)
    (w v : Fin k → ℕ → S)
    (h : ∀ i s, s ≤ playCount a N i → w i s = v i s) :
    pathWeight pi a w = pathWeight pi a v := by
  unfold pathWeight wordWeight
  apply Finset.prod_congr rfl
  intro t _
  have he : pathHistory a w t.val (Nat.le_of_lt t.isLt) =
      pathHistory a v t.val (Nat.le_of_lt t.isLt) :=
    pathHistory_congr a t.val _ w v (fun i s hs => h i s (hs.trans (playCount_mono a (Nat.le_of_lt t.isLt) i)))
  change ((pi.select t.val) (pathHistory a w t.val _) {a t}).toReal = _
  rw [he]
  rfl

theorem pathWeight_snoc (pi : MarkovBanditPolicy k S) (a : Fin N → Fin k) (b : Fin k)
    (w : Fin k → ℕ → S) :
    pathWeight pi (Fin.snoc a b) w = pathWeight pi a w *
      ((pi.select N) (pathHistory a w N le_rfl) {b}).toReal :=
  wordWeight_snoc pi a b (pathArray (N+1) w)

omit [MeasurableSpace S] in
theorem pathHistory_terminal_snoc (a : Fin N → Fin k) (b : Fin k) (w : Fin k → ℕ → S) :
    pathHistory (Fin.snoc a b) w (N+1) le_rfl =
      historySnoc (pathHistory a w N le_rfl) (b, w b (playCount a N b + 1)) := by
  rw [pathHistory, replayHistory_step _ _ N (by omega)]
  change historySnoc (pathHistory (Fin.snoc a b) w N _) (_, _) = _
  rw [pathHistory_snoc a b w N le_rfl]
  change historySnoc (pathHistory a w N le_rfl)
    (Fin.snoc (α := fun _ => Fin k) a b (Fin.last N), arrayState (Fin.snoc a b) (pathArray (N+1) w) (N+1) (Fin.snoc (α := fun _ => Fin k) a b (Fin.last N))) = _
  simp only [Fin.snoc_last]
  congr 1
  apply Prod.ext
  · simp
  · change w b (playCount (Fin.snoc a b) (N+1) b) = _
    rw [playCount_succ _ N (by omega), playCount_snoc _ _ N le_rfl]
    change w b (playCount a N b + if Fin.snoc (α := fun _ => Fin k) a b (Fin.last N) = b then 1 else 0) = _
    simp

end GittinsProof
-- END GittinsProof.PathReplay

-- BEGIN GittinsProof.GreedyAlgebra
namespace GittinsProof
variable {I : Type*} [DecidableEq I]

def ChargeInvariant (c v : I → ℝ) : Prop :=
  ∀ i, c i < v i → ∀ j, j ≠ i → v j = c j ∧ c j ≤ c i

omit [DecidableEq I] in
theorem chargeInvariant_initial (v : I → ℝ) : ChargeInvariant v v := by
  intro i hi
  exact (lt_irrefl _ hi).elim

omit [DecidableEq I] in
theorem greedy_idle (c v : I → ℝ) (hcv : ∀ i, c i ≤ v i)
    (hinv : ChargeInvariant c v) (a : I) (ha : ∀ j, v j ≤ v a) :
    ∀ j, j ≠ a → v j = c j ∧ c j ≤ c a := by
  intro j hja
  have he : v j = c j := by
    by_contra hn
    have hj : c j < v j := lt_of_le_of_ne (hcv j) (Ne.symm hn)
    obtain ⟨he, hle⟩ := hinv j hj a (Ne.symm hja)
    have := ha j
    linarith
  refine ⟨he, ?_⟩
  by_cases hac : c a < v a
  · exact (hinv a hac j hja).2
  · have hae : c a = v a := le_antisymm (hcv a) (le_of_not_gt hac)
    rw [hae, ← he]
    exact ha j

theorem chargeInvariant_update (c v : I → ℝ) (hcv : ∀ i, c i ≤ v i)
    (hinv : ChargeInvariant c v) (a : I) (ha : ∀ j, v j ≤ v a) (y : ℝ) :
    ChargeInvariant (Function.update c a (min (c a) y)) (Function.update v a y) := by
  intro i hi j hji
  by_cases hiA : i = a
  · subst i
    have hy : c a < y := by simpa using hi
    have hc : min (c a) y = c a := min_eq_left hy.le
    simp only [Function.update_of_ne hji, Function.update_self, hc]
    exact greedy_idle c v hcv hinv a ha j hji
  · have he := (greedy_idle c v hcv hinv a ha i hiA).1
    simp only [Function.update_of_ne hiA] at hi
    exact (not_lt_of_ge (le_of_eq he) hi).elim

theorem charge_update_le (c v : I → ℝ) (hcv : ∀ i, c i ≤ v i) (a : I) (y : ℝ) :
    ∀ i, Function.update c a (min (c a) y) i ≤ Function.update v a y i := by
  intro i
  by_cases hi : i = a
  · subst i; simp
  · simpa [Function.update_of_ne hi] using hcv i

end GittinsProof
-- END GittinsProof.GreedyAlgebra

-- BEGIN GittinsProof.PrevailingBasics
open MeasureTheory ProbabilityTheory BanditAlgorithm
namespace GittinsProof
universe u
variable {k n : ℕ} {S : Type u} [MeasurableSpace S]

theorem prevailing_measurable (g : S → ℝ) (hg : Measurable g) (i : Fin k) (n : ℕ) :
    Measurable (fun h : MarkovBanditHistory k S n => currentHistoryPrevailingCharge g n h i) := by
  induction n with
  | zero => exact hg.comp ((measurable_pi_apply i).comp measurable_snd)
  | succ n ih =>
    exact (ih.comp measurable_truncateHistory).min
      (hg.comp ((measurable_pi_apply i).comp measurable_snd))

omit [MeasurableSpace S] in
theorem prevailing_le_current (g : S → ℝ) (h : MarkovBanditHistory k S n) (i : Fin k) :
    currentHistoryPrevailingCharge g n h i ≤ g (h.2 i) := by
  cases n with
  | zero => exact le_rfl
  | succ n => exact min_le_right _ _

omit [MeasurableSpace S] in
theorem prevailing_nonneg (g : S → ℝ) (hg : ∀ y, 0 ≤ g y)
    (h : MarkovBanditHistory k S n) (i : Fin k) :
    0 ≤ currentHistoryPrevailingCharge g n h i := by
  induction n with
  | zero => exact hg _
  | succ n ih => exact le_min (ih _) (hg _)

omit [MeasurableSpace S] in
theorem prevailing_le_bound (g : S → ℝ) (M : ℝ) (hg : ∀ y, g y ≤ M)
    (h : MarkovBanditHistory k S n) (i : Fin k) :
    currentHistoryPrevailingCharge g n h i ≤ M :=
  (prevailing_le_current g h i).trans (hg _)

omit [MeasurableSpace S] in
theorem prevailing_snoc (g : S → ℝ) (h : MarkovBanditHistory k S n) (a : Fin k) (y : S) :
    currentHistoryPrevailingCharge g (n+1) (historySnoc h (a,y)) =
      Function.update (currentHistoryPrevailingCharge g n h) a
        (min (currentHistoryPrevailingCharge g n h a) (g y)) := by
  funext i
  simp only [currentHistoryPrevailingCharge, truncate_historySnoc]
  by_cases hi : i = a
  · subst i; simp [historySnoc]
  · simp only [historySnoc, Function.update_of_ne hi]
    exact min_eq_left (prevailing_le_current g h i)

end GittinsProof
-- END GittinsProof.PrevailingBasics

-- BEGIN GittinsProof.GreedySupport
open MeasureTheory ProbabilityTheory BanditAlgorithm
namespace GittinsProof
variable {k N : ℕ} {S : Type*} [MeasurableSpace S]

theorem positive_selection_mem (pi : MarkovBanditPolicy k S) (t : ℕ)
    (h : MarkovBanditHistory k S t) (A : Set (Fin k)) (hA : (pi.select t) h A = 1)
    (a : Fin k) (ha : 0 < ((pi.select t) h {a}).toReal) : a ∈ A := by
  by_contra hn
  have hc : (pi.select t) h Aᶜ = 0 := (prob_compl_eq_zero_iff (Set.toFinite A).measurableSet).mpr hA
  have hz : (pi.select t) h {a} = 0 := measure_mono_null (Set.singleton_subset_iff.mpr hn) hc
  rw [hz, ENNReal.toReal_zero] at ha
  exact (lt_irrefl _ ha)

theorem pathWeight_pos_factor (pi : MarkovBanditPolicy k S) (a : Fin N → Fin k)
    (w : Fin k → ℕ → S) (hp : 0 < pathWeight pi a w) (t : Fin N) :
    0 < ((pi.select t.val) (pathHistory a w t.val (Nat.le_of_lt t.isLt)) {a t}).toReal := by
  have hn : pathWeight pi a w ≠ 0 := ne_of_gt hp
  unfold pathWeight wordWeight at hn
  have ht := Finset.prod_ne_zero_iff.mp hn t (Finset.mem_univ t)
  exact lt_of_le_of_ne ENNReal.toReal_nonneg (Ne.symm ht)

theorem pathWeight_pos_max (P : Kernel S S) [IsMarkovKernel P] (r : S → ℝ) (beta : ℝ)
    (pi : MarkovBanditPolicy k S) (hpi : IsGittinsIndexPolicy P r beta pi)
    (a : Fin N → Fin k) (w : Fin k → ℕ → S) (hp : 0 < pathWeight pi a w) (t : Fin N) :
    ∀ j, gittinsIndex P r beta ((pathHistory a w t.val (Nat.le_of_lt t.isLt)).2 j) ≤
      gittinsIndex P r beta ((pathHistory a w t.val (Nat.le_of_lt t.isLt)).2 (a t)) :=
  positive_selection_mem pi t.val _ _ (hpi t.val _) (a t) (pathWeight_pos_factor pi a w hp t)

omit [MeasurableSpace S] in
theorem pathHistory_step (a : Fin N → Fin k) (w : Fin k → ℕ → S) (t : ℕ) (ht : t < N) :
    pathHistory a w (t+1) (by omega) = historySnoc (pathHistory a w t (by omega))
      (a ⟨t,ht⟩, w (a ⟨t,ht⟩) (playCount a (t+1) (a ⟨t,ht⟩))) :=
  replayHistory_step a (pathArray N w) t ht

omit [MeasurableSpace S] in
theorem current_after_snoc (g : S → ℝ) (h : MarkovBanditHistory k S N) (a : Fin k) (y : S) :
    (fun i => g ((historySnoc h (a,y)).2 i)) = Function.update (fun i => g (h.2 i)) a (g y) := by
  funext i
  by_cases hi : i = a
  · subst i; simp [historySnoc]
  · simp [historySnoc, Function.update_of_ne hi]

omit [MeasurableSpace S] in
theorem path_charge_invariant (g : S → ℝ) (a : Fin N → Fin k) (w : Fin k → ℕ → S)
    (t : ℕ) (ht : t ≤ N)
    (hmax : ∀ s (hs : s < t), ∀ j,
      g ((pathHistory a w s (by omega)).2 j) ≤
        g ((pathHistory a w s (by omega)).2 (a ⟨s,by omega⟩))) :
    ChargeInvariant (currentHistoryPrevailingCharge g t (pathHistory a w t ht))
      (fun i => g ((pathHistory a w t ht).2 i)) := by
  induction t with
  | zero => exact chargeInvariant_initial _
  | succ t ih =>
    have htn : t < N := by omega
    rw [pathHistory_step a w t htn, prevailing_snoc, current_after_snoc]
    apply chargeInvariant_update
    · exact prevailing_le_current g _
    · exact ih (by omega) (fun s hs => hmax s (by omega))
    · exact hmax t (by omega)

end GittinsProof
-- END GittinsProof.GreedySupport

-- BEGIN GittinsProof.PathCharges
open MeasureTheory ProbabilityTheory BanditAlgorithm
namespace GittinsProof
variable {k N : ℕ} {S : Type*}

def chargeStack (g : S → ℝ) (w : ℕ → S) : ℕ → ℝ
  | 0 => g (w 0)
  | n+1 => min (chargeStack g w n) (g (w (n+1)))

theorem chargeStack_antitone (g : S → ℝ) (w : ℕ → S) : Antitone (chargeStack g w) := by
  apply antitone_nat_of_succ_le
  intro n
  exact min_le_left _ _

theorem path_charge_stack (g : S → ℝ) (a : Fin N → Fin k) (w : Fin k → ℕ → S)
    (t : ℕ) (ht : t ≤ N) :
    currentHistoryPrevailingCharge g t (pathHistory a w t ht) =
      fun i => chargeStack g (w i) (playCount a t i) := by
  induction t with
  | zero =>
    funext i
    change g (w i (playCount a 0 i)) = chargeStack g (w i) (playCount a 0 i)
    rw [playCount_zero]
    rfl
  | succ t ih =>
    have htn : t < N := by omega
    rw [pathHistory_step a w t htn, prevailing_snoc, ih (by omega)]
    funext i
    by_cases hi : i = a ⟨t,htn⟩
    · subst i
      simp only [Function.update_self]
      rw [playCount_succ a t htn]
      simp only [↓reduceIte, chargeStack]
    · rw [Function.update_of_ne hi, playCount_succ a t htn]
      simp [Ne.symm hi]

variable [MeasurableSpace S]

theorem greedy_charge_stack (P : Kernel S S) [IsMarkovKernel P] (r : S → ℝ) (beta : ℝ)
    (pi : MarkovBanditPolicy k S) (hpi : IsGittinsIndexPolicy P r beta pi)
    (a : Fin N → Fin k) (w : Fin k → ℕ → S) (hp : 0 < pathWeight pi a w)
    (t : ℕ) (ht : t < N) (j : Fin k) :
    chargeStack (gittinsIndex P r beta) (w j) (playCount a t j) ≤
      chargeStack (gittinsIndex P r beta) (w (a ⟨t,ht⟩)) (playCount a t (a ⟨t,ht⟩)) := by
  let g := gittinsIndex P r beta
  have hmax := pathWeight_pos_max P r beta pi hpi a w hp ⟨t,ht⟩
  have hi := path_charge_invariant g a w t (Nat.le_of_lt ht) (fun s hs =>
    pathWeight_pos_max P r beta pi hpi a w hp ⟨s,lt_trans hs ht⟩)
  have hg := greedy_idle _ _ (prevailing_le_current g _) hi (a ⟨t,ht⟩) hmax
  by_cases hj : j = a ⟨t,ht⟩
  · subst j; exact le_rfl
  · have hh := (hg j hj).2
    simpa only [path_charge_stack] using hh

end GittinsProof
-- END GittinsProof.PathCharges

-- BEGIN GittinsProof.DeterministicComparison
open MeasureTheory ProbabilityTheory BanditAlgorithm
namespace GittinsProof
variable {k N : ℕ}

theorem deterministic_playCount_mono (a : Fin N → Fin k) {s t : ℕ} (hst : s ≤ t) (i : Fin k) :
    playCount a s i ≤ playCount a t i := by
  apply Finset.card_le_card
  intro j hj
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj ⊢
  exact ⟨lt_of_lt_of_le hj.1 hst, hj.2⟩

theorem playCount_sum (a : Fin N → Fin k) (t : ℕ) (ht : t ≤ N) :
    ∑ i : Fin k, playCount a t i = t := by
  induction t with
  | zero => simp [playCount_zero]
  | succ t ih =>
    have htN : t < N := by omega
    simp_rw [playCount_succ a t htN]
    rw [Finset.sum_add_distrib, ih (by omega)]
    simp

theorem greedy_remaining_le (H : Fin k → ℕ → ℝ) (hH : ∀ i, Antitone (H i))
    (a b : Fin N → Fin k) (t : ℕ) (ht : t ≤ N)
    (ha : ∀ (s : ℕ) (hs : s < t) (i : Fin k),
      H i (playCount a s i) ≤ H (a ⟨s, lt_of_lt_of_le hs ht⟩)
        (playCount a s (a ⟨s, lt_of_lt_of_le hs ht⟩))) (j : Fin k) :
    H j (playCount a t j) ≤ ⨆ i : Fin k, H i (playCount b t i) := by
  classical
  by_contra hn
  have hz : (⨆ i : Fin k, H i (playCount b t i)) < H j (playCount a t j) := lt_of_not_ge hn
  have hb (i : Fin k) : H i (playCount b t i) < H j (playCount a t j) :=
    lt_of_le_of_lt (le_ciSup (Set.finite_range (fun i : Fin k => H i (playCount b t i))).bddAbove i) hz
  have hinv : ∀ s, s ≤ t → ∀ i, playCount a s i ≤ playCount b t i := by
    intro s
    induction s with
    | zero => intro _ i; simp [playCount_zero]
    | succ s ih =>
      intro hs i
      have hst : s < t := by omega
      have hsN : s < N := lt_of_lt_of_le hst ht
      let q := a ⟨s, hsN⟩
      have hq : playCount a s q < playCount b t q := by
        by_contra hh
        have hc := hH q (le_of_not_gt hh)
        have hg := ha s hst j
        have hj := hH j (deterministic_playCount_mono a (Nat.le_of_lt hst) j)
        have htq := hb q
        change H j (playCount a s j) ≤ H q (playCount a s q) at hg
        linarith
      rw [playCount_succ a s hsN]
      by_cases hi : q = i
      · subst i
        simp only [show a ⟨s, hsN⟩ = q from rfl, ↓reduceIte]
        omega
      · simp only [show a ⟨s, hsN⟩ ≠ i from hi, ↓reduceIte, add_zero]
        exact ih (by omega) i
  have hcounts : playCount a t j = playCount b t j := by
    by_contra hne
    have hlt : playCount a t j < playCount b t j := lt_of_le_of_ne (hinv t le_rfl j) hne
    have hsum := Finset.sum_lt_sum (fun i _ => hinv t le_rfl i) ⟨j, Finset.mem_univ j, hlt⟩
    rw [playCount_sum a t ht, playCount_sum b t ht] at hsum
    exact (lt_irrefl t) hsum
  rw [hcounts] at hz
  exact (not_lt_of_ge (le_ciSup (Set.finite_range (fun i : Fin k => H i (playCount b t i))).bddAbove j)) hz

theorem greedy_remaining_sup_le [Nonempty (Fin k)] (H : Fin k → ℕ → ℝ)
    (hH : ∀ i, Antitone (H i)) (a b : Fin N → Fin k) (t : ℕ) (ht : t ≤ N)
    (ha : ∀ (s : ℕ) (hs : s < t) (i : Fin k),
      H i (playCount a s i) ≤ H (a ⟨s, lt_of_lt_of_le hs ht⟩)
        (playCount a s (a ⟨s, lt_of_lt_of_le hs ht⟩))) :
    (⨆ i : Fin k, H i (playCount a t i)) ≤ ⨆ i : Fin k, H i (playCount b t i) := by
  apply ciSup_le
  exact greedy_remaining_le H hH a b t ht ha
end GittinsProof
-- END GittinsProof.DeterministicComparison

-- BEGIN GittinsProof.WeightedComparison
namespace GittinsProof
variable {I J : Type*} [Fintype I] [Fintype J]

theorem weighted_compare (u : I → ℝ) (v : J → ℝ) (A : I → ℝ) (B : J → ℝ)
    (hu : ∀ i, 0 ≤ u i) (hv : ∀ j, 0 ≤ v j)
    (hsu : ∑ i, u i = 1) (hsv : ∑ j, v j = 1)
    (hAB : ∀ i, 0 < u i → ∀ j, A i ≤ B j) :
    (∑ i, u i * A i) ≤ ∑ j, v j * B j := by
  calc
    _ ≤ ∑ i, u i * (∑ j, v j * B j) := by
      apply Finset.sum_le_sum
      intro i _
      by_cases hi : u i = 0
      · simp [hi]
      · apply mul_le_mul_of_nonneg_left _ (hu i)
        calc
          A i = ∑ j, v j * A i := by rw [← Finset.sum_mul, hsv, one_mul]
          _ ≤ ∑ j, v j * B j := Finset.sum_le_sum (fun j _ =>
            mul_le_mul_of_nonneg_left (hAB i (lt_of_le_of_ne (hu i) (Ne.symm hi)) j) (hv j))
    _ = _ := by rw [← Finset.sum_mul, hsu, one_mul]

end GittinsProof
-- END GittinsProof.WeightedComparison

-- BEGIN GittinsProof.MaxCharge
open MeasureTheory ProbabilityTheory BanditAlgorithm
namespace GittinsProof
variable {k N : ℕ} {S : Type*} [MeasurableSpace S]

noncomputable def maxCharge (g : S → ℝ) (n : ℕ) (h : MarkovBanditHistory k S n) : ℝ :=
  ⨆ i : Fin k, currentHistoryPrevailingCharge g n h i

theorem measurable_maxCharge (g : S → ℝ) (hg : Measurable g) (n : ℕ) :
    Measurable (maxCharge (k := k) g n) :=
  Measurable.iSup (fun i => prevailing_measurable g hg i n)

omit [MeasurableSpace S] in
theorem maxCharge_bounds [Nonempty (Fin k)] (g : S → ℝ) (M : ℝ)
    (hg : ∀ y, 0 ≤ g y ∧ g y ≤ M) (h : MarkovBanditHistory k S N) :
    0 ≤ maxCharge g N h ∧ maxCharge g N h ≤ M := by
  constructor
  · obtain ⟨i⟩ := ‹Nonempty (Fin k)›
    exact (prevailing_nonneg g (fun y => (hg y).1) h i).trans
      (le_ciSup (Set.finite_range _).bddAbove i)
  · exact ciSup_le (fun i => prevailing_le_bound g M (fun y => (hg y).2) h i)

theorem greedy_path_max_le [Nonempty (Fin k)] (P : Kernel S S) [IsMarkovKernel P]
    (r : S → ℝ) (beta : ℝ) (pi : MarkovBanditPolicy k S)
    (hpi : IsGittinsIndexPolicy P r beta pi) (a b : Fin N → Fin k)
    (w : Fin k → ℕ → S) (hp : 0 < pathWeight pi a w) :
    maxCharge (gittinsIndex P r beta) N (pathHistory a w N le_rfl) ≤
      maxCharge (gittinsIndex P r beta) N (pathHistory b w N le_rfl) := by
  unfold maxCharge
  simp only [path_charge_stack]
  exact greedy_remaining_sup_le (fun i => chargeStack (gittinsIndex P r beta) (w i))
    (fun i => chargeStack_antitone _ _) a b N le_rfl
      (fun t ht j => greedy_charge_stack P r beta pi hpi a w hp t ht j)

theorem pathWeight_sum (pi : MarkovBanditPolicy k S) (w : Fin k → ℕ → S) :
    (∑ a : Fin N → Fin k, pathWeight pi a w) = 1 := wordWeight_sum pi (pathArray N w)

theorem weighted_max_comparison [Nonempty (Fin k)] (P : Kernel S S) [IsMarkovKernel P]
    (r : S → ℝ) (beta : ℝ) (pistar pi : MarkovBanditPolicy k S)
    (hpi : IsGittinsIndexPolicy P r beta pistar) (w : Fin k → ℕ → S) :
    (∑ a : Fin N → Fin k, pathWeight pistar a w *
      maxCharge (gittinsIndex P r beta) N (pathHistory a w N le_rfl)) ≤
    ∑ b : Fin N → Fin k, pathWeight pi b w *
      maxCharge (gittinsIndex P r beta) N (pathHistory b w N le_rfl) := by
  exact weighted_compare _ _ _ _ (fun a => (pathWeight_bounds pistar a w).1)
    (fun b => (pathWeight_bounds pi b w).1) (pathWeight_sum pistar w) (pathWeight_sum pi w)
      (fun a ha b => greedy_path_max_le P r beta pistar hpi a b w ha)

end GittinsProof
-- END GittinsProof.MaxCharge

-- BEGIN GittinsProof.HistoryStep
open MeasureTheory ProbabilityTheory BanditAlgorithm
namespace GittinsProof
variable {k n : ℕ} {S : Type*} [MeasurableSpace S]

theorem abs_integral_le_bound {A : Type*} [MeasurableSpace A] (mu : Measure A)
    [IsProbabilityMeasure mu] (f : A → ℝ) (C : ℝ) (hC : ∀ a, |f a| ≤ C) :
    |∫ a, f a ∂mu| ≤ C := by
  have hh : ∀ᵐ a ∂mu, ‖f a‖ ≤ C := ae_of_all _ (fun a => by simpa only [Real.norm_eq_abs] using hC a)
  simpa using norm_integral_le_of_norm_le_const hh

noncomputable def stepValue (P : Kernel S S) [IsMarkovKernel P] (pi : MarkovBanditPolicy k S)
    (F : MarkovBanditHistory k S (n+1) → ℝ) (h : MarkovBanditHistory k S n) : ℝ :=
  ∫ z, F (historySnoc h z) ∂markovBanditStepKernel P pi n h

theorem measurable_stepValue (P : Kernel S S) [IsMarkovKernel P] (pi : MarkovBanditPolicy k S)
    (F : MarkovBanditHistory k S (n+1) → ℝ) (hF : Measurable F) :
    Measurable (stepValue P pi F) :=
  (hF.comp measurable_historySnoc).stronglyMeasurable.integral_kernel_prod_right'.measurable

theorem stepValue_bound (P : Kernel S S) [IsMarkovKernel P] (pi : MarkovBanditPolicy k S)
    (F : MarkovBanditHistory k S (n+1) → ℝ) (C : ℝ) (hC : ∀ h, |F h| ≤ C)
    (h : MarkovBanditHistory k S n) : |stepValue P pi F h| ≤ C :=
  abs_integral_le_bound _ _ C (fun _ => hC _)

theorem stepValue_sum (P : Kernel S S) [IsMarkovKernel P] (pi : MarkovBanditPolicy k S)
    (F : MarkovBanditHistory k S (n+1) → ℝ) (hF : Measurable F)
    (C : ℝ) (hC : ∀ h, |F h| ≤ C) (h : MarkovBanditHistory k S n) :
    stepValue P pi F h = ∑ a : Fin k, ((pi.select n) h {a}).toReal *
      ∫ y, F (historySnoc h (a,y)) ∂P (h.2 a) := by
  unfold stepValue markovBanditStepKernel
  rw [ProbabilityTheory.integral_compProd]
  · rw [integral_fintype]
    · rfl
    · exact Integrable.of_finite
  · exact bounded_integrable _ _
      (hF.comp (measurable_historySnoc.comp (measurable_const.prodMk measurable_id))) C (fun _ => hC _)

end GittinsProof
-- END GittinsProof.HistoryStep

-- BEGIN GittinsProof.ChargeCertificate
open MeasureTheory ProbabilityTheory BanditAlgorithm
namespace GittinsProof
variable {k n : ℕ} {S : Type*} [MeasurableSpace S]

structure ChargeCertificate (P : Kernel S S) (r : S → ℝ) (beta : ℝ)
    (g : S → ℝ) (U : ℝ → S → ℝ) (M B : ℝ) : Prop where
  g_measurable : Measurable g
  U_measurable : Measurable (Function.uncurry U)
  g_bounds : ∀ x, 0 ≤ g x ∧ g x ≤ M
  M_nonneg : 0 ≤ M
  B_nonneg : 0 ≤ B
  U_bounds : ∀ c x, 0 ≤ c → c ≤ M → 0 ≤ U c x ∧ U c x ≤ B
  zero : ∀ c x, g x ≤ c → U c x = 0
  continuation : ∀ c x, c ≤ g x → U c x = r x - c + beta * ∫ y, U c y ∂P x

noncomputable def totalChargePotential (U : ℝ → S → ℝ) (g : S → ℝ)
    (n : ℕ) (h : MarkovBanditHistory k S n) : ℝ :=
  ∑ i : Fin k, U (currentHistoryPrevailingCharge g n h i) (h.2 i)

theorem potential_measurable {P : Kernel S S} {r : S → ℝ} {beta : ℝ}
    {g : S → ℝ} {U : ℝ → S → ℝ} {M B : ℝ} (D : ChargeCertificate P r beta g U M B) :
    Measurable (totalChargePotential (k := k) U g n) := by
  apply Finset.measurable_sum
  intro i _
  exact D.U_measurable.comp ((prevailing_measurable g D.g_measurable i n).prodMk
    ((measurable_pi_apply i).comp measurable_snd))

theorem potential_bounds {P : Kernel S S} {r : S → ℝ} {beta : ℝ}
    {g : S → ℝ} {U : ℝ → S → ℝ} {M B : ℝ} (D : ChargeCertificate P r beta g U M B)
    (h : MarkovBanditHistory k S n) :
    0 ≤ totalChargePotential U g n h ∧ totalChargePotential U g n h ≤ k*B := by
  have hb (i : Fin k) := D.U_bounds (currentHistoryPrevailingCharge g n h i) (h.2 i)
    (prevailing_nonneg g (fun y => (D.g_bounds y).1) h i)
    (prevailing_le_bound g M (fun y => (D.g_bounds y).2) h i)
  constructor
  · exact Finset.sum_nonneg (fun i _ => (hb i).1)
  · calc
      _ ≤ ∑ _i : Fin k, B := Finset.sum_le_sum (fun i _ => (hb i).2)
      _ = _ := by simp

theorem potential_initial {P : Kernel S S} {r : S → ℝ} {beta : ℝ}
    {g : S → ℝ} {U : ℝ → S → ℝ} {M B : ℝ} (D : ChargeCertificate P r beta g U M B)
    (x : Fin k → S) : totalChargePotential U g 0 (Fin.elim0,x) = 0 := by
  apply Finset.sum_eq_zero
  intro i _
  exact D.zero _ _ le_rfl

theorem retirement_reset {P : Kernel S S} {r : S → ℝ} {beta : ℝ}
    {g : S → ℝ} {U : ℝ → S → ℝ} {M B : ℝ} (D : ChargeCertificate P r beta g U M B)
    (c : ℝ) (y : S) : U (min c (g y)) y = U c y := by
  by_cases hc : c ≤ g y
  · rw [min_eq_left hc]
  · rw [min_eq_right (le_of_not_ge hc), D.zero _ _ le_rfl, D.zero _ _ (le_of_not_ge hc)]

theorem potential_snoc {P : Kernel S S} {r : S → ℝ} {beta : ℝ}
    {g : S → ℝ} {U : ℝ → S → ℝ} {M B : ℝ} (D : ChargeCertificate P r beta g U M B)
    (h : MarkovBanditHistory k S n) (a : Fin k) (y : S) :
    totalChargePotential U g (n+1) (historySnoc h (a,y)) =
      totalChargePotential U g n h - U (currentHistoryPrevailingCharge g n h a) (h.2 a) +
        U (currentHistoryPrevailingCharge g n h a) y := by
  have he : (fun i => U (currentHistoryPrevailingCharge g (n+1) (historySnoc h (a,y)) i)
      ((historySnoc h (a,y)).2 i)) =
      Function.update (fun i => U (currentHistoryPrevailingCharge g n h i) (h.2 i)) a
        (U (currentHistoryPrevailingCharge g n h a) y) := by
    rw [prevailing_snoc]
    funext i
    by_cases hi : i = a
    · subst i
      simp only [Function.update_self, historySnoc]
      exact retirement_reset D _ _
    · simp [Function.update_of_ne hi, historySnoc]
  unfold totalChargePotential
  rw [he, Finset.sum_update_of_mem (Finset.mem_univ a)]
  have hs := Finset.sum_erase_add (Finset.univ : Finset (Fin k))
    (fun i => U (currentHistoryPrevailingCharge g n h i) (h.2 i)) (Finset.mem_univ a)
  simp only [Finset.sdiff_singleton_eq_erase]
  linarith

end GittinsProof
-- END GittinsProof.ChargeCertificate

-- BEGIN GittinsProof.NativeCertificate
open MeasureTheory ProbabilityTheory BanditAlgorithm
namespace GittinsProof
variable {S : Type*} [MeasurableSpace S]

theorem native_charge_certificate (P : Kernel S S) [IsMarkovKernel P]
    {r : S → ℝ} (hrm : Measurable r) {β C : ℝ} (hβ : 0 ≤ β) (hβ1 : β < 1)
    (hC : 0 ≤ C) (hr : ∀ y, 0 ≤ r y ∧ r y ≤ C) :
    ChargeCertificate P r β (gittinsIndex P r β) (gittinsRetirementValue P r β) C (2*C/(1-β)) := by
  have hab : ∀ y, |r y| ≤ C := fun y => by rw [abs_of_nonneg (hr y).1]; exact (hr y).2
  refine ⟨index_measurable P hrm hβ hβ1 hC hr,
    retirement_joint_measurable P hrm hβ hβ1 hC hab,
    fun x => index_bounds P x hrm hβ hβ1 hC hr, hC, by positivity, ?_, ?_, ?_⟩
  · intro c x hc0 hcC
    have hM : 0 ≤ 2*C := by positivity
    have hbound : ∀ y, |r y-c| ≤ 2*C := by
      intro y
      have hh := abs_sub (r y) c
      rw [abs_of_nonneg (hr y).1, abs_of_nonneg hc0] at hh
      linarith [(hr y).2]
    exact ⟨retirement_nonneg P r hβ hβ1 hM hbound x, retirement_bound P r hβ hβ1 hM hbound x⟩
  · intro c x hc
    exact retirement_zero P x hrm hβ hβ1 hC hr c hc
  · intro c x hc
    exact retirement_continue P x hrm hβ hβ1 hC hr c hc
end GittinsProof
-- END GittinsProof.NativeCertificate

-- BEGIN GittinsProof.RewardBasics
open MeasureTheory ProbabilityTheory BanditAlgorithm
namespace GittinsProof
variable {k n : ℕ} {S : Type*} [MeasurableSpace S]

def instantReward (r : S → ℝ) (n : ℕ) (h : MarkovBanditHistory k S (n+1)) : ℝ :=
  r ((h.1 (Fin.last n)).1 ((h.1 (Fin.last n)).2))

theorem measurable_instantReward (r : S → ℝ) (hr : Measurable r) :
    Measurable (instantReward (k := k) r n) := by
  have hh := (measurable_pi_apply (Fin.last n)).comp
    (measurable_fst : Measurable (fun h : MarkovBanditHistory k S (n+1) => h.1))
  have hev : Measurable (fun p : (Fin k → S) × Fin k => p.1 p.2) :=
    measurable_from_prod_countable_left (fun a => measurable_pi_apply a)
  exact hr.comp (hev.comp hh)

omit [MeasurableSpace S] in
theorem instantReward_snoc (r : S → ℝ) (h : MarkovBanditHistory k S n) (a : Fin k) (y : S) :
    instantReward r n (historySnoc h (a,y)) = r (h.2 a) := by
  simp [instantReward, historySnoc]

theorem reward_step_sum (P : Kernel S S) [IsMarkovKernel P] (pi : MarkovBanditPolicy k S)
    (r : S → ℝ) (hr : Measurable r) (R : ℝ) (hR : ∀ y, |r y| ≤ R)
    (h : MarkovBanditHistory k S n) :
    stepValue P pi (instantReward r n) h = ∑ a : Fin k, ((pi.select n) h {a}).toReal * r (h.2 a) := by
  rw [stepValue_sum P pi _ (measurable_instantReward r hr) R (fun _ => hR _) h]
  simp only [instantReward_snoc, integral_const]
  simp

theorem round_reward_step (P : Kernel S S) [IsMarkovKernel P] (pi : MarkovBanditPolicy k S)
    (x : Fin k → S) (r : S → ℝ) (hr : Measurable r) (R : ℝ) (hR : ∀ y, |r y| ≤ R) :
    markovBanditRoundReward P r pi x n =
      ∫ h, stepValue P pi (instantReward r n) h ∂markovBanditMeasure P pi x n :=
  history_integral_succ P pi x (instantReward r n) (measurable_instantReward r hr) R (fun _ => hR _)

theorem round_reward_bound (P : Kernel S S) [IsMarkovKernel P] (pi : MarkovBanditPolicy k S)
    (x : Fin k → S) (r : S → ℝ) (R : ℝ) (hR : ∀ y, |r y| ≤ R) :
    |markovBanditRoundReward P r pi x n| ≤ R :=
  abs_integral_le_bound _ _ R (fun _ => hR _)

end GittinsProof
-- END GittinsProof.RewardBasics

-- BEGIN GittinsProof.ChainConditional
open MeasureTheory ProbabilityTheory BanditAlgorithm
namespace GittinsProof
variable {S : Type*} [MeasurableSpace S]

def fillPrefix (x : S) (n : ℕ) (v : Finset.Iic n → S) (t : ℕ) : S :=
  if h : t ≤ n then v ⟨t, Finset.mem_Iic.mpr h⟩ else x

theorem measurable_fillPrefix (x : S) (n : ℕ) : Measurable (fillPrefix x n) := by
  apply measurable_pi_lambda
  intro t
  by_cases h : t ≤ n
  · simpa [fillPrefix, h] using (measurable_pi_apply (⟨t, Finset.mem_Iic.mpr h⟩ : Finset.Iic n))
  · simp [fillPrefix, h]

omit [MeasurableSpace S] in
theorem fillPrefix_agrees (x : S) (n : ℕ) (w : ℕ → S) (t : ℕ) (ht : t ≤ n) :
    fillPrefix x n (Preorder.frestrictLe n w) t = w t := by
  simp [fillPrefix, ht, Preorder.frestrictLe]

theorem chain_conditional_integral (P : Kernel S S) [IsMarkovKernel P] (x : S) (n : ℕ)
    (F : (ℕ → S) → S → ℝ) (hF : Measurable (Function.uncurry F))
    (C : ℝ) (hC : ∀ w y, |F w y| ≤ C)
    (hdep : ∀ w v, (∀ t, t ≤ n → w t = v t) → ∀ y, F w y = F v y) :
    (∫ w, F w (w (n+1)) ∂markovChainMeasure P x) =
      ∫ w, ∫ y, F w y ∂P (w n) ∂markovChainMeasure P x := by
  let H : (Finset.Iic n → S) × S → ℝ := fun z => F (fillPrefix x n z.1) z.2
  have hH : Measurable H := hF.comp ((measurable_fillPrefix x n).comp measurable_fst |>.prodMk measurable_snd)
  have hsame (w : ℕ → S) (y : S) : H (Preorder.frestrictLe n w, y) = F w y := by
    exact hdep _ _ (fun t ht => fillPrefix_agrees x n w t ht) y
  have hleft : (∫ z, H z ∂((markovChainMeasure P x).map
      (fun w => (Preorder.frestrictLe n w, w (n+1))))) =
      ∫ w, F w (w (n+1)) ∂markovChainMeasure P x := by
    rw [integral_map (by fun_prop) hH.aestronglyMeasurable]
    exact integral_congr_ae (ae_of_all _ fun w => hsame w _)
  rw [← hleft, ← chain_prefix_next]
  rw [Measure.integral_compProd (bounded_integrable _ H hH C (fun z => hC _ _))]
  have hm : StronglyMeasurable (fun v : Finset.Iic n → S =>
      ∫ y, H (v,y) ∂markovChainStep P n v) :=
    hH.stronglyMeasurable.integral_kernel_prod_right'
  rw [integral_map (by fun_prop) hm.aestronglyMeasurable]
  apply integral_congr_ae
  filter_upwards [] with w
  change (∫ y, H (Preorder.frestrictLe n w,y) ∂P (w n)) = _
  exact integral_congr_ae (ae_of_all _ fun y => hsame w y)

end GittinsProof
-- END GittinsProof.ChainConditional

-- BEGIN GittinsProof.ArrayConditional
open MeasureTheory ProbabilityTheory BanditAlgorithm
namespace GittinsProof
variable {k : ℕ} {S : Type*} [MeasurableSpace S]

noncomputable def restoreArm (a : Fin (k+1)) :
    (ℕ → S) × (Fin k → ℕ → S) ≃ᵐ (Fin (k+1) → ℕ → S) :=
  (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (k+1) => ℕ → S) a).symm

theorem restoreArm_selected (a : Fin (k+1)) (w : ℕ → S) (v : Fin k → ℕ → S) :
    restoreArm a (w,v) a = w := by
  simp [restoreArm, MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv]

theorem integral_pi_split (mu : Fin (k+1) → Measure (ℕ → S))
    [∀ i, IsProbabilityMeasure (mu i)] (a : Fin (k+1))
    (f : (Fin (k+1) → ℕ → S) → ℝ) (hf : Measurable f)
    (C : ℝ) (hC : ∀ w, |f w| ≤ C) :
    (∫ w, f w ∂Measure.pi mu) =
      ∫ v, ∫ w, f (restoreArm a (w,v)) ∂mu a
        ∂Measure.pi (fun j => mu (a.succAbove j)) := by
  rw [← ((measurePreserving_piFinSuccAbove mu a).symm).integral_comp']
  exact integral_prod_symm _ (bounded_integrable _ _
    (hf.comp (restoreArm a).measurable) C (fun z => hC _))

theorem array_conditional_integral (P : Kernel S S) [IsMarkovKernel P]
    (x : Fin (k+1) → S) (a : Fin (k+1)) (n : ℕ)
    (F : (Fin (k+1) → ℕ → S) → S → ℝ)
    (hF : Measurable (Function.uncurry F)) (C : ℝ) (hC : ∀ w y, |F w y| ≤ C)
    (hdep : ∀ v w z, (∀ t, t ≤ n → w t = z t) → ∀ y,
      F (restoreArm a (w,v)) y = F (restoreArm a (z,v)) y) :
    (∫ w, F w (w a (n+1)) ∂Measure.pi (fun i => markovChainMeasure P (x i))) =
      ∫ w, ∫ y, F w y ∂P (w a n) ∂Measure.pi (fun i => markovChainMeasure P (x i)) := by
  let K : Kernel (Fin (k+1) → ℕ → S) S :=
    P.comap (fun w => w a n) ((measurable_pi_apply n).comp (measurable_pi_apply a))
  have hm : Measurable (fun w => ∫ y, F w y ∂K w) :=
    hF.stronglyMeasurable.integral_kernel_prod_right.measurable
  have hb (w : Fin (k+1) → ℕ → S) : |∫ y, F w y ∂K w| ≤ C := by
    have hh : ∀ᵐ y ∂K w, ‖F w y‖ ≤ C := ae_of_all _ (fun y => by simpa only [Real.norm_eq_abs] using hC w y)
    simpa only [Real.norm_eq_abs, Measure.real, measure_univ, ENNReal.toReal_one, mul_one] using norm_integral_le_of_norm_le_const hh
  change _ = ∫ w, ∫ y, F w y ∂K w ∂Measure.pi (fun i => markovChainMeasure P (x i))
  have hleft : Measurable (fun w => F w (w a (n+1))) := hF.comp (measurable_id.prodMk (by fun_prop))
  rw [integral_pi_split _ a _ hleft C (fun w => hC w _),
    integral_pi_split _ a _ hm C hb]
  apply integral_congr_ae
  filter_upwards [] with v
  simp only [restoreArm_selected]
  have hh : Measurable (Function.uncurry (fun w y => F (restoreArm a (w,v)) y)) :=
    hF.comp (((restoreArm a).measurable.comp (measurable_fst.prodMk measurable_const)).prodMk measurable_snd)
  simpa [K, restoreArm_selected] using
    chain_conditional_integral P (x a) n (fun w y => F (restoreArm a (w,v)) y)
      hh C (fun w y => hC _ _) (hdep v)

end GittinsProof
-- END GittinsProof.ArrayConditional

-- BEGIN GittinsProof.WordStep
open MeasureTheory ProbabilityTheory BanditAlgorithm
namespace GittinsProof
variable {k N : ℕ} {S : Type*} [MeasurableSpace S]

theorem restoreArm_other (a : Fin (k+1)) (w : ℕ → S) (v : Fin k → ℕ → S) (j : Fin k) :
    restoreArm a (w,v) (a.succAbove j) = v j := by
  simp [restoreArm, MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv]

theorem restoreArm_prefix (a : Fin (k+1)) (c : Fin (k+1) → ℕ)
    (v : Fin k → ℕ → S) (w z : ℕ → S) (h : ∀ t, t ≤ c a → w t = z t) :
    ∀ i t, t ≤ c i → restoreArm a (w,v) i t = restoreArm a (z,v) i t := by
  intro i
  refine Fin.succAboveCases a ?_ (fun j => ?_) i
  · simpa only [restoreArm_selected] using h
  · intro t _
    simp only [restoreArm_other]

theorem selection_bounds (pi : MarkovBanditPolicy k S) (h : MarkovBanditHistory k S N) (a : Fin k) :
    0 ≤ ((pi.select N) h {a}).toReal ∧ ((pi.select N) h {a}).toReal ≤ 1 := by
  refine ⟨ENNReal.toReal_nonneg, ?_⟩
  rw [← selection_mass pi N h]
  exact Finset.single_le_sum (f := fun b : Fin k => ((pi.select N) h {b}).toReal) (fun _ _ => ENNReal.toReal_nonneg) (Finset.mem_univ a)

theorem word_step_integral (P : Kernel S S) [IsMarkovKernel P]
    (pi : MarkovBanditPolicy (k+1) S) (x : Fin (k+1) → S)
    (a : Fin N → Fin (k+1)) (b : Fin (k+1))
    (F : MarkovBanditHistory (k+1) S (N+1) → ℝ) (hF : Measurable F)
    (C : ℝ) (hC : ∀ h, |F h| ≤ C) :
    (∫ w, pathWeight pi (Fin.snoc a b) w *
      F (pathHistory (Fin.snoc a b) w (N+1) le_rfl)
      ∂Measure.pi (fun i => markovChainMeasure P (x i))) =
    ∫ w, pathWeight pi a w * ((pi.select N) (pathHistory a w N le_rfl) {b}).toReal *
      (∫ y, F (historySnoc (pathHistory a w N le_rfl) (b,y))
        ∂P (w b (playCount a N b)))
      ∂Measure.pi (fun i => markovChainMeasure P (x i)) := by
  let H : (Fin (k+1) → ℕ → S) → S → ℝ := fun w y =>
    pathWeight pi a w * ((pi.select N) (pathHistory a w N le_rfl) {b}).toReal *
      F (historySnoc (pathHistory a w N le_rfl) (b,y))
  have hmH : Measurable (Function.uncurry H) := by
    have hh : Measurable (fun z : (Fin (k+1) → ℕ → S) × S => pathHistory a z.1 N le_rfl) :=
      (measurable_pathHistory a N le_rfl).comp measurable_fst
    have hw : Measurable (fun z : (Fin (k+1) → ℕ → S) × S => pathWeight pi a z.1) :=
      (measurable_pathWeight pi a).comp measurable_fst
    have hs := (((pi.select N).measurable_coe (measurableSet_singleton b)).comp hh).ennreal_toReal
    exact (hw.mul hs).mul (hF.comp (measurable_historySnoc.comp
      (hh.prodMk (measurable_const.prodMk measurable_snd))))
  have hbH (w : Fin (k+1) → ℕ → S) (y : S) : |H w y| ≤ C := by
    dsimp [H]
    rw [abs_mul, abs_mul, abs_of_nonneg (pathWeight_bounds pi a w).1,
      abs_of_nonneg (selection_bounds pi _ b).1]
    have hw := (pathWeight_bounds pi a w).2
    have hs := (selection_bounds pi (pathHistory a w N le_rfl) b).2
    exact (mul_le_of_le_one_left (abs_nonneg _) (mul_le_one₀ hw (selection_bounds pi _ b).1 hs)).trans (hC _)
  have hdH : ∀ v w z, (∀ t, t ≤ playCount a N b → w t = z t) → ∀ y,
      H (restoreArm b (w,v)) y = H (restoreArm b (z,v)) y := by
    intro v w z h y
    have hp := restoreArm_prefix b (playCount a N) v w z h
    have hh := pathHistory_congr a N le_rfl _ _ hp
    have hw := pathWeight_congr pi a _ _ hp
    simp only [H, hh, hw]
  have he := array_conditional_integral P x b (playCount a N b) H hmH C hbH hdH
  simpa only [H, pathWeight_snoc, pathHistory_terminal_snoc, integral_const_mul] using he

end GittinsProof
-- END GittinsProof.WordStep

-- BEGIN GittinsProof.ArmStep
open MeasureTheory ProbabilityTheory BanditAlgorithm
namespace GittinsProof
variable {k n : ℕ} {S : Type*} [MeasurableSpace S]

noncomputable def armStepValue (P : Kernel S S) [IsMarkovKernel P]
    (F : MarkovBanditHistory k S (n+1) → ℝ) (a : Fin k) (h : MarkovBanditHistory k S n) : ℝ :=
  ∫ y, F (historySnoc h (a,y)) ∂P (h.2 a)

theorem measurable_armStepValue (P : Kernel S S) [IsMarkovKernel P]
    (F : MarkovBanditHistory k S (n+1) → ℝ) (hF : Measurable F) (a : Fin k) :
    Measurable (armStepValue P F a) := by
  let K : Kernel (MarkovBanditHistory k S n) S := P.comap (fun h : MarkovBanditHistory k S n => h.2 a)
    ((measurable_pi_apply a).comp measurable_snd)
  have hm : Measurable (fun z : MarkovBanditHistory k S n × S => F (historySnoc z.1 (a,z.2))) :=
    hF.comp (measurable_historySnoc.comp (measurable_fst.prodMk (measurable_const.prodMk measurable_snd)))
  exact (hm.stronglyMeasurable.integral_kernel_prod_right' (κ := K)).measurable

theorem armStepValue_bound (P : Kernel S S) [IsMarkovKernel P]
    (F : MarkovBanditHistory k S (n+1) → ℝ) (C : ℝ) (hC : ∀ h, |F h| ≤ C)
    (a : Fin k) (h : MarkovBanditHistory k S n) : |armStepValue P F a h| ≤ C :=
  abs_integral_le_bound _ _ C (fun _ => hC _)

theorem weighted_abs_bound {w v z C : ℝ} (hw : 0 ≤ w ∧ w ≤ 1)
    (hv : 0 ≤ v ∧ v ≤ 1) (hz : |z| ≤ C) : |w*v*z| ≤ C := by
  rw [abs_mul, abs_mul, abs_of_nonneg hw.1, abs_of_nonneg hv.1]
  exact (mul_le_of_le_one_left (abs_nonneg _) (mul_le_one₀ hw.2 hv.1 hv.2)).trans hz

end GittinsProof
-- END GittinsProof.ArmStep

-- BEGIN GittinsProof.GreedyAccounting
open MeasureTheory ProbabilityTheory BanditAlgorithm
namespace GittinsProof
variable {k n : ℕ} {S : Type*} [MeasurableSpace S]

theorem greedy_potential_arm {P : Kernel S S} [IsMarkovKernel P] {r : S → ℝ} {beta : ℝ}
    {g : S → ℝ} {U : ℝ → S → ℝ} {M B : ℝ} (D : ChargeCertificate P r beta g U M B)
    (h : MarkovBanditHistory k S n)
    (hinv : ChargeInvariant (currentHistoryPrevailingCharge g n h) (fun i => g (h.2 i)))
    (a : Fin k) (ha : ∀ j, g (h.2 j) ≤ g (h.2 a)) :
    totalChargePotential U g n h = U (currentHistoryPrevailingCharge g n h a) (h.2 a) := by
  apply Finset.sum_eq_single a
  · intro j _ hj
    have he := (greedy_idle _ _ (prevailing_le_current g h) hinv a ha j hj).1
    exact D.zero _ _ he.le
  · simp

omit [MeasurableSpace S] in
theorem greedy_max_selected [Nonempty (Fin k)] (g : S → ℝ) (h : MarkovBanditHistory k S n)
    (hinv : ChargeInvariant (currentHistoryPrevailingCharge g n h) (fun i => g (h.2 i)))
    (a : Fin k) (ha : ∀ j, g (h.2 j) ≤ g (h.2 a)) :
    maxCharge g n h = currentHistoryPrevailingCharge g n h a := by
  apply le_antisymm
  · apply ciSup_le
    intro j
    by_cases hj : j = a
    · subst j; exact le_rfl
    · exact (greedy_idle _ _ (prevailing_le_current g h) hinv a ha j hj).2
  · exact le_ciSup (Set.finite_range _).bddAbove a

theorem greedy_arm_identity [Nonempty (Fin k)] {P : Kernel S S} [IsMarkovKernel P]
    {r : S → ℝ} {beta : ℝ} {g : S → ℝ} {U : ℝ → S → ℝ} {M B : ℝ}
    (D : ChargeCertificate P r beta g U M B) (h : MarkovBanditHistory k S n)
    (hinv : ChargeInvariant (currentHistoryPrevailingCharge g n h) (fun i => g (h.2 i)))
    (a : Fin k) (ha : ∀ j, g (h.2 j) ≤ g (h.2 a)) :
    r (h.2 a) - maxCharge g n h = totalChargePotential U g n h -
      beta * armStepValue P (totalChargePotential U g (n+1)) a h := by
  have hp := greedy_potential_arm D h hinv a ha
  have hm := greedy_max_selected g h hinv a ha
  have he : armStepValue P (totalChargePotential U g (n+1)) a h =
      ∫ y, U (currentHistoryPrevailingCharge g n h a) y ∂P (h.2 a) := by
    apply integral_congr_ae
    filter_upwards [] with y
    rw [potential_snoc D, hp]
    ring
  have hc := D.continuation (currentHistoryPrevailingCharge g n h a) (h.2 a)
    (prevailing_le_current g h a)
  rw [he, hp, hm]
  linarith

theorem greedy_step_identity [Nonempty (Fin k)] {P : Kernel S S} [IsMarkovKernel P]
    {r : S → ℝ} {beta : ℝ} {g : S → ℝ} {U : ℝ → S → ℝ} {M B : ℝ}
    (D : ChargeCertificate P r beta g U M B) (hr : Measurable r)
    (R : ℝ) (hR : ∀ y, |r y| ≤ R) (pi : MarkovBanditPolicy k S)
    (h : MarkovBanditHistory k S n)
    (hinv : ChargeInvariant (currentHistoryPrevailingCharge g n h) (fun i => g (h.2 i)))
    (hsel : (pi.select n) h {a | ∀ j, g (h.2 j) ≤ g (h.2 a)} = 1) :
    stepValue P pi (instantReward r n) h - maxCharge g n h =
      totalChargePotential U g n h - beta * stepValue P pi (totalChargePotential U g (n+1)) h := by
  have hb (z : MarkovBanditHistory k S (n+1)) : |totalChargePotential U g (n+1) z| ≤ k*B := by
    rw [abs_of_nonneg (potential_bounds D z).1]
    exact (potential_bounds D z).2
  have he (a : Fin k) : ((pi.select n) h {a}).toReal * (r (h.2 a) - maxCharge g n h) =
      ((pi.select n) h {a}).toReal * (totalChargePotential U g n h -
        beta * armStepValue P (totalChargePotential U g (n+1)) a h) := by
    by_cases hp : ((pi.select n) h {a}).toReal = 0
    · simp [hp]
    · rw [greedy_arm_identity D h hinv a
        (positive_selection_mem pi n h _ hsel a (lt_of_le_of_ne ENNReal.toReal_nonneg (Ne.symm hp)))]
  have hs := congrArg (fun f : Fin k → ℝ => ∑ a, f a) (funext he)
  simp only [Finset.sum_sub_distrib, mul_sub, ← Finset.sum_mul] at hs
  rw [selection_mass pi n h] at hs
  rw [reward_step_sum P pi r hr R hR h,
    stepValue_sum P pi _ (potential_measurable D) (k*B) hb h]
  change _ = _ - beta * ∑ a : Fin k, ((pi.select n) h {a}).toReal *
    armStepValue P (totalChargePotential U g (n+1)) a h
  have hm : (∑ a : Fin k, ((pi.select n) h {a}).toReal * (beta * armStepValue P (totalChargePotential U g (n+1)) a h)) =
      beta * ∑ a : Fin k, ((pi.select n) h {a}).toReal * armStepValue P (totalChargePotential U g (n+1)) a h := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro a _
    ring
  rw [hm] at hs
  simpa using hs

end GittinsProof
-- END GittinsProof.GreedyAccounting

-- BEGIN GittinsProof.ArrayInitial
open MeasureTheory ProbabilityTheory BanditAlgorithm
namespace GittinsProof
variable {k : ℕ} {S : Type*} [MeasurableSpace S]

theorem pi_dirac_eq (x : Fin k → S) : Measure.pi (fun i => Measure.dirac (x i)) = Measure.dirac x := by
  apply Measure.pi_eq
  intro s hs
  by_cases h : ∀ i, x i ∈ s i
  · have hx : x ∈ Set.univ.pi s := by simpa only [Set.mem_pi, Set.mem_univ, forall_const] using h
    rw [Measure.dirac_apply_of_mem hx]
    symm
    exact Finset.prod_eq_one (fun i _ => Measure.dirac_apply_of_mem (h i))
  · have hx : x ∉ Set.univ.pi s := by simpa only [Set.mem_pi, Set.mem_univ, forall_const] using h
    rw [Measure.dirac_apply' x (MeasurableSet.univ_pi hs), Set.indicator_of_notMem hx]
    push Not at h
    obtain ⟨i, hi⟩ := h
    symm
    apply Finset.prod_eq_zero (Finset.mem_univ i)
    simp [Measure.dirac_apply' (x i) (hs i), hi]

theorem array_initial_map (P : Kernel S S) [IsMarkovKernel P] (x : Fin k → S) :
    (Measure.pi (fun i => markovChainMeasure P (x i))).map (fun w i => w i 0) = Measure.dirac x := by
  have : ∀ i : Fin k, IsProbabilityMeasure ((markovChainMeasure P (x i)).map (fun w => w 0)) := by
    intro i
    exact Measure.isProbabilityMeasure_map (measurable_pi_apply 0).aemeasurable
  rw [Measure.pi_map_pi (fun _ => (measurable_pi_apply 0).aemeasurable)]
  simp_rw [chain_initial_map]
  exact pi_dirac_eq x

theorem integral_array_initial (P : Kernel S S) [IsMarkovKernel P] (x : Fin k → S)
    (F : (Fin k → S) → ℝ) (hF : Measurable F) :
    (∫ w, F (fun i => w i 0) ∂Measure.pi (fun i => markovChainMeasure P (x i))) = F x := by
  have hm : Measurable (fun w : Fin k → ℕ → S => fun i => w i 0) :=
    measurable_pi_lambda _ (fun i => (measurable_pi_apply 0).comp (measurable_pi_apply i))
  rw [← integral_map hm.aemeasurable hF.aestronglyMeasurable, array_initial_map]
  exact integral_dirac' _ _ hF.stronglyMeasurable

end GittinsProof
-- END GittinsProof.ArrayInitial

-- BEGIN GittinsProof.PathMarginal
open MeasureTheory ProbabilityTheory BanditAlgorithm
namespace GittinsProof
variable {k N : ℕ} {S : Type*} [MeasurableSpace S]

theorem path_marginal_succ (P : Kernel S S) [IsMarkovKernel P]
    (pi : MarkovBanditPolicy (k+1) S) (x : Fin (k+1) → S)
    (F : MarkovBanditHistory (k+1) S (N+1) → ℝ) (hF : Measurable F)
    (C : ℝ) (hC : ∀ h, |F h| ≤ C) :
    (∑ a : Fin (N+1) → Fin (k+1), ∫ w, pathWeight pi a w * F (pathHistory a w (N+1) le_rfl)
      ∂Measure.pi (fun i => markovChainMeasure P (x i))) =
    ∑ a : Fin N → Fin (k+1), ∫ w, pathWeight pi a w * stepValue P pi F (pathHistory a w N le_rfl)
      ∂Measure.pi (fun i => markovChainMeasure P (x i)) := by
  rw [← Equiv.sum_comp (Fin.snocEquiv (fun _ : Fin (N+1) => Fin (k+1))), Fintype.sum_prod_type]
  change (∑ b : Fin (k+1), ∑ a : Fin N → Fin (k+1), ∫ w,
    pathWeight pi (Fin.snoc a b) w * F (pathHistory (Fin.snoc a b) w (N+1) le_rfl) ∂_) = _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  simp_rw [word_step_integral P pi x a _ F hF C hC]
  let G : Fin (k+1) → (Fin (k+1) → ℕ → S) → ℝ := fun b w =>
    pathWeight pi a w * ((pi.select N) (pathHistory a w N le_rfl) {b}).toReal *
      armStepValue P F b (pathHistory a w N le_rfl)
  have hG (b : Fin (k+1)) : Integrable (G b) (Measure.pi (fun i => markovChainMeasure P (x i))) := by
    have hh := measurable_pathHistory (S := S) a N le_rfl
    have hs := (((pi.select N).measurable_coe (measurableSet_singleton b)).comp hh).ennreal_toReal
    apply bounded_integrable _ _ ((measurable_pathWeight pi a).mul hs |>.mul
      ((measurable_armStepValue P F hF b).comp hh)) C
    intro w
    exact weighted_abs_bound (pathWeight_bounds pi a w) (selection_bounds pi _ b)
      (armStepValue_bound P F C hC b _)
  change (∑ b : Fin (k+1), ∫ w, G b w ∂_) = _
  rw [← integral_finsetSum _ (fun b _ => hG b)]
  apply integral_congr_ae
  filter_upwards [] with w
  rw [stepValue_sum P pi F hF C hC]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro b _
  change _ * _ * _ = _ * (_ * _)
  simp only [armStepValue]
  ring

theorem path_marginal (P : Kernel S S) [IsMarkovKernel P]
    (pi : MarkovBanditPolicy (k+1) S) (x : Fin (k+1) → S)
    (F : MarkovBanditHistory (k+1) S N → ℝ) (hF : Measurable F)
    (C : ℝ) (hC : ∀ h, |F h| ≤ C) :
    (∑ a : Fin N → Fin (k+1), ∫ w, pathWeight pi a w * F (pathHistory a w N le_rfl)
      ∂Measure.pi (fun i => markovChainMeasure P (x i))) =
      ∫ h, F h ∂markovBanditMeasure P pi x N := by
  induction N with
  | zero =>
    have hm : Measurable (fun y : Fin (k+1) → S => F (Fin.elim0,y)) :=
      hF.comp (measurable_const.prodMk measurable_id)
    have he (a : Fin 0 → Fin (k+1)) (w : Fin (k+1) → ℕ → S) :
        pathHistory a w 0 le_rfl = (Fin.elim0, fun i => w i 0) := by
      apply Prod.ext
      · funext i; exact Fin.elim0 i
      · change arrayState a (pathArray 0 w) 0 = _
        exact arrayState_zero (default : Fin 0 → Fin (k+1)) (pathArray 0 w)
    simp only [pathWeight, wordWeight, Finset.univ_eq_empty, Finset.prod_empty, one_mul,
      Fintype.sum_unique]
    rw [markovBanditMeasure, integral_dirac' _ _ hF.stronglyMeasurable]
    trans ∫ w, F (Fin.elim0, fun i => w i 0) ∂Measure.pi (fun i => markovChainMeasure P (x i))
    · apply integral_congr_ae
      filter_upwards [] with w
      exact congrArg F (he _ w)
    · exact integral_array_initial P x _ hm

  | succ N ih =>
    rw [path_marginal_succ P pi x F hF C hC]
    rw [ih (stepValue P pi F) (measurable_stepValue P pi F hF) (stepValue_bound P pi F C hC)]
    exact (history_integral_succ P pi x F hF C hC).symm

end GittinsProof
-- END GittinsProof.PathMarginal

-- BEGIN GittinsProof.FiniteMarginal
open MeasureTheory ProbabilityTheory BanditAlgorithm
namespace GittinsProof
variable {k N : ℕ} {S : Type*} [MeasurableSpace S]

theorem pathArray_map (P : Kernel S S) [IsMarkovKernel P] (x : Fin k → S) :
    (Measure.pi (fun i => markovChainMeasure P (x i))).map (pathArray N) = arrayLaw (N := N) P x := by
  have : ∀ i : Fin k, IsProbabilityMeasure ((markovChainMeasure P (x i)).map
      (fun w (j : Fin (N+1)) => w j.val)) := by
    intro i
    exact Measure.isProbabilityMeasure_map
      ((measurable_pi_lambda _ (fun j : Fin (N+1) => measurable_pi_apply j.val)).aemeasurable)
  exact Measure.pi_map_pi (fun _ =>
    (measurable_pi_lambda _ (fun j : Fin (N+1) => measurable_pi_apply j.val)).aemeasurable)

theorem finite_marginal (P : Kernel S S) [IsMarkovKernel P]
    (pi : MarkovBanditPolicy k S) (x : Fin k → S)
    (F : MarkovBanditHistory k S N → ℝ) (hF : Measurable F)
    (C : ℝ) (hC : ∀ h, |F h| ≤ C) :
    (∑ a : Fin N → Fin k, ∫ w, wordWeight pi a w * F (replayHistory a w N le_rfl)
      ∂arrayLaw (N := N) P x) = ∫ h, F h ∂markovBanditMeasure P pi x N := by
  cases k with
  | zero =>
    have hh := selection_mass pi 0 (Fin.elim0,x)
    simp at hh
  | succ k =>
    rw [← path_marginal P pi x F hF C hC]
    apply Finset.sum_congr rfl
    intro a _
    rw [← pathArray_map]
    exact integral_map measurable_pathArray.aemeasurable
      ((measurable_wordWeight pi a).mul (hF.comp (measurable_replayHistory a N le_rfl))).aestronglyMeasurable

end GittinsProof
-- END GittinsProof.FiniteMarginal

-- BEGIN GittinsProof.ExpectedComparison
open MeasureTheory ProbabilityTheory BanditAlgorithm
namespace GittinsProof
variable {k N : ℕ} {S : Type*} [MeasurableSpace S]

theorem weighted_history_integrable (P : Kernel S S) [IsMarkovKernel P]
    (pi : MarkovBanditPolicy k S) (x : Fin k → S) (a : Fin N → Fin k)
    (F : MarkovBanditHistory k S N → ℝ) (hF : Measurable F)
    (C : ℝ) (hC : ∀ h, |F h| ≤ C) :
    Integrable (fun w => pathWeight pi a w * F (pathHistory a w N le_rfl))
      (Measure.pi (fun i => markovChainMeasure P (x i))) := by
  apply bounded_integrable _ _ ((measurable_pathWeight pi a).mul
    (hF.comp (measurable_pathHistory a N le_rfl))) C
  intro w
  change |pathWeight pi a w * F (pathHistory a w N le_rfl)| ≤ C
  rw [abs_mul, abs_of_nonneg (pathWeight_bounds pi a w).1]
  exact (mul_le_of_le_one_left (abs_nonneg _) (pathWeight_bounds pi a w).2).trans (hC _)

theorem expected_max_comparison (P : Kernel S S) [IsMarkovKernel P]
    (r : S → ℝ) (beta : ℝ) (pistar pi : MarkovBanditPolicy (k+1) S)
    (hpi : IsGittinsIndexPolicy P r beta pistar) (x : Fin (k+1) → S)
    (hg : Measurable (gittinsIndex P r beta))
    (M : ℝ) (hM : ∀ y, 0 ≤ gittinsIndex P r beta y ∧ gittinsIndex P r beta y ≤ M) :
    (∫ h, maxCharge (gittinsIndex P r beta) N h ∂markovBanditMeasure P pistar x N) ≤
      ∫ h, maxCharge (gittinsIndex P r beta) N h ∂markovBanditMeasure P pi x N := by
  let F := maxCharge (k := k+1) (gittinsIndex P r beta) N
  have hF : Measurable F := measurable_maxCharge _ hg N
  have hb (h : MarkovBanditHistory (k+1) S N) : |F h| ≤ M := by
    rw [abs_of_nonneg (maxCharge_bounds _ M hM h).1]
    exact (maxCharge_bounds _ M hM h).2
  change (∫ h, F h ∂_) ≤ ∫ h, F h ∂_
  rw [← path_marginal P pistar x F hF M hb, ← path_marginal P pi x F hF M hb]
  rw [← integral_finsetSum _ (fun a _ => weighted_history_integrable P pistar x a F hF M hb),
      ← integral_finsetSum _ (fun a _ => weighted_history_integrable P pi x a F hF M hb)]
  apply integral_mono
  · exact integrable_finsetSum _ (fun a _ => weighted_history_integrable P pistar x a F hF M hb)
  · exact integrable_finsetSum _ (fun a _ => weighted_history_integrable P pi x a F hF M hb)
  · intro w
    exact weighted_max_comparison P r beta pistar pi hpi w

end GittinsProof
-- END GittinsProof.ExpectedComparison

-- BEGIN GittinsProof.ReachableIntegral
open MeasureTheory ProbabilityTheory BanditAlgorithm
namespace GittinsProof
variable {k N : ℕ} {S : Type*} [MeasurableSpace S]

theorem history_integral_eq_of_positive_paths (P : Kernel S S) [IsMarkovKernel P]
    (pi : MarkovBanditPolicy (k+1) S) (x : Fin (k+1) → S)
    (F G : MarkovBanditHistory (k+1) S N → ℝ) (hF : Measurable F) (hG : Measurable G)
    (C D : ℝ) (hC : ∀ h, |F h| ≤ C) (hD : ∀ h, |G h| ≤ D)
    (he : ∀ a : Fin N → Fin (k+1), ∀ w : Fin (k+1) → ℕ → S,
      0 < pathWeight pi a w → F (pathHistory a w N le_rfl) = G (pathHistory a w N le_rfl)) :
    (∫ h, F h ∂markovBanditMeasure P pi x N) = ∫ h, G h ∂markovBanditMeasure P pi x N := by
  rw [← path_marginal P pi x F hF C hC, ← path_marginal P pi x G hG D hD]
  apply Finset.sum_congr rfl
  intro a _
  apply integral_congr_ae
  filter_upwards [] with w
  by_cases hw : pathWeight pi a w = 0
  · simp [hw]
  · rw [he a w (lt_of_le_of_ne (pathWeight_bounds pi a w).1 (Ne.symm hw))]

end GittinsProof
-- END GittinsProof.ReachableIntegral

-- BEGIN GittinsProof.DiscountedAlgebra
namespace GittinsProof

theorem discounted_summable {beta C : ℝ} (hb : 0 ≤ beta) (hb1 : beta < 1)
    (f : ℕ → ℝ) (hf : ∀ n, |f n| ≤ C) : Summable (fun n => beta^n * f n) := by
  apply ((summable_geometric_of_abs_lt_one (by rwa [abs_of_nonneg hb])).mul_left C).of_norm_bounded
  intro n
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (pow_nonneg hb n)]
  nlinarith [pow_nonneg hb n, hf n]

theorem discounted_telescoping {beta A B E : ℝ} (hb : 0 ≤ beta) (hb1 : beta < 1)
    (a b e : ℕ → ℝ) (ha : ∀ n, |a n| ≤ A) (hbb : ∀ n, |b n| ≤ B)
    (he : ∀ n, |e n| ≤ E) (h0 : e 0 = 0)
    (hstep : ∀ n, a n - b n = e n - beta * e (n+1)) :
    (∑' n, beta^n * a n) = ∑' n, beta^n * b n := by
  have hsa := discounted_summable hb hb1 a ha
  have hsb := discounted_summable hb hb1 b hbb
  have hse := discounted_summable hb hb1 e he
  have hshift : Summable (fun n => beta^(n+1) * e (n+1)) := (summable_nat_add_iff 1).mpr hse
  have hrel : (∑' n, (beta^n*a n - beta^n*b n)) =
      ∑' n, (beta^n*e n - beta^(n+1)*e (n+1)) := by
    apply tsum_congr
    intro n
    calc
      _ = beta^n * (a n - b n) := by ring
      _ = beta^n * (e n - beta * e (n+1)) := by rw [hstep n]
      _ = _ := by rw [pow_succ]; ring
  rw [hsa.tsum_sub hsb, hse.tsum_sub hshift] at hrel
  have hz := hse.tsum_eq_zero_add
  simp only [pow_zero, one_mul, h0, zero_add] at hz
  rw [hz] at hrel
  linarith

end GittinsProof
-- END GittinsProof.DiscountedAlgebra

-- BEGIN GittinsProof.GreedyValue
open MeasureTheory ProbabilityTheory BanditAlgorithm
namespace GittinsProof
variable {k : ℕ} {S : Type*} [MeasurableSpace S]

noncomputable def meanCharge (P : Kernel S S) [IsMarkovKernel P]
    (pi : MarkovBanditPolicy k S) (x : Fin k → S) (g : S → ℝ) (n : ℕ) : ℝ :=
  ∫ h, maxCharge g n h ∂markovBanditMeasure P pi x n

noncomputable def meanPotential (P : Kernel S S) [IsMarkovKernel P]
    (pi : MarkovBanditPolicy k S) (x : Fin k → S) (U : ℝ → S → ℝ) (g : S → ℝ) (n : ℕ) : ℝ :=
  ∫ h, totalChargePotential U g n h ∂markovBanditMeasure P pi x n

theorem greedy_round_identity {P : Kernel S S} [IsMarkovKernel P] {r : S → ℝ} {beta : ℝ}
    {U : ℝ → S → ℝ} {M B : ℝ}
    (D : ChargeCertificate P r beta (gittinsIndex P r beta) U M B)
    (hr : Measurable r) (R : ℝ) (hR : ∀ y, |r y| ≤ R)
    (pi : MarkovBanditPolicy (k+1) S) (hpi : IsGittinsIndexPolicy P r beta pi)
    (x : Fin (k+1) → S) (n : ℕ) :
    markovBanditRoundReward P r pi x n - meanCharge P pi x (gittinsIndex P r beta) n =
      meanPotential P pi x U (gittinsIndex P r beta) n -
        beta * meanPotential P pi x U (gittinsIndex P r beta) (n+1) := by
  let g := gittinsIndex P r beta
  let K : ℝ := ((k+1 : ℕ) : ℝ)*B
  have hmax (h : MarkovBanditHistory (k+1) S n) : |maxCharge g n h| ≤ M := by
    rw [abs_of_nonneg (maxCharge_bounds g M D.g_bounds h).1]
    exact (maxCharge_bounds g M D.g_bounds h).2
  have hpot (m : ℕ) (h : MarkovBanditHistory (k+1) S m) : |totalChargePotential U g m h| ≤ K := by
    rw [abs_of_nonneg (potential_bounds D h).1]
    exact (potential_bounds D h).2
  have hsr := measurable_stepValue P pi (instantReward r n) (measurable_instantReward r hr)
  have hsp := measurable_stepValue P pi (totalChargePotential U g (n+1)) (potential_measurable D)
  have hbr (h : MarkovBanditHistory (k+1) S n) : |stepValue P pi (instantReward r n) h| ≤ R :=
    stepValue_bound P pi _ R (fun _ => hR _) h
  have hbp (h : MarkovBanditHistory (k+1) S n) : |stepValue P pi (totalChargePotential U g (n+1)) h| ≤ K :=
    stepValue_bound P pi _ K (hpot (n+1)) h
  have he := history_integral_eq_of_positive_paths P pi x
    (fun h => stepValue P pi (instantReward r n) h - maxCharge g n h)
    (fun h => totalChargePotential U g n h - beta * stepValue P pi (totalChargePotential U g (n+1)) h)
    (hsr.sub (measurable_maxCharge g D.g_measurable n))
    ((potential_measurable D).sub (measurable_const.mul hsp)) (R+M) (K + |beta| * K)
    (fun h => (abs_sub _ _).trans (add_le_add (hbr h) (hmax h)))
    (fun h => (abs_sub _ _).trans (add_le_add (hpot n h) (by
      rw [abs_mul]; exact mul_le_mul_of_nonneg_left (hbp h) (abs_nonneg beta)))) ?_
  · have hir := bounded_integrable (markovBanditMeasure P pi x n) _ hsr R hbr
    have him := bounded_integrable (markovBanditMeasure P pi x n) _ (measurable_maxCharge g D.g_measurable n) M hmax
    have hip := bounded_integrable (markovBanditMeasure P pi x n) _ (potential_measurable D) K (hpot n)
    have his := bounded_integrable (markovBanditMeasure P pi x n) _ hsp K hbp
    rw [integral_sub hir him, integral_sub hip (his.const_mul beta), integral_const_mul] at he
    rw [← round_reward_step P pi x r hr R hR] at he
    have hsnext : (∫ h, stepValue P pi (totalChargePotential U g (n+1)) h ∂markovBanditMeasure P pi x n) =
        ∫ h, totalChargePotential U g (n+1) h ∂markovBanditMeasure P pi x (n+1) :=
      (history_integral_succ P pi x (totalChargePotential U g (n+1)) (potential_measurable D) K (hpot (n+1))).symm
    rw [hsnext] at he
    exact he
  · intro a w hw
    apply greedy_step_identity D hr R hR pi _
    · exact path_charge_invariant g a w n le_rfl (fun s hs =>
        pathWeight_pos_max P r beta pi hpi a w hw ⟨s,hs⟩)
    · exact hpi n _

theorem greedy_value_eq_charge {P : Kernel S S} [IsMarkovKernel P] {r : S → ℝ} {beta : ℝ}
    {U : ℝ → S → ℝ} {M B : ℝ}
    (D : ChargeCertificate P r beta (gittinsIndex P r beta) U M B)
    (hr : Measurable r) (R : ℝ) (hR : ∀ y, |r y| ≤ R) (hb : 0 ≤ beta) (hb1 : beta < 1)
    (pi : MarkovBanditPolicy (k+1) S) (hpi : IsGittinsIndexPolicy P r beta pi) (x : Fin (k+1) → S) :
    markovBanditDiscountedValue P r beta pi x =
      ∑' n, beta^n * meanCharge P pi x (gittinsIndex P r beta) n := by
  apply discounted_telescoping hb hb1 _ _ (meanPotential P pi x U (gittinsIndex P r beta))
    (A := R) (B := M) (E := ((k+1 : ℕ) : ℝ)*B)
  · exact fun n => round_reward_bound P pi x r R hR
  · intro n
    apply abs_integral_le_bound
    intro h
    rw [abs_of_nonneg (maxCharge_bounds _ M D.g_bounds h).1]
    exact (maxCharge_bounds _ M D.g_bounds h).2
  · intro n
    apply abs_integral_le_bound
    intro h
    rw [abs_of_nonneg (potential_bounds D h).1]
    exact (potential_bounds D h).2
  · unfold meanPotential
    rw [markovBanditMeasure, integral_dirac' _ _ (potential_measurable D).stronglyMeasurable]
    exact potential_initial D x
  · exact greedy_round_identity D hr R hR pi hpi x

end GittinsProof
-- END GittinsProof.GreedyValue

-- BEGIN GittinsProof.DiscountedComparison
open MeasureTheory ProbabilityTheory BanditAlgorithm
namespace GittinsProof
variable {k : ℕ} {S : Type*} [MeasurableSpace S]

theorem meanCharge_bound [Nonempty (Fin k)] (P : Kernel S S) [IsMarkovKernel P]
    (pi : MarkovBanditPolicy k S) (x : Fin k → S) (g : S → ℝ) (M : ℝ)
    (hg : ∀ y, 0 ≤ g y ∧ g y ≤ M) (n : ℕ) : |meanCharge P pi x g n| ≤ M := by
  apply abs_integral_le_bound
  intro h
  rw [abs_of_nonneg (maxCharge_bounds g M hg h).1]
  exact (maxCharge_bounds g M hg h).2

theorem discounted_charge_comparison (P : Kernel S S) [IsMarkovKernel P]
    (r : S → ℝ) (beta : ℝ) (pistar pi : MarkovBanditPolicy (k+1) S)
    (hpi : IsGittinsIndexPolicy P r beta pistar) (x : Fin (k+1) → S)
    (hg : Measurable (gittinsIndex P r beta)) (M : ℝ)
    (hM : ∀ y, 0 ≤ gittinsIndex P r beta y ∧ gittinsIndex P r beta y ≤ M)
    (hb : 0 ≤ beta) (hb1 : beta < 1) :
    (∑' n, beta^n * meanCharge P pistar x (gittinsIndex P r beta) n) ≤
      ∑' n, beta^n * meanCharge P pi x (gittinsIndex P r beta) n := by
  apply Summable.tsum_le_tsum
  · intro n
    exact mul_le_mul_of_nonneg_left (expected_max_comparison P r beta pistar pi hpi x hg M hM)
      (pow_nonneg hb n)
  · exact discounted_summable hb hb1 _ (meanCharge_bound P pistar x _ M hM)
  · exact discounted_summable hb hb1 _ (meanCharge_bound P pi x _ M hM)

end GittinsProof
-- END GittinsProof.DiscountedComparison

-- BEGIN GittinsProof.WeberScaling
open MeasureTheory ProbabilityTheory BanditAlgorithm WeberGittins.Suboptimality
namespace GittinsProof
variable {k : ℕ} {S : Type*} [MeasurableSpace S]

omit [MeasurableSpace S] in
theorem prevailing_div (g : S → ℝ) {d : ℝ} (hd : 0 ≤ d) (n : ℕ)
    (h : MarkovBanditHistory k S n) (i : Fin k) :
    currentHistoryPrevailingCharge (fun y => g y/d) n h i = currentHistoryPrevailingCharge g n h i / d := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [currentHistoryPrevailingCharge]
    rw [ih, min_div_div_right hd]

omit [MeasurableSpace S] in
theorem maxCharge_div [Nonempty (Fin k)] (g : S → ℝ) {d : ℝ} (hd : 0 < d) (n : ℕ)
    (h : MarkovBanditHistory k S n) :
    maxCharge (fun y => g y/d) n h = maxCharge g n h / d := by
  unfold maxCharge
  simp only [prevailing_div g hd.le]
  apply le_antisymm
  · apply ciSup_le
    intro i
    exact div_le_div_of_nonneg_right (le_ciSup (Set.finite_range _).bddAbove i) hd.le
  · apply (div_le_iff₀ hd).mpr
    apply ciSup_le
    intro i
    exact (div_le_iff₀ hd).mp (le_ciSup (Set.finite_range (fun j : Fin k => currentHistoryPrevailingCharge g n h j / d)).bddAbove i)

theorem weber_prevailing (P : Kernel S S) [IsMarkovKernel P] (r : S → ℝ)
    {β : ℝ} (hβ1 : β < 1) (n : ℕ) (h : MarkovBanditHistory k S n) (i : Fin k) :
    currentHistoryPrevailingCharge (weberIndex P r β) n h i =
      currentHistoryPrevailingCharge (gittinsIndex P r β) n h i / (1-β) :=
  prevailing_div _ (sub_pos.mpr hβ1).le n h i

theorem weber_maxCharge [Nonempty (Fin k)] (P : Kernel S S) [IsMarkovKernel P] (r : S → ℝ)
    {β : ℝ} (hβ1 : β < 1) (n : ℕ) (h : MarkovBanditHistory k S n) :
    maxCharge (weberIndex P r β) n h = maxCharge (gittinsIndex P r β) n h / (1-β) :=
  maxCharge_div _ (sub_pos.mpr hβ1) n h
end GittinsProof
-- END GittinsProof.WeberScaling

-- BEGIN GittinsProof.WeberNormalization
open MeasureTheory ProbabilityTheory BanditAlgorithm WeberGittins.Suboptimality
namespace GittinsProof
variable {k : ℕ} {S : Type*} [MeasurableSpace S]

theorem weber_round_normalization [Nonempty (Fin k)] (P : Kernel S S) [IsMarkovKernel P]
    (pi : MarkovBanditPolicy k S) (x : Fin k → S) {r : S → ℝ} (hrm : Measurable r)
    {β C : ℝ} (hβ : 0 ≤ β) (hβ1 : β < 1) (hC : 0 ≤ C)
    (hr : ∀ y, 0 ≤ r y ∧ r y ≤ C) (n : ℕ) :
    (1-β) * roundExpectation P pi x n (fun h j =>
      (⨆ i : Fin k, currentHistoryPrevailingCharge (weberIndex P r β) n h i) - r (h.2 j)/(1-β)) =
      meanCharge P pi x (gittinsIndex P r β) n - markovBanditRoundReward P r pi x n := by
  let g := gittinsIndex P r β
  have hg : Measurable g := index_measurable P hrm hβ hβ1 hC hr
  have hgb : ∀ y, 0 ≤ g y ∧ g y ≤ C := fun y => index_bounds P y hrm hβ hβ1 hC hr
  have hmax (h : MarkovBanditHistory k S n) : |maxCharge g n h| ≤ C := by
    rw [abs_of_nonneg (maxCharge_bounds g C hgb h).1]
    exact (maxCharge_bounds g C hgb h).2
  have hm := (measurable_maxCharge (k := k) g hg n).comp (measurable_truncateHistory (k := k) (n := n))
  have hi := bounded_integrable (markovBanditMeasure P pi x (n+1)) _ hm C (fun h => hmax _)
  change Integrable (fun h => maxCharge g n (truncateMarkovBanditHistory h)) (markovBanditMeasure P pi x (n+1)) at hi
  have hrb : ∀ y, |r y| ≤ C := fun y => by rw [abs_of_nonneg (hr y).1]; exact (hr y).2
  have hri := bounded_integrable (markovBanditMeasure P pi x (n+1)) (instantReward r n)
    (measurable_instantReward r hrm) C (fun h => hrb _)
  have he : roundExpectation P pi x n (fun h j =>
      (⨆ i : Fin k, currentHistoryPrevailingCharge (weberIndex P r β) n h i) - r (h.2 j)/(1-β)) =
      (meanCharge P pi x g n - markovBanditRoundReward P r pi x n)/(1-β) := by
    unfold roundExpectation
    trans ∫ h, (maxCharge g n (truncateMarkovBanditHistory h) - instantReward r n h)/(1-β)
      ∂markovBanditMeasure P pi x (n+1)
    · apply integral_congr_ae
      filter_upwards [] with h
      change maxCharge (weberIndex P r β) n (truncateMarkovBanditHistory h) - _ = _
      rw [weber_maxCharge P r hβ1]
      exact (sub_div _ _ _).symm
    · rw [integral_div, integral_sub hi hri,
        history_forget_integral P pi x _ (measurable_maxCharge g hg n) C hmax]
      rfl
  rw [he]
  dsimp [g]
  field_simp [ne_of_gt (sub_pos.mpr hβ1)]

theorem weber_rhs_normalization [Nonempty (Fin k)] (P : Kernel S S) [IsMarkovKernel P]
    (pi : MarkovBanditPolicy k S) (x : Fin k → S) {r : S → ℝ} (hrm : Measurable r)
    {β C : ℝ} (hβ : 0 ≤ β) (hβ1 : β < 1) (hC : 0 ≤ C)
    (hr : ∀ y, 0 ≤ r y ∧ r y ≤ C) :
    (1-β) * (∑' n, β^n * roundExpectation P pi x n (fun h j =>
      (⨆ i : Fin k, currentHistoryPrevailingCharge (weberIndex P r β) n h i) - r (h.2 j)/(1-β))) =
      (∑' n, β^n * meanCharge P pi x (gittinsIndex P r β) n) -
        markovBanditDiscountedValue P r β pi x := by
  have hrb : ∀ y, |r y| ≤ C := fun y => by rw [abs_of_nonneg (hr y).1]; exact (hr y).2
  have hmean : ∀ n, |meanCharge P pi x (gittinsIndex P r β) n| ≤ C := by
    intro n
    apply abs_integral_le_bound
    intro h
    have hb := maxCharge_bounds (gittinsIndex P r β) C (fun y => index_bounds P y hrm hβ hβ1 hC hr) h
    rw [abs_of_nonneg hb.1]
    exact hb.2
  have hs1 := discounted_summable hβ hβ1 _ hmean
  have hs2 := discounted_summable hβ hβ1 _ (fun n => round_reward_bound (n := n) P pi x r C hrb)
  rw [← tsum_mul_left]
  trans ∑' n, (β^n * meanCharge P pi x (gittinsIndex P r β) n - β^n * markovBanditRoundReward P r pi x n)
  · apply tsum_congr
    intro n
    have he := weber_round_normalization P pi x hrm hβ hβ1 hC hr n
    linear_combination β^n * he
  · exact hs1.tsum_sub hs2
end GittinsProof
-- END GittinsProof.WeberNormalization

-- BEGIN GittinsProof.Root
open MeasureTheory ProbabilityTheory BanditAlgorithm WeberGittins.Suboptimality
namespace GittinsProof

theorem full_solution {k : ℕ} {S : Type*}
    [MeasurableSpace S] [StandardBorelSpace S] (P : Kernel S S) [IsMarkovKernel P]
    {r : S → ℝ} (hr : Measurable r) (hrb : RewardsNonnegBounded r)
    {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1)
    (πstar : MarkovBanditPolicy k S) (hπstar : IsGittinsIndexPolicy P r β πstar)
    (π : MarkovBanditPolicy k S) (x : Fin k → S) :
    markovBanditDiscountedValue P r β πstar x - markovBanditDiscountedValue P r β π x ≤
      (1 - β) * ∑' t : ℕ, β ^ t * roundExpectation P π x t (fun h j =>
        (⨆ i : Fin k, currentHistoryPrevailingCharge (weberIndex P r β) t h i) -
          r (h.2 j) / (1 - β)) := by
  cases k with
  | zero =>
    have hh := selection_mass π 0 (Fin.elim0,x)
    simp at hh
  | succ k =>
    obtain ⟨hr0,C,hrC⟩ := hrb
    have hC : 0 ≤ C := (hr0 (x 0)).trans (hrC (x 0))
    have hrange (y : S) : 0 ≤ r y ∧ r y ≤ C := ⟨hr0 y,hrC y⟩
    have hab (y : S) : |r y| ≤ C := by rw [abs_of_nonneg (hr0 y)]; exact hrC y
    have D := native_charge_certificate P hr hβ0.le hβ1 hC hrange
    rw [weber_rhs_normalization P π x hr hβ0.le hβ1 hC hrange,
      greedy_value_eq_charge D hr C hab hβ0.le hβ1 πstar hπstar x]
    exact sub_le_sub_right (discounted_charge_comparison P r β πstar π hπstar x
      D.g_measurable C D.g_bounds hβ0.le hβ1) _

end GittinsProof
-- END GittinsProof.Root

open MeasureTheory ProbabilityTheory BanditAlgorithm WeberGittins.Suboptimality
theorem solution {k : ℕ} {S : Type*}
    [MeasurableSpace S] [StandardBorelSpace S] (P : Kernel S S) [IsMarkovKernel P]
    {r : S → ℝ} (hr : Measurable r) (hrb : RewardsNonnegBounded r)
    {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1)
    (πstar : MarkovBanditPolicy k S) (hπstar : IsGittinsIndexPolicy P r β πstar)
    (π : MarkovBanditPolicy k S) (x : Fin k → S) :
    markovBanditDiscountedValue P r β πstar x - markovBanditDiscountedValue P r β π x ≤
      (1 - β) * ∑' t : ℕ, β ^ t * roundExpectation P π x t (fun h j =>
        (⨆ i : Fin k, currentHistoryPrevailingCharge (weberIndex P r β) t h i) -
          r (h.2 j) / (1 - β)) := GittinsProof.full_solution P hr hrb hβ0 hβ1 πstar hπstar π x
namespace WeberGittins.Suboptimality
theorem theorem2_suboptimality_bound {k : ℕ} {S : Type*}
    [MeasurableSpace S] [StandardBorelSpace S] (P : Kernel S S) [IsMarkovKernel P]
    {r : S → ℝ} (hr : Measurable r) (hrb : RewardsNonnegBounded r)
    {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1)
    (πstar : MarkovBanditPolicy k S) (hπstar : IsGittinsIndexPolicy P r β πstar)
    (π : MarkovBanditPolicy k S) (x : Fin k → S) :
    markovBanditDiscountedValue P r β πstar x - markovBanditDiscountedValue P r β π x ≤
      (1 - β) * ∑' t : ℕ, β ^ t * roundExpectation P π x t (fun h j =>
        (⨆ i : Fin k, currentHistoryPrevailingCharge (weberIndex P r β) t h i) -
          r (h.2 j) / (1 - β)) := _root_.solution P hr hrb hβ0 hβ1 πstar hπstar π x
end WeberGittins.Suboptimality
