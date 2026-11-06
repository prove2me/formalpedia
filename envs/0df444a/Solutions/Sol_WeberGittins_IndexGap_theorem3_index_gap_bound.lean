-- Prove2me | solution 1 for WeberGittins.IndexGap.theorem3_index_gap_bound
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-06T05:13:43.437969+00:00
-- url     : https://prove2.me/submissions/15dbaece-17bf-4767-a99d-1b1e7f773981
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_WeberGittins_IndexGap_switch_to_gittins_after_t_optimal
import Theorems.Thm_WeberGittins_IndexGap_eq8_one_switch_gap_bound

open MeasureTheory ProbabilityTheory BanditAlgorithm

namespace WGThm3Aux

open Classical

variable {S : Type*} [MeasurableSpace S]

/-- Rewards in `[0, C]` force the fair charge into `[0, C]`. -/
lemma gittinsIndex_mem_Icc (P : Kernel S S) [IsMarkovKernel P] {r : S → ℝ} {C : ℝ}
    (hC : 0 ≤ C) (hr0 : ∀ y, 0 ≤ r y) (hrC : ∀ y, r y ≤ C) {β : ℝ} (hβ0 : 0 < β)
    (hβ1 : β < 1) (y : S) :
    0 ≤ gittinsIndex P r β y ∧ gittinsIndex P r β y ≤ C := by
  have key : ∀ g ∈ {g : ℝ | ∃ τ : (ℕ → S) → ℕ∞, IsTrajStoppingTime τ ∧ (∀ ω, 1 ≤ τ ω) ∧
      g = (∫ ω, discountedStoppedSum β r τ ω ∂markovChainMeasure P y) /
        (∫ ω, discountedStoppedSum β (fun _ ↦ 1) τ ω ∂markovChainMeasure P y)},
      0 ≤ g ∧ g ≤ C := by
    rintro g ⟨τ, -, -, rfl⟩
    set f := fun ω => discountedStoppedSum β r τ ω
    set g' := fun ω => discountedStoppedSum β (fun _ ↦ 1) τ ω
    have hsf : ∀ ω, Summable (fun t : ℕ => if (t : ℕ∞) < τ ω then β ^ t * r (ω t) else 0) := by
      intro ω
      refine Summable.of_nonneg_of_le (fun t => ?_) (fun t => ?_)
        ((summable_geometric_of_lt_one hβ0.le hβ1).mul_right C)
      · split_ifs
        · exact mul_nonneg (pow_nonneg hβ0.le _) (hr0 _)
        · exact le_rfl
      · split_ifs
        · exact mul_le_mul_of_nonneg_left (hrC _) (pow_nonneg hβ0.le _)
        · exact mul_nonneg (pow_nonneg hβ0.le _) hC
    have hsg : ∀ ω, Summable (fun t : ℕ => if (t : ℕ∞) < τ ω then β ^ t * (1 : ℝ) else 0) := by
      intro ω
      refine Summable.of_nonneg_of_le (fun t => ?_) (fun t => ?_)
        ((summable_geometric_of_lt_one hβ0.le hβ1).mul_right 1)
      · split_ifs
        · exact mul_nonneg (pow_nonneg hβ0.le _) zero_le_one
        · exact le_rfl
      · split_ifs
        · exact le_rfl
        · exact mul_nonneg (pow_nonneg hβ0.le _) zero_le_one
    have hf0 : ∀ ω, 0 ≤ f ω := fun ω => tsum_nonneg fun t => by
      split_ifs
      · exact mul_nonneg (pow_nonneg hβ0.le _) (hr0 _)
      · exact le_rfl
    have hg0 : ∀ ω, 0 ≤ g' ω := fun ω => tsum_nonneg fun t => by
      split_ifs
      · exact mul_nonneg (pow_nonneg hβ0.le _) zero_le_one
      · exact le_rfl
    have hfg : ∀ ω, f ω ≤ C * g' ω := by
      intro ω
      simp only [f, g', discountedStoppedSum]
      rw [← tsum_mul_left]
      refine Summable.tsum_le_tsum (fun t => ?_) (hsf ω) ((hsg ω).mul_left C)
      split_ifs
      · nlinarith [hrC (ω t), pow_nonneg hβ0.le t]
      · simp
    have hN : 0 ≤ ∫ ω, f ω ∂markovChainMeasure P y := integral_nonneg hf0
    have hD : 0 ≤ ∫ ω, g' ω ∂markovChainMeasure P y := integral_nonneg hg0
    refine ⟨div_nonneg hN hD, ?_⟩
    rcases hD.lt_or_eq with hDpos | hD0
    · rw [div_le_iff₀ hDpos]
      by_cases hfi : Integrable f (markovChainMeasure P y)
      · by_cases hgi : Integrable g' (markovChainMeasure P y)
        · calc ∫ ω, f ω ∂markovChainMeasure P y ≤ ∫ ω, C * g' ω ∂markovChainMeasure P y :=
                integral_mono hfi (hgi.const_mul C) hfg
            _ = C * ∫ ω, g' ω ∂markovChainMeasure P y := integral_const_mul C _
        · rw [integral_undef hgi] at hDpos
          exact absurd hDpos (lt_irrefl 0)
      · rw [integral_undef hfi]
        exact mul_nonneg hC hD
    · rw [← hD0, div_zero]
      exact hC
  constructor
  · exact Real.sSup_nonneg (fun g hg => (key g hg).1)
  · exact Real.sSup_le (fun g hg => (key g hg).2) hC

variable {k : ℕ}

/-- Two policies with the same selection kernels in rounds `n < m` induce the same law
of the first `m` rounds. -/
lemma measure_eq_of_select_eq (P : Kernel S S) [IsMarkovKernel P]
    (σ π : MarkovBanditPolicy k S) (x : Fin k → S) :
    ∀ m, (∀ n, n < m → σ.select n = π.select n) →
      markovBanditMeasure P σ x m = markovBanditMeasure P π x m := by
  intro m
  induction m with
  | zero => intro _; rfl
  | succ m ih =>
    intro h
    have h1 := ih (fun n hn => h n (Nat.lt_succ_of_lt hn))
    have h2 : markovBanditStepKernel P σ m = markovBanditStepKernel P π m := by
      unfold markovBanditStepKernel
      rw [h m (Nat.lt_succ_self m)]
    simp only [markovBanditMeasure, h1, h2]

lemma roundReward_mem_Icc (P : Kernel S S) [IsMarkovKernel P] {r : S → ℝ} {C : ℝ}
    (hr0 : ∀ y, 0 ≤ r y) (hrC : ∀ y, r y ≤ C) (σ : MarkovBanditPolicy k S)
    (x : Fin k → S) (t : ℕ) :
    0 ≤ markovBanditRoundReward P r σ x t ∧ markovBanditRoundReward P r σ x t ≤ C := by
  unfold markovBanditRoundReward
  refine ⟨integral_nonneg fun h => hr0 _, ?_⟩
  have hb := norm_integral_le_of_norm_le_const (μ := markovBanditMeasure P σ x (t + 1))
    (f := fun h : MarkovBanditHistory k S (t + 1) => r ((h.1 (Fin.last t)).1 ((h.1 (Fin.last t)).2)))
    (C := C) (Filter.Eventually.of_forall fun h => by
      rw [Real.norm_eq_abs, abs_of_nonneg (hr0 _)]; exact hrC _)
  simp only [probReal_univ, mul_one] at hb
  exact le_trans (le_abs_self _) (by simpa [Real.norm_eq_abs] using hb)

lemma value_summable (P : Kernel S S) [IsMarkovKernel P] {r : S → ℝ} {C : ℝ}
    (hr0 : ∀ y, 0 ≤ r y) (hrC : ∀ y, r y ≤ C) {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1)
    (σ : MarkovBanditPolicy k S) (x : Fin k → S) :
    Summable (fun t => β ^ t * markovBanditRoundReward P r σ x t) := by
  refine Summable.of_nonneg_of_le (fun t => ?_) (fun t => ?_)
    ((summable_geometric_of_lt_one hβ0.le hβ1).mul_right C)
  · exact mul_nonneg (pow_nonneg hβ0.le _) (roundReward_mem_Icc P hr0 hrC σ x t).1
  · exact mul_le_mul_of_nonneg_left (roundReward_mem_Icc P hr0 hrC σ x t).2
      (pow_nonneg hβ0.le _)

/-- If `σ` agrees with `π` before round `T`, the value of `σ` exceeds that of `π` by at most
`C β^T / (1 - β)`. -/
lemma value_sub_le_tail (P : Kernel S S) [IsMarkovKernel P] {r : S → ℝ} {C : ℝ}
    (hr0 : ∀ y, 0 ≤ r y) (hrC : ∀ y, r y ≤ C) {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1)
    (σ π : MarkovBanditPolicy k S) (x : Fin k → S) (T : ℕ)
    (hagree : ∀ n, n < T → σ.select n = π.select n) :
    markovBanditDiscountedValue P r β σ x - markovBanditDiscountedValue P r β π x ≤
      C * β ^ T * (1 - β)⁻¹ := by
  have hsσ := value_summable P hr0 hrC hβ0 hβ1 σ x
  have hsπ := value_summable P hr0 hrC hβ0 hβ1 π x
  unfold markovBanditDiscountedValue
  rw [← hsσ.tsum_sub hsπ]
  set a := fun t => β ^ t * markovBanditRoundReward P r σ x t -
    β ^ t * markovBanditRoundReward P r π x t with ha
  have hsa : Summable a := hsσ.sub hsπ
  rw [← hsa.sum_add_tsum_nat_add T]
  have h0 : ∑ i ∈ Finset.range T, a i = 0 := by
    refine Finset.sum_eq_zero fun i hi => ?_
    have hi' := Finset.mem_range.1 hi
    have hm := measure_eq_of_select_eq P σ π x (i + 1) (fun n hn => hagree n (by omega))
    simp only [ha, markovBanditRoundReward, hm, sub_self]
  rw [h0, zero_add]
  have hle : ∀ i, a (i + T) ≤ C * β ^ T * β ^ i := by
    intro i
    simp only [ha]
    have h1 := (roundReward_mem_Icc P hr0 hrC σ x (i + T)).2
    have h2 := (roundReward_mem_Icc P hr0 hrC π x (i + T)).1
    have hp : 0 ≤ β ^ (i + T) := pow_nonneg hβ0.le _
    rw [pow_add]
    have hp' : 0 ≤ β ^ i * β ^ T := by rw [← pow_add]; exact hp
    nlinarith [mul_nonneg hp' h2, mul_le_mul_of_nonneg_left h1 hp']
  calc ∑' i, a (i + T) ≤ ∑' i, C * β ^ T * β ^ i :=
        Summable.tsum_le_tsum hle ((summable_nat_add_iff T).2 hsa)
          ((summable_geometric_of_lt_one hβ0.le hβ1).mul_left _)
    _ = C * β ^ T * (1 - β)⁻¹ := by
        rw [tsum_mul_left, tsum_geometric_of_lt_one hβ0.le hβ1]

/-! ### Construction of the comparison policies -/

/-- Read an arm index from a natural number (out-of-range numbers go to a fixed arm). -/
def natToArm (hk : 0 < k) (n : ℕ) : Fin k := if h : n < k then ⟨n, h⟩ else ⟨0, hk⟩

/-- The arm-maximality predicate, indexed by naturals. -/
def IsMaxNat (γ : S → ℝ) (hk : 0 < k) (y : Fin k → S) (n : ℕ) : Prop :=
  ∀ i, γ (y i) ≤ γ (y (natToArm hk n))

lemma exists_isMaxNat (γ : S → ℝ) (hk : 0 < k) (y : Fin k → S) : ∃ n, IsMaxNat γ hk y n := by
  haveI : Nonempty (Fin k) := ⟨⟨0, hk⟩⟩
  obtain ⟨a, -, ha⟩ := Finset.univ.exists_max_image (fun a => γ (y a)) Finset.univ_nonempty
  refine ⟨a.val, fun i => ?_⟩
  have : natToArm hk a.val = a := by simp [natToArm]
  rw [this]
  exact ha i (Finset.mem_univ _)

/-- A measurable selection of an arm of greatest index. -/
noncomputable def gChoice (γ : S → ℝ) (hk : 0 < k) (y : Fin k → S) : Fin k :=
  natToArm hk (Nat.find (exists_isMaxNat γ hk y))

lemma gChoice_spec (γ : S → ℝ) (hk : 0 < k) (y : Fin k → S) :
    ∀ i, γ (y i) ≤ γ (y (gChoice γ hk y)) :=
  Nat.find_spec (exists_isMaxNat γ hk y)

lemma measurable_eval_pair :
    Measurable (fun p : (Fin k → S) × Fin k => p.1 p.2) :=
  measurable_from_prod_countable_left fun a => measurable_pi_apply a

lemma measurable_gChoice {γ : S → ℝ} (hγ : Measurable γ) (hk : 0 < k) :
    Measurable (gChoice γ hk) := by
  unfold gChoice
  refine (measurable_from_top (f := natToArm hk)).comp ?_
  refine measurable_find _ fun n => ?_
  unfold IsMaxNat
  rw [Set.ofPred_forall]
  exact MeasurableSet.iInter fun i =>
    measurableSet_le (hγ.comp (measurable_pi_apply i)) (hγ.comp (measurable_pi_apply _))

/-- Kernel playing a greatest-index arm deterministically. -/
noncomputable def gKernel {γ : S → ℝ} (hγ : Measurable γ) (hk : 0 < k) (n : ℕ) :
    Kernel (MarkovBanditHistory k S n) (Fin k) :=
  Kernel.deterministic (fun h => gChoice γ hk h.2) ((measurable_gChoice hγ hk).comp measurable_snd)

lemma gKernel_apply {γ : S → ℝ} (hγ : Measurable γ) (hk : 0 < k) (n : ℕ)
    (h : MarkovBanditHistory k S n) :
    gKernel hγ hk n h {a | ∀ i, γ (h.2 i) ≤ γ (h.2 a)} = 1 := by
  unfold gKernel
  rw [Kernel.deterministic_apply' _ _ (Set.toFinite _).measurableSet]
  simp [Set.indicator, gChoice_spec γ hk h.2]

instance gKernel.instIsMarkovKernel {γ : S → ℝ} (hγ : Measurable γ) (hk : 0 < k) (n : ℕ) :
    IsMarkovKernel (gKernel (k := k) hγ hk n) := by
  unfold gKernel; infer_instance

/-- `π*(t)`: follow `π` before round `t`, then play a greatest-index arm. -/
noncomputable def swPolicy {γ : S → ℝ} (hγ : Measurable γ) (hk : 0 < k)
    (π : MarkovBanditPolicy k S) (t : ℕ) : MarkovBanditPolicy k S where
  select n := if n < t then π.select n else gKernel hγ hk n
  markov n := by split_ifs <;> infer_instance

lemma measurableSet_runContinues (P : Kernel S S) [IsMarkovKernel P] (r : S → ℝ) (β : ℝ)
    (hγ : Measurable (gittinsIndex P r β)) (t n : ℕ) (hn : t < n) :
    MeasurableSet {h : MarkovBanditHistory k S n | WeberGittins.IndexGap.RunContinues P r β t n hn h} := by
  have hj : Measurable (fun h : MarkovBanditHistory k S n => (h.1 ⟨t, hn⟩).2) :=
    measurable_snd.comp ((measurable_pi_apply _).comp measurable_fst)
  have hv : ∀ m : Fin n, Measurable (fun h : MarkovBanditHistory k S n =>
      gittinsIndex P r β ((h.1 m).1 (h.1 ⟨t, hn⟩).2)) := fun m =>
    hγ.comp (measurable_eval_pair.comp
      ((measurable_fst.comp ((measurable_pi_apply _).comp measurable_fst)).prodMk hj))
  have hc : Measurable (fun h : MarkovBanditHistory k S n =>
      gittinsIndex P r β (h.2 (h.1 ⟨t, hn⟩).2)) :=
    hγ.comp (measurable_eval_pair.comp (measurable_snd.prodMk hj))
  simp only [WeberGittins.IndexGap.RunContinues, Set.setOf_and]
  refine MeasurableSet.inter ?_ (MeasurableSet.inter ?_ ?_)
  · rw [Set.ofPred_forall]
    refine MeasurableSet.iInter fun m => ?_
    by_cases htm : t ≤ (m : ℕ)
    · simp only [htm, forall_const]
      exact measurableSet_eq_fun
        (measurable_snd.comp ((measurable_pi_apply _).comp measurable_fst)) hj
    · simp [htm]
  · rw [Set.ofPred_forall]
    refine MeasurableSet.iInter fun m => ?_
    by_cases htm : t < (m : ℕ)
    · simp only [htm, forall_const]
      exact measurableSet_le (hv ⟨t, hn⟩) (hv m)
    · simp [htm]
  · exact measurableSet_le (hv ⟨t, hn⟩) hc

/-- The arm chosen by `π(t)` at round `n > t`. -/
noncomputable def runChoice (P : Kernel S S) [IsMarkovKernel P] (r : S → ℝ) (β : ℝ)
    (hk : 0 < k) (t n : ℕ) (hn : t < n) (h : MarkovBanditHistory k S n) : Fin k :=
  if WeberGittins.IndexGap.RunContinues P r β t n hn h then (h.1 ⟨t, hn⟩).2
  else gChoice (gittinsIndex P r β) hk h.2

lemma measurable_runChoice (P : Kernel S S) [IsMarkovKernel P] (r : S → ℝ) (β : ℝ)
    (hγ : Measurable (gittinsIndex P r β)) (hk : 0 < k) (t n : ℕ) (hn : t < n) :
    Measurable (runChoice (k := k) P r β hk t n hn) := by
  unfold runChoice
  exact Measurable.ite (measurableSet_runContinues P r β hγ t n hn)
    (measurable_snd.comp ((measurable_pi_apply _).comp measurable_fst))
    ((measurable_gChoice hγ hk).comp measurable_snd)

/-- `π(t)`: follow `π` through round `t`, keep playing `j(t)` while its charge stays at least
its round-`t` value, then play a greatest-index arm. -/
noncomputable def runPolicy (P : Kernel S S) [IsMarkovKernel P] (r : S → ℝ) (β : ℝ)
    (hγ : Measurable (gittinsIndex P r β)) (hk : 0 < k)
    (π : MarkovBanditPolicy k S) (t : ℕ) : MarkovBanditPolicy k S where
  select n := if hn : t < n then
      Kernel.deterministic (runChoice P r β hk t n hn) (measurable_runChoice P r β hγ hk t n hn)
    else π.select n
  markov n := by split_ifs <;> infer_instance

lemma runPolicy_spec (P : Kernel S S) [IsMarkovKernel P] (r : S → ℝ) (β : ℝ)
    (hγ : Measurable (gittinsIndex P r β)) (hk : 0 < k)
    (π : MarkovBanditPolicy k S) (t : ℕ) :
    WeberGittins.IndexGap.IsRunThenGittinsAt P r β π t (runPolicy P r β hγ hk π t) := by
  refine ⟨fun n hn => ?_, fun n hn h => ⟨fun hrc => ?_, fun hrc => ?_⟩⟩
  · show (if hn' : t < n then _ else π.select n) = π.select n
    rw [dif_neg (by omega)]
  · show (if hn' : t < n then _ else π.select n) h _ = 1
    rw [dif_pos hn, Kernel.deterministic_apply' _ _ (measurableSet_singleton _)]
    simp [runChoice, hrc]
  · show (if hn' : t < n then _ else π.select n) h _ = 1
    rw [dif_pos hn, Kernel.deterministic_apply' _ _ (Set.toFinite _).measurableSet]
    simp [Set.indicator, runChoice, hrc, gChoice_spec (gittinsIndex P r β) hk h.2]

lemma swPolicy_spec (P : Kernel S S) [IsMarkovKernel P] (r : S → ℝ) (β : ℝ)
    (hγ : Measurable (gittinsIndex P r β)) (hk : 0 < k)
    (π σ : MarkovBanditPolicy k S) (t : ℕ) (hagree : ∀ n, n < t → σ.select n = π.select n) :
    WeberGittins.IndexGap.IsSwitchToGittinsAt P r β σ t (swPolicy hγ hk π t) := by
  refine ⟨fun n hn => ?_, fun n hn h => ?_⟩
  · show (if n < t then π.select n else _) = σ.select n
    rw [if_pos hn, hagree n hn]
  · show (if n < t then π.select n else _) h _ = 1
    rw [if_neg (by omega)]
    exact gKernel_apply hγ hk n h

end WGThm3Aux

open WGThm3Aux in
theorem solution {k : ℕ} {S : Type*} [MeasurableSpace S]
    [StandardBorelSpace S] (P : Kernel S S) [IsMarkovKernel P]
    {r : S → ℝ} (hr : Measurable r) (hrb : WeberGittins.Suboptimality.RewardsNonnegBounded r)
    {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hγ : Measurable (gittinsIndex P r β))
    (πstar : MarkovBanditPolicy k S) (hπstar : IsGittinsIndexPolicy P r β πstar)
    (π : MarkovBanditPolicy k S) (x : Fin k → S) :
    markovBanditDiscountedValue P r β πstar x - markovBanditDiscountedValue P r β π x ≤
      ∑' t : ℕ, β ^ t * WeberGittins.Suboptimality.roundExpectation P π x t (fun h j =>
        (⨆ i : Fin k, WeberGittins.Suboptimality.weberIndex P r β (h.2 i)) - WeberGittins.Suboptimality.weberIndex P r β (h.2 j)) := by
  classical
  obtain ⟨hr0, C', hC'⟩ := hrb
  set C := max C' 0 with hCdef
  have hC : 0 ≤ C := le_max_right _ _
  have hrC : ∀ y, r y ≤ C := fun y => (hC' y).trans (le_max_left _ _)
  -- there is at least one arm
  have hk : 0 < k := by
    rcases Nat.eq_zero_or_pos k with h0 | h0
    · subst h0
      exfalso
      have h1 := measure_univ (μ := π.select 0 (fun t => t.elim0, x))
      rw [Set.univ_eq_empty_iff.2 (by infer_instance), measure_empty] at h1
      exact zero_ne_one h1
    · exact h0
  have h1β : 0 < 1 - β := by linarith
  -- the index bounds
  have hγb := gittinsIndex_mem_Icc P hC hr0 hrC hβ0 hβ1
  set E : ℕ → ℝ := fun t => WeberGittins.Suboptimality.roundExpectation P π x t (fun h j =>
      (⨆ i : Fin k, WeberGittins.Suboptimality.weberIndex P r β (h.2 i)) -
        WeberGittins.Suboptimality.weberIndex P r β (h.2 j)) with hE
  -- the integrand lies in [0, C/(1-β)]
  have hint : ∀ t (h : MarkovBanditHistory k S t) (j : Fin k),
      0 ≤ (⨆ i : Fin k, WeberGittins.Suboptimality.weberIndex P r β (h.2 i)) -
        WeberGittins.Suboptimality.weberIndex P r β (h.2 j) ∧
      (⨆ i : Fin k, WeberGittins.Suboptimality.weberIndex P r β (h.2 i)) -
        WeberGittins.Suboptimality.weberIndex P r β (h.2 j) ≤ C / (1 - β) := by
    intro t h j
    haveI : Nonempty (Fin k) := ⟨j⟩
    have hbdd : BddAbove (Set.range fun i : Fin k =>
        WeberGittins.Suboptimality.weberIndex P r β (h.2 i)) := (Set.finite_range _).bddAbove
    have hle := le_ciSup hbdd j
    have hsup : (⨆ i : Fin k, WeberGittins.Suboptimality.weberIndex P r β (h.2 i)) ≤ C / (1 - β) :=
      ciSup_le fun i => by
        unfold WeberGittins.Suboptimality.weberIndex
        exact div_le_div_of_nonneg_right (hγb _).2 h1β.le
    have hj0 : 0 ≤ WeberGittins.Suboptimality.weberIndex P r β (h.2 j) := by
      unfold WeberGittins.Suboptimality.weberIndex
      exact div_nonneg (hγb _).1 h1β.le
    constructor <;> linarith
  have hEb : ∀ t, 0 ≤ E t ∧ E t ≤ C / (1 - β) := by
    intro t
    simp only [hE, WeberGittins.Suboptimality.roundExpectation]
    refine ⟨integral_nonneg fun h => (hint _ _ _).1, ?_⟩
    have hb := norm_integral_le_of_norm_le_const (μ := markovBanditMeasure P π x (t + 1))
      (C := C / (1 - β))
      (f := fun h : MarkovBanditHistory k S (t + 1) =>
        (⨆ i : Fin k, WeberGittins.Suboptimality.weberIndex P r β
            ((truncateMarkovBanditHistory h).2 i)) -
          WeberGittins.Suboptimality.weberIndex P r β
            ((truncateMarkovBanditHistory h).2 (h.1 (Fin.last t)).2))
      (Filter.Eventually.of_forall fun h => by
        rw [Real.norm_eq_abs, abs_of_nonneg (hint _ _ _).1]; exact (hint _ _ _).2)
    simp only [probReal_univ, mul_one] at hb
    exact le_trans (le_abs_self _) (by simpa [Real.norm_eq_abs] using hb)
  have hsE : Summable (fun t => β ^ t * E t) := by
    refine Summable.of_nonneg_of_le (fun t => mul_nonneg (pow_nonneg hβ0.le _) (hEb t).1)
      (fun t => mul_le_mul_of_nonneg_left (hEb t).2 (pow_nonneg hβ0.le _))
      ((summable_geometric_of_lt_one hβ0.le hβ1).mul_right _)
  -- the milestone integrand equals the goal integrand
  have hfun : ∀ t, (fun (h : MarkovBanditHistory k S t) (j : Fin k) =>
      ((⨆ i : Fin k, gittinsIndex P r β (h.2 i)) - gittinsIndex P r β (h.2 j)) / (1 - β)) =
      (fun h j => (⨆ i : Fin k, WeberGittins.Suboptimality.weberIndex P r β (h.2 i)) -
        WeberGittins.Suboptimality.weberIndex P r β (h.2 j)) := by
    intro t
    funext h j
    unfold WeberGittins.Suboptimality.weberIndex
    rw [sub_div, div_eq_mul_inv, div_eq_mul_inv, Real.iSup_mul_of_nonneg (inv_nonneg.2 h1β.le)]
    simp only [div_eq_mul_inv]
  -- the comparison policies
  let A : ℕ → MarkovBanditPolicy k S := fun t =>
    match t with
    | 0 => πstar
    | s + 1 => swPolicy hγ hk π (s + 1)
  have hA : ∀ t, WeberGittins.IndexGap.IsSwitchToGittinsAt P r β π t (A t) := by
    intro t
    cases t with
    | zero => exact ⟨fun n hn => absurd hn (Nat.not_lt_zero n), fun n _ h => hπstar n h⟩
    | succ s => exact swPolicy_spec P r β hγ hk π π (s + 1) (fun _ _ => rfl)
  let R : ℕ → MarkovBanditPolicy k S := fun t => runPolicy P r β hγ hk π t
  have hstep : ∀ t, markovBanditDiscountedValue P r β (A t) x -
      markovBanditDiscountedValue P r β (A (t + 1)) x ≤ β ^ t * E t := by
    intro t
    have hRspec := runPolicy_spec P r β hγ hk π t
    have h1 := WeberGittins.IndexGap.switch_to_gittins_after_t_optimal P hr
      ⟨hr0, C', hC'⟩ hβ0 hβ1 (R t) (A (t + 1)) t
      (swPolicy_spec P r β hγ hk π (R t) (t + 1) (fun n hn => hRspec.1 n (by omega))) x
    have h2 := WeberGittins.IndexGap.eq8_one_switch_gap_bound P hr ⟨hr0, C', hC'⟩ hβ0 hβ1 hγ
      π t (A t) (R t) (hA t) hRspec x
    rw [hfun t] at h2
    have : β ^ t * E t = β ^ t * WeberGittins.Suboptimality.roundExpectation P π x t
        (fun h j => (⨆ i : Fin k, WeberGittins.Suboptimality.weberIndex P r β (h.2 i)) -
          WeberGittins.Suboptimality.weberIndex P r β (h.2 j)) := rfl
    linarith
  have hT : ∀ T, markovBanditDiscountedValue P r β πstar x -
      markovBanditDiscountedValue P r β π x ≤
      (∑' t, β ^ t * E t) + C * β ^ (T + 1) * (1 - β)⁻¹ := by
    intro T
    have htel := Finset.sum_range_sub' (fun t => markovBanditDiscountedValue P r β (A t) x) (T + 1)
    have hsum : ∑ t ∈ Finset.range (T + 1), (markovBanditDiscountedValue P r β (A t) x -
        markovBanditDiscountedValue P r β (A (t + 1)) x) ≤
        ∑ t ∈ Finset.range (T + 1), β ^ t * E t := Finset.sum_le_sum fun t _ => hstep t
    have hpart : ∑ t ∈ Finset.range (T + 1), β ^ t * E t ≤ ∑' t, β ^ t * E t :=
      hsE.sum_le_tsum _ fun t _ => mul_nonneg (pow_nonneg hβ0.le _) (hEb t).1
    have htail := value_sub_le_tail P hr0 hrC hβ0 hβ1 (A (T + 1)) π x (T + 1)
      (fun n hn => by
        show (if n < T + 1 then π.select n else _) = π.select n
        rw [if_pos hn])
    have hA0 : A 0 = πstar := rfl
    simp only [hA0] at htel
    linarith
  refine le_of_forall_pos_le_add fun ε hε => ?_
  obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one (show 0 < ε * (1 - β) / (C + 1) by positivity) hβ1
  have hb : C * β ^ (n + 1) * (1 - β)⁻¹ ≤ ε := by
    have hpow : β ^ (n + 1) ≤ β ^ n := pow_le_pow_of_le_one hβ0.le hβ1.le (Nat.le_succ n)
    rw [mul_inv_le_iff₀ h1β]
    have h3 : C * β ^ n ≤ (C + 1) * β ^ n := by nlinarith [pow_nonneg hβ0.le n]
    have h4 : (C + 1) * β ^ n ≤ ε * (1 - β) := by
      rw [lt_div_iff₀ (by linarith)] at hn; linarith
    nlinarith [pow_nonneg hβ0.le (n + 1)]
  have := hT n
  linarith
