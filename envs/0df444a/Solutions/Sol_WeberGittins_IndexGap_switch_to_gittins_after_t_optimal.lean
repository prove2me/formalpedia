-- Prove2me | solution 1 for WeberGittins.IndexGap.switch_to_gittins_after_t_optimal
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-06T05:20:06.162732+00:00
-- url     : https://prove2.me/submissions/18a87336-b2bb-494c-920c-4fb1f050f543

import Theorems.Thm_BanditAlgorithm_gittins_index_policy_dominates
import Definitions.Def_WeberGittins_IndexGap_SwitchPolicies

open MeasureTheory ProbabilityTheory BanditAlgorithm

namespace WGM1Aux

variable {S : Type*} [MeasurableSpace S] {k : ℕ}

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

lemma measurable_eval_pair :
    Measurable (fun p : (Fin k → S) × Fin k => p.1 p.2) :=
  measurable_from_prod_countable_left fun a => measurable_pi_apply a

/-! ### Concatenation of histories and continuation policies -/

/-- Concatenate a history of `T` rounds with a history of `m` further rounds. -/
def cat {T m : ℕ} (h : MarkovBanditHistory k S T) (h' : MarkovBanditHistory k S m) :
    MarkovBanditHistory k S (T + m) :=
  (Fin.append h.1 h'.1, h'.2)

lemma measurable_cat_right {T m : ℕ} (h : MarkovBanditHistory k S T) :
    Measurable (cat (m := m) h) := by
  refine Measurable.prodMk (measurable_pi_iff.2 fun i => ?_) measurable_snd
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i
  · simp only [Fin.append_left]
    exact measurable_const
  · simp only [Fin.append_right]
    exact (measurable_pi_apply j).comp measurable_fst

/-- The continuation of `σ` after the history `h` of `T` rounds. -/
noncomputable def contPolicy (σ : MarkovBanditPolicy k S) (T : ℕ)
    (h : MarkovBanditHistory k S T) : MarkovBanditPolicy k S where
  select n := (σ.select (T + n)).comap (cat h) (measurable_cat_right h)
  markov n := by infer_instance

/-- The one-round history update. -/
def snocH (n : ℕ) (p : MarkovBanditHistory k S n × (Fin k × S)) : MarkovBanditHistory k S (n + 1) :=
  (Fin.snoc (α := fun _ ↦ (Fin k → S) × Fin k) p.1.1 (p.1.2, p.2.1),
    Function.update p.1.2 p.2.1 p.2.2)

lemma measurable_snocH (n : ℕ) : Measurable (snocH (k := k) (S := S) n) :=
  measurable_markovBanditSnoc

lemma measure_succ (P : Kernel S S) [IsMarkovKernel P] (σ : MarkovBanditPolicy k S)
    (x : Fin k → S) (n : ℕ) :
    markovBanditMeasure P σ x (n + 1) =
      ((markovBanditMeasure P σ x n).compProd (markovBanditStepKernel P σ n)).map (snocH n) := rfl

lemma cat_snoc {T m : ℕ} (h : MarkovBanditHistory k S T) (h' : MarkovBanditHistory k S m)
    (p : Fin k × S) : snocH (T + m) (cat h h', p) = cat h (snocH m (h', p)) := by
  refine Prod.ext ?_ rfl
  simp only [snocH, cat]
  exact (Fin.append_snoc _ _ _).symm

lemma cat_nil {T : ℕ} (h : MarkovBanditHistory k S T) :
    cat (m := 0) h ((fun t => t.elim0), h.2) = h := by
  refine Prod.ext ?_ rfl
  simp only [cat]
  funext i
  rw [Fin.append_right_nil _ _ rfl]
  rfl

lemma step_lintegral (P : Kernel S S) [IsMarkovKernel P] (σ : MarkovBanditPolicy k S) {T m : ℕ}
    (h : MarkovBanditHistory k S T) (h' : MarkovBanditHistory k S m)
    {g : Fin k × S → ENNReal} (hg : Measurable g) :
    ∫⁻ p, g p ∂(markovBanditStepKernel P (contPolicy σ T h) m h') =
      ∫⁻ p, g p ∂(markovBanditStepKernel P σ (T + m) (cat h h')) := by
  unfold markovBanditStepKernel
  rw [Kernel.lintegral_compProd _ _ _ hg, Kernel.lintegral_compProd _ _ _ hg]
  simp only [contPolicy, Kernel.comap_apply]
  rfl

/-- Integral of `F (cat h ·)` against the continuation law. -/
noncomputable def Phi (P : Kernel S S) [IsMarkovKernel P] (σ : MarkovBanditPolicy k S) (T m : ℕ)
    (F : MarkovBanditHistory k S (T + m) → ENNReal) (h : MarkovBanditHistory k S T) : ENNReal :=
  ∫⁻ h', F (cat h h') ∂(markovBanditMeasure P (contPolicy σ T h) h.2 m)

lemma Phi_spec (P : Kernel S S) [IsMarkovKernel P] (σ : MarkovBanditPolicy k S) (x : Fin k → S)
    (T : ℕ) : ∀ m (F : MarkovBanditHistory k S (T + m) → ENNReal), Measurable F →
      Measurable (Phi P σ T m F) ∧
      ∫⁻ y, F y ∂(markovBanditMeasure P σ x (T + m)) =
        ∫⁻ h, Phi P σ T m F h ∂(markovBanditMeasure P σ x T) := by
  intro m
  induction m with
  | zero =>
    intro F hF
    have hPhi : Phi P σ T 0 F = F := by
      funext h
      unfold Phi
      show ∫⁻ h', F (cat h h') ∂(Measure.dirac ((fun t => t.elim0), h.2)) = F h
      refine (lintegral_dirac' _ (hF.comp (measurable_cat_right h))).trans ?_
      simp only [Function.comp_apply, cat_nil]
    rw [hPhi]
    exact ⟨hF, rfl⟩
  | succ m ih =>
    intro F hF
    set G : MarkovBanditHistory k S (T + m) → ENNReal :=
      fun y => ∫⁻ p, F (snocH (T + m) (y, p)) ∂(markovBanditStepKernel P σ (T + m) y) with hGdef
    have hG : Measurable G :=
      (hF.comp (measurable_snocH (T + m))).lintegral_kernel_prod_right'
    have hPhi : Phi P σ T (m + 1) F = Phi P σ T m G := by
      funext h
      unfold Phi
      rw [measure_succ]
      refine (lintegral_map (hF.comp (measurable_cat_right h)) (measurable_snocH m)).trans ?_
      refine (Measure.lintegral_compProd
        ((hF.comp (measurable_cat_right h)).comp (measurable_snocH m))).trans ?_
      refine lintegral_congr fun h' => ?_
      simp only [Function.comp_apply]
      rw [step_lintegral P σ h h'
        (g := fun p => F (cat h (snocH m (h', p))))
        ((hF.comp (measurable_cat_right h)).comp ((measurable_snocH m).comp measurable_prodMk_left))]
      simp only [hGdef, cat_snoc]
    refine ⟨hPhi ▸ (ih G hG).1, ?_⟩
    rw [hPhi, ← (ih G hG).2]
    show ∫⁻ y, F y ∂(markovBanditMeasure P σ x (T + m + 1)) = _
    rw [measure_succ]
    refine (lintegral_map hF (measurable_snocH _)).trans ?_
    exact Measure.lintegral_compProd (hF.comp (measurable_snocH _))

/-- The reward of the last round of a history of `n + 1` rounds. -/
def rew (r : S → ℝ) (n : ℕ) (h : MarkovBanditHistory k S (n + 1)) : ℝ :=
  r ((h.1 (Fin.last n)).1 ((h.1 (Fin.last n)).2))

lemma measurable_rew {r : S → ℝ} (hr : Measurable r) (n : ℕ) :
    Measurable (rew (k := k) r n) :=
  hr.comp (measurable_eval_pair.comp
    ((measurable_fst.comp ((measurable_pi_apply _).comp measurable_fst)).prodMk
      (measurable_snd.comp ((measurable_pi_apply _).comp measurable_fst))))

lemma rew_cat (r : S → ℝ) {T m : ℕ} (h : MarkovBanditHistory k S T)
    (h' : MarkovBanditHistory k S (m + 1)) :
    rew r (T + m) (cat (m := m + 1) h h') = rew r m h' := by
  unfold rew cat
  have : (Fin.last (T + m) : Fin (T + (m + 1))) = Fin.natAdd T (Fin.last m) := Fin.ext rfl
  simp only
  rw [this, Fin.append_right]

lemma ofReal_roundReward (P : Kernel S S) [IsMarkovKernel P] {r : S → ℝ} (hr : Measurable r)
    {C : ℝ} (hr0 : ∀ y, 0 ≤ r y) (hrC : ∀ y, r y ≤ C)
    (σ : MarkovBanditPolicy k S) (x : Fin k → S) (n : ℕ) :
    ENNReal.ofReal (markovBanditRoundReward P r σ x n) =
      ∫⁻ y, ENNReal.ofReal (rew r n y) ∂(markovBanditMeasure P σ x (n + 1)) := by
  unfold markovBanditRoundReward
  refine ofReal_integral_eq_lintegral_ofReal ?_ (Filter.Eventually.of_forall fun y => hr0 _)
  refine Integrable.of_bound (measurable_rew hr n).aestronglyMeasurable C
    (Filter.Eventually.of_forall fun y => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (hr0 _)]
  exact hrC _

lemma Phi_rew (P : Kernel S S) [IsMarkovKernel P] {r : S → ℝ} (hr : Measurable r)
    {C : ℝ} (hr0 : ∀ y, 0 ≤ r y) (hrC : ∀ y, r y ≤ C)
    (σ : MarkovBanditPolicy k S) (T m : ℕ) (h : MarkovBanditHistory k S T) :
    Phi P σ T (m + 1) (fun y => ENNReal.ofReal (rew r (T + m) y)) h =
      ENNReal.ofReal (markovBanditRoundReward P r (contPolicy σ T h) h.2 m) := by
  rw [ofReal_roundReward P hr hr0 hrC]
  unfold Phi
  refine lintegral_congr fun h' => ?_
  exact congrArg ENNReal.ofReal (rew_cat r h h')

/-- The value of the continuation after `h`. -/
noncomputable def W (P : Kernel S S) [IsMarkovKernel P] (r : S → ℝ) (β : ℝ)
    (σ : MarkovBanditPolicy k S) (T : ℕ) (h : MarkovBanditHistory k S T) : ℝ :=
  markovBanditDiscountedValue P r β (contPolicy σ T h) h.2

lemma tail_eq (P : Kernel S S) [IsMarkovKernel P] {r : S → ℝ} (hr : Measurable r)
    {C : ℝ} (hr0 : ∀ y, 0 ≤ r y) (hrC : ∀ y, r y ≤ C) {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1)
    (σ : MarkovBanditPolicy k S) (x : Fin k → S) (T : ℕ) :
    ENNReal.ofReal (∑' m, β ^ m * markovBanditRoundReward P r σ x (T + m)) =
      ∫⁻ h, ENNReal.ofReal (W P r β σ T h) ∂(markovBanditMeasure P σ x T) := by
  have hnn : ∀ (τ : MarkovBanditPolicy k S) y m,
      0 ≤ β ^ m * markovBanditRoundReward P r τ y m := fun τ y m =>
    mul_nonneg (pow_nonneg hβ0.le _) (roundReward_mem_Icc P hr0 hrC τ y m).1
  have hs : Summable (fun m => β ^ m * markovBanditRoundReward P r σ x (T + m)) := by
    refine Summable.of_nonneg_of_le (fun m => mul_nonneg (pow_nonneg hβ0.le _)
      (roundReward_mem_Icc P hr0 hrC σ x (T + m)).1) (fun m => ?_)
      ((summable_geometric_of_lt_one hβ0.le hβ1).mul_right C)
    exact mul_le_mul_of_nonneg_left (roundReward_mem_Icc P hr0 hrC σ x _).2 (pow_nonneg hβ0.le _)
  rw [ENNReal.ofReal_tsum_of_nonneg (fun m => mul_nonneg (pow_nonneg hβ0.le _)
    (roundReward_mem_Icc P hr0 hrC σ x (T + m)).1) hs]
  have hterm : ∀ m, ENNReal.ofReal (β ^ m * markovBanditRoundReward P r σ x (T + m)) =
      ∫⁻ h, ENNReal.ofReal (β ^ m) *
        Phi P σ T (m + 1) (fun y => ENNReal.ofReal (rew r (T + m) y)) h
        ∂(markovBanditMeasure P σ x T) := by
    intro m
    rw [ENNReal.ofReal_mul (pow_nonneg hβ0.le _), ofReal_roundReward P hr hr0 hrC,
      lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    congr 1
    exact (Phi_spec P σ x T (m + 1) _ (ENNReal.measurable_ofReal.comp (measurable_rew hr _))).2
  simp_rw [hterm]
  refine (lintegral_tsum (f := fun m h => ENNReal.ofReal (β ^ m) *
      Phi P σ T (m + 1) (fun y => ENNReal.ofReal (rew r (T + m) y)) h)
    (fun m => ((Phi_spec P σ x T (m + 1) _
      (ENNReal.measurable_ofReal.comp (measurable_rew hr _))).1.const_mul _).aemeasurable)).symm.trans ?_
  refine lintegral_congr fun h => ?_
  simp only [Phi_rew P hr hr0 hrC]
  unfold W markovBanditDiscountedValue
  rw [ENNReal.ofReal_tsum_of_nonneg (fun m => hnn _ _ m)
    (value_summable P hr0 hrC hβ0 hβ1 _ _)]
  refine tsum_congr fun m => ?_
  rw [ENNReal.ofReal_mul (pow_nonneg hβ0.le _)]

lemma value_split (P : Kernel S S) [IsMarkovKernel P] {r : S → ℝ}
    {C : ℝ} (hr0 : ∀ y, 0 ≤ r y) (hrC : ∀ y, r y ≤ C) {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1)
    (σ : MarkovBanditPolicy k S) (x : Fin k → S) (T : ℕ) :
    markovBanditDiscountedValue P r β σ x =
      ∑ s ∈ Finset.range T, β ^ s * markovBanditRoundReward P r σ x s +
        β ^ T * ∑' m, β ^ m * markovBanditRoundReward P r σ x (T + m) := by
  unfold markovBanditDiscountedValue
  rw [← (value_summable P hr0 hrC hβ0 hβ1 σ x).sum_add_tsum_nat_add T, ← tsum_mul_left]
  congr 1
  refine tsum_congr fun m => ?_
  rw [pow_add, add_comm m T]
  ring

end WGM1Aux

open WGM1Aux in
theorem solution {k : ℕ} {S : Type*} [MeasurableSpace S]
    [StandardBorelSpace S] (P : Kernel S S) [IsMarkovKernel P]
    {r : S → ℝ} (hr : Measurable r) (hrb : WeberGittins.Suboptimality.RewardsNonnegBounded r)
    {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1)
    (σ σ' : MarkovBanditPolicy k S) (t : ℕ)
    (hσ' : WeberGittins.IndexGap.IsSwitchToGittinsAt P r β σ (t + 1) σ')
    (x : Fin k → S) :
    markovBanditDiscountedValue P r β σ x ≤ markovBanditDiscountedValue P r β σ' x := by
  obtain ⟨hr0, C', hC'⟩ := hrb
  set C := max C' 0 with hCdef
  have hC : 0 ≤ C := le_max_right _ _
  have hrC : ∀ y, r y ≤ C := fun y => (hC' y).trans (le_max_left _ _)
  set T := t + 1 with hTdef
  -- integrability assumption of the index theorem
  have hint : DiscountedRewardIntegrable P r β := by
    intro y
    have hle : ∀ ω : ℕ → S, ∑' n : ℕ, ENNReal.ofReal (β ^ n * |r (ω n)|) ≤
        ENNReal.ofReal (∑' n : ℕ, β ^ n * C) := by
      intro ω
      rw [ENNReal.ofReal_tsum_of_nonneg (fun n => mul_nonneg (pow_nonneg hβ0.le _) hC)
        ((summable_geometric_of_lt_one hβ0.le hβ1).mul_right C)]
      refine ENNReal.tsum_le_tsum fun n => ENNReal.ofReal_le_ofReal ?_
      rw [abs_of_nonneg (hr0 _)]
      exact mul_le_mul_of_nonneg_left (hrC _) (pow_nonneg hβ0.le _)
    calc ∫⁻ ω, ∑' n : ℕ, ENNReal.ofReal (β ^ n * |r (ω n)|) ∂markovChainMeasure P y
        ≤ ∫⁻ _ω, ENNReal.ofReal (∑' n : ℕ, β ^ n * C) ∂markovChainMeasure P y :=
          lintegral_mono hle
      _ < ⊤ := by
          haveI : IsProbabilityMeasure (markovChainMeasure P y) := by
            unfold markovChainMeasure; infer_instance
          rw [lintegral_const]
          exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top (measure_lt_top _ _)
  -- the two policies induce the same law of the first T rounds
  have hagree : ∀ n, n < T → σ'.select n = σ.select n := hσ'.1
  have hμ : ∀ m, m ≤ T → markovBanditMeasure P σ' x m = markovBanditMeasure P σ x m :=
    fun m hm => measure_eq_of_select_eq P σ' σ x m (fun n hn => hagree n (by omega))
  have hhead : ∑ s ∈ Finset.range T, β ^ s * markovBanditRoundReward P r σ x s =
      ∑ s ∈ Finset.range T, β ^ s * markovBanditRoundReward P r σ' x s := by
    refine Finset.sum_congr rfl fun s hs => ?_
    have hs' := Finset.mem_range.1 hs
    unfold markovBanditRoundReward
    rw [hμ (s + 1) (by omega)]
  -- continuation values are dominated by the Gittins continuation
  have hW : ∀ h : MarkovBanditHistory k S T, W P r β σ T h ≤ W P r β σ' T h := by
    intro h
    have hG : IsGittinsIndexPolicy P r β (contPolicy σ' T h) := by
      intro n h'
      simp only [contPolicy, Kernel.comap_apply]
      exact hσ'.2 (T + n) (Nat.le_add_right T n) (cat h h')
    exact gittins_index_policy_dominates P hr hβ0 hβ1 hint (contPolicy σ' T h) hG h.2
      (contPolicy σ T h)
  have hnn : ∀ τ : MarkovBanditPolicy k S, 0 ≤ ∑' m, β ^ m * markovBanditRoundReward P r τ x (T + m) :=
    fun τ => tsum_nonneg fun m =>
      mul_nonneg (pow_nonneg hβ0.le _) (roundReward_mem_Icc P hr0 hrC τ x _).1
  have htail : ∑' m, β ^ m * markovBanditRoundReward P r σ x (T + m) ≤
      ∑' m, β ^ m * markovBanditRoundReward P r σ' x (T + m) := by
    rw [← ENNReal.ofReal_le_ofReal_iff (hnn σ'), tail_eq P hr hr0 hrC hβ0 hβ1 σ x T,
      tail_eq P hr hr0 hrC hβ0 hβ1 σ' x T, hμ T le_rfl]
    exact lintegral_mono fun h => ENNReal.ofReal_le_ofReal (hW h)
  rw [value_split P hr0 hrC hβ0 hβ1 σ x T, value_split P hr0 hrC hβ0 hβ1 σ' x T, hhead]
  have := mul_le_mul_of_nonneg_left htail (pow_nonneg hβ0.le T)
  linarith
