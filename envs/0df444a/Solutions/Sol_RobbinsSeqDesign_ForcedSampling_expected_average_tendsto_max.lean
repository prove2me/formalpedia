-- Prove2me | solution 1 for RobbinsSeqDesign.ForcedSampling.expected_average_tendsto_max
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-22T01:06:33.305504+00:00
-- url     : https://prove2.me/submissions/e4fa311d-9a2c-4cd7-8005-e19482d46131

import Mathlib
import Definitions.Def_RobbinsSeqDesign_ForcedSampling_Rule
import Definitions.Def_RobbinsSeqDesign_ForcedSampling_Loss

open MeasureTheory ProbabilityTheory Filter Topology BanditAlgorithm

namespace RobbinsSeqDesign.ForcedSampling


lemma toeplitz (w a : ℕ → ℝ) (L : ℝ) (hw : ∀ s, 0 ≤ w s)
    (hW : Tendsto (fun n => ∑ s ∈ Finset.range n, w s) atTop atTop)
    (ha : Tendsto a atTop (𝓝 L)) :
    Tendsto (fun n => (∑ s ∈ Finset.range n, w s * a s) / ∑ s ∈ Finset.range n, w s) atTop (𝓝 L) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨N1, hN1⟩ := (Metric.tendsto_atTop.mp ha) (ε / 2) (by positivity)
  set C : ℝ := ∑ s ∈ Finset.range N1, w s * |a s - L| with hC
  have hC0 : 0 ≤ C := Finset.sum_nonneg fun s _ => mul_nonneg (hw s) (abs_nonneg _)
  obtain ⟨N2, hN2⟩ := Filter.eventually_atTop.mp (hW.eventually_gt_atTop (2 * C / ε + 1))
  refine ⟨max N1 N2, fun n hn => ?_⟩
  have hn1 : N1 ≤ n := le_trans (le_max_left _ _) hn
  have hn2 : N2 ≤ n := le_trans (le_max_right _ _) hn
  set W := ∑ s ∈ Finset.range n, w s with hWdef
  have hWpos : 0 < W := by
    have := hN2 n hn2
    have : 0 ≤ 2 * C / ε := by positivity
    linarith
  have hWbig : 2 * C / ε < W := by have := hN2 n hn2; linarith
  rw [Real.dist_eq]
  have e1 : (∑ s ∈ Finset.range n, w s * a s) / W - L = (∑ s ∈ Finset.range n, w s * (a s - L)) / W := by
    field_simp
    rw [hWdef, Finset.sum_mul]
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun s _ => by ring
  rw [e1, abs_div, abs_of_pos hWpos, div_lt_iff₀ hWpos]
  have e2 : |∑ s ∈ Finset.range n, w s * (a s - L)| ≤ ∑ s ∈ Finset.range n, w s * |a s - L| := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    refine Finset.sum_le_sum fun s _ => ?_
    rw [abs_mul, abs_of_nonneg (hw s)]
  refine e2.trans_lt ?_
  rw [← Finset.sum_range_add_sum_Ico _ hn1]
  have e3 : ∑ s ∈ Finset.Ico N1 n, w s * |a s - L| ≤ ∑ s ∈ Finset.Ico N1 n, w s * (ε / 2) := by
    refine Finset.sum_le_sum fun s hs => ?_
    have hs1 : N1 ≤ s := (Finset.mem_Ico.mp hs).1
    have := hN1 s hs1
    rw [Real.dist_eq] at this
    exact mul_le_mul_of_nonneg_left this.le (hw s)
  have e4 : ∑ s ∈ Finset.Ico N1 n, w s * (ε / 2) ≤ W * (ε / 2) := by
    rw [← Finset.sum_mul]
    refine mul_le_mul_of_nonneg_right ?_ (by positivity)
    rw [hWdef, ← Finset.sum_range_add_sum_Ico _ hn1]
    have : 0 ≤ ∑ s ∈ Finset.range N1, w s := Finset.sum_nonneg fun s _ => hw s
    linarith
  have e5 : C < W * (ε / 2) := by
    have : 2 * C / ε < W := hWbig
    rw [div_lt_iff₀ hε] at this
    nlinarith
  linarith

lemma kronecker (x b : ℕ → ℝ) (hb_pos : ∀ n, 0 < b n) (hb_mono : Monotone b)
    (hb_top : Tendsto b atTop atTop) (L : ℝ)
    (hconv : Tendsto (fun n => ∑ s ∈ Finset.range n, x s / b s) atTop (𝓝 L)) :
    Tendsto (fun n => (∑ s ∈ Finset.range n, x s) / b n) atTop (𝓝 0) := by
  set S : ℕ → ℝ := fun n => ∑ s ∈ Finset.range n, x s / b s with hS
  set w : ℕ → ℝ := fun s => b (s + 1) - b s with hw
  have hw0 : ∀ s, 0 ≤ w s := fun s => sub_nonneg.mpr (hb_mono (Nat.le_succ s))
  have hWsum : ∀ n, ∑ s ∈ Finset.range n, w s = b n - b 0 := by
    intro n; simp only [hw]; exact Finset.sum_range_sub b n
  have hWtop : Tendsto (fun n => ∑ s ∈ Finset.range n, w s) atTop atTop := by
    simp_rw [hWsum]
    simpa [sub_eq_add_neg] using tendsto_atTop_add_const_right atTop (-b 0) hb_top
  have hT := toeplitz w (fun s => S (s + 1)) L hw0 hWtop (hconv.comp (tendsto_add_atTop_nat 1))
  -- Abel summation
  have habel : ∀ n, ∑ s ∈ Finset.range n, x s =
      b n * S n - ∑ s ∈ Finset.range n, w s * S (s + 1) := by
    intro n
    induction n with
    | zero => simp [hS]
    | succ n ih =>
      rw [Finset.sum_range_succ, ih, Finset.sum_range_succ (fun s => w s * S (s + 1))]
      have hSn : S (n + 1) = S n + x n / b n := by simp [hS, Finset.sum_range_succ]
      have hbn := (hb_pos n).ne'
      simp only [hw]
      rw [hSn]
      field_simp
      ring
  have hratio : Tendsto (fun n => (∑ s ∈ Finset.range n, w s) / b n) atTop (𝓝 1) := by
    have : ∀ n, (∑ s ∈ Finset.range n, w s) / b n = 1 - b 0 / b n := by
      intro n; rw [hWsum]; field_simp [(hb_pos n).ne']
    simp_rw [this]
    have h0 : Tendsto (fun n => b 0 / b n) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop hb_top
    simpa using (tendsto_const_nhds (x := (1 : ℝ))).sub h0
  have hfin : Tendsto (fun n => S n - ((∑ s ∈ Finset.range n, w s) / b n) *
      ((∑ s ∈ Finset.range n, w s * S (s + 1)) / ∑ s ∈ Finset.range n, w s)) atTop (𝓝 (L - 1 * L)) :=
    hconv.sub (hratio.mul hT)
  have h0 : L - 1 * L = 0 := by ring
  rw [h0] at hfin
  refine hfin.congr' ?_
  filter_upwards [hWtop.eventually_gt_atTop 0] with n hn
  rw [habel n]
  have hbn := (hb_pos n).ne'
  field_simp



lemma combine (a b : ℝ) (c0 c1 : ℕ → ℕ) (hsum : ∀ n, c0 n + c1 n = n) (S Y0 Y1 : ℕ → ℝ)
    (hS : ∀ n, S n = Y0 n + Y1 n)
    (hY0 : Tendsto (fun n => Y0 n / (c0 n : ℝ)) atTop (𝓝 a))
    (hY1 : Tendsto (fun n => Y1 n / (c1 n : ℝ)) atTop (𝓝 b))
    (hc0 : Tendsto c0 atTop atTop) (hc1 : Tendsto c1 atTop atTop)
    (hw1 : a < b → Tendsto (fun n => (c0 n : ℝ) / n) atTop (𝓝 0))
    (hw2 : b < a → Tendsto (fun n => (c1 n : ℝ) / n) atTop (𝓝 0)) :
    Tendsto (fun n => ((c0 n : ℝ) * a + (c1 n : ℝ) * b) / n) atTop (𝓝 (max a b)) ∧
    Tendsto (fun n => S n / n) atTop (𝓝 (max a b)) := by
  have hn : ∀ᶠ n : ℕ in atTop, 0 < n := eventually_gt_atTop 0
  have hsumR : ∀ n, (c0 n : ℝ) + c1 n = n := fun n => by exact_mod_cast hsum n
  -- q converges
  have hq : Tendsto (fun n => ((c0 n : ℝ) * a + (c1 n : ℝ) * b) / n) atTop (𝓝 (max a b)) := by
    rcases lt_trichotomy a b with hab | hab | hab
    · have h := hw1 hab
      have h' : Tendsto (fun n => b + ((c0 n : ℝ) / n) * (a - b)) atTop (𝓝 (b + 0 * (a - b))) :=
        tendsto_const_nhds.add (h.mul_const _)
      rw [zero_mul, add_zero] at h'
      rw [max_eq_right hab.le]
      refine h'.congr' ?_
      filter_upwards [hn] with n hn
      have hnR : (0 : ℝ) < n := by exact_mod_cast hn
      have e : (c1 n : ℝ) = n - c0 n := by linarith [hsumR n]
      rw [e]
      field_simp
      ring
    · subst hab
      rw [max_self]
      refine tendsto_const_nhds.congr' ?_
      filter_upwards [hn] with n hn
      have hnR : (0 : ℝ) < n := by exact_mod_cast hn
      have e : (c1 n : ℝ) = n - c0 n := by linarith [hsumR n]
      rw [e]
      field_simp
      ring
    · have h := hw2 hab
      have h' : Tendsto (fun n => a + ((c1 n : ℝ) / n) * (b - a)) atTop (𝓝 (a + 0 * (b - a))) :=
        tendsto_const_nhds.add (h.mul_const _)
      rw [zero_mul, add_zero] at h'
      rw [max_eq_left hab.le]
      refine h'.congr' ?_
      filter_upwards [hn] with n hn
      have hnR : (0 : ℝ) < n := by exact_mod_cast hn
      have e : (c1 n : ℝ) = n - c0 n := by linarith [hsumR n]
      rw [e]
      field_simp
      ring
  refine ⟨hq, ?_⟩
  -- S/n - q → 0
  have hd0 : Tendsto (fun n => Y0 n / (c0 n : ℝ) - a) atTop (𝓝 0) := by
    simpa using hY0.sub_const a
  have hd1 : Tendsto (fun n => Y1 n / (c1 n : ℝ) - b) atTop (𝓝 0) := by
    simpa using hY1.sub_const b
  have hbound : Tendsto (fun n => |Y0 n / (c0 n : ℝ) - a| + |Y1 n / (c1 n : ℝ) - b|) atTop (𝓝 0) := by
    simpa using hd0.abs.add hd1.abs
  have hdiff : Tendsto (fun n => S n / n - ((c0 n : ℝ) * a + (c1 n : ℝ) * b) / n) atTop (𝓝 0) := by
    refine squeeze_zero_norm' ?_ hbound
    filter_upwards [hn, hc0.eventually_gt_atTop 0, hc1.eventually_gt_atTop 0] with n hn h0 h1
    have hnR : (0 : ℝ) < n := by exact_mod_cast hn
    have h0R : (0 : ℝ) < c0 n := by exact_mod_cast h0
    have h1R : (0 : ℝ) < c1 n := by exact_mod_cast h1
    have e : S n / n - ((c0 n : ℝ) * a + (c1 n : ℝ) * b) / n =
        ((c0 n : ℝ) / n) * (Y0 n / (c0 n : ℝ) - a) + ((c1 n : ℝ) / n) * (Y1 n / (c1 n : ℝ) - b) := by
      rw [hS n]
      have e : (c1 n : ℝ) = n - c0 n := by linarith [hsumR n]
      field_simp
      ring
    rw [e, Real.norm_eq_abs]
    have w0 : 0 ≤ (c0 n : ℝ) / n := by positivity
    have w1 : 0 ≤ (c1 n : ℝ) / n := by positivity
    have w0' : (c0 n : ℝ) / n ≤ 1 := by
      rw [div_le_one hnR]; have := hsumR n; linarith
    have w1' : (c1 n : ℝ) / n ≤ 1 := by
      rw [div_le_one hnR]; have := hsumR n; linarith
    calc _ ≤ |((c0 n : ℝ) / n) * (Y0 n / (c0 n : ℝ) - a)| + |((c1 n : ℝ) / n) * (Y1 n / (c1 n : ℝ) - b)| :=
          abs_add_le _ _
      _ = ((c0 n : ℝ) / n) * |Y0 n / (c0 n : ℝ) - a| + ((c1 n : ℝ) / n) * |Y1 n / (c1 n : ℝ) - b| := by
          rw [abs_mul, abs_mul, abs_of_nonneg w0, abs_of_nonneg w1]
      _ ≤ 1 * |Y0 n / (c0 n : ℝ) - a| + 1 * |Y1 n / (c1 n : ℝ) - b| := by
          gcongr
      _ = _ := by ring
  have := hq.add hdiff
  simpa using this


section KeyLemma

variable {k : ℕ} (ν : StochasticBandit k) (π : BanditPolicy k)

lemma measurable_pair (n : ℕ) :
    Measurable (fun ω : ℕ → Fin k × ℝ => (banditTrajPrefix k n ω, ω n)) :=
  (measurable_banditTrajPrefix).prodMk (measurable_pi_apply n)

/-- law of (prefix, next coordinate) -/
lemma lintegral_pair_succ (m : ℕ) (f : BanditHistory k (m + 1) × (Fin k × ℝ) → ENNReal)
    (hf : Measurable f) :
    ∫⁻ ω, f (banditTrajPrefix k (m + 1) ω, ω (m + 1)) ∂(banditTrajMeasure ν π) =
      ∫⁻ ω, ∫⁻ y, f (banditTrajPrefix k (m + 1) ω, y)
        ∂(banditStepKernel ν π (m + 1) (banditTrajPrefix k (m + 1) ω)) ∂(banditTrajMeasure ν π) := by
  have h := Kernel.map_frestrictLe_trajMeasure_compProd_eq_map_trajMeasure
    (X := fun _ => Fin k × ℝ) (μ₀ := banditStepKernel ν π 0 fun t => t.elim0) (κ := banditTrajKernel ν π) (a := m)
  have hpre : ∀ ω : ℕ → Fin k × ℝ, banditTrajPrefix k (m + 1) ω = banditIicHistory k m (Preorder.frestrictLe m ω) := fun ω => rfl
  have h' : ((banditTrajMeasure ν π).map (Preorder.frestrictLe m)) ⊗ₘ banditTrajKernel ν π m =
      (banditTrajMeasure ν π).map (fun x => (Preorder.frestrictLe m x, x (m + 1))) := h
  clear h
  set μ := banditTrajMeasure ν π with hμ
  have hmeas_iic : Measurable (fun ω : ℕ → Fin k × ℝ => banditIicHistory k m (Preorder.frestrictLe m ω)) := by
    exact measurable_banditIicHistory.comp (Preorder.measurable_frestrictLe m)
  have h1 : ∫⁻ ω, f (banditTrajPrefix k (m + 1) ω, ω (m + 1)) ∂μ =
      ∫⁻ z, f (banditIicHistory k m z.1, z.2) ∂(μ.map (fun x => (Preorder.frestrictLe m x, x (m + 1)))) := by
    rw [lintegral_map]
    · rfl
    · exact hf.comp (measurable_banditIicHistory.comp measurable_fst |>.prodMk measurable_snd)
    · exact (Preorder.measurable_frestrictLe m).prodMk (measurable_pi_apply _)
  rw [h1, ← h', Measure.lintegral_compProd]
  · rw [lintegral_map]
    · congr 1
    · exact (hf.comp (measurable_banditIicHistory.comp measurable_fst |>.prodMk measurable_snd)).lintegral_kernel_prod_right'
    · exact Preorder.measurable_frestrictLe m
  · exact hf.comp (measurable_banditIicHistory.comp measurable_fst |>.prodMk measurable_snd)


lemma marginal_zero :
    (banditTrajMeasure ν π).map (fun ω => ω 0) = banditStepKernel ν π 0 (fun t => t.elim0) := by
  unfold banditTrajMeasure Kernel.trajMeasure
  have h0 : (fun ω : ℕ → Fin k × ℝ => ω 0) =
      (fun y : (Π i : Finset.Iic 0, Fin k × ℝ) => y ⟨0, by simp⟩) ∘ Preorder.frestrictLe 0 := rfl
  have hg : Measurable (fun y : (Π i : Finset.Iic 0, Fin k × ℝ) => y ⟨0, by simp⟩) := by fun_prop
  rw [h0, ← Measure.map_map hg (Preorder.measurable_frestrictLe 0),
    Measure.map_comp _ _ (Preorder.measurable_frestrictLe 0)]
  simp only [Kernel.traj_map_frestrictLe]
  rw [Kernel.partialTraj_self, Measure.id_comp, Measure.map_map hg (by fun_prop)]
  have : ((fun y : (Π i : Finset.Iic 0, Fin k × ℝ) => y ⟨0, by simp⟩) ∘
      ⇑(MeasurableEquiv.piUnique fun i : Finset.Iic 0 => Fin k × ℝ).symm) = id := by
    funext x; rfl
  rw [this, Measure.map_id]


lemma lintegral_pair (n : ℕ) (f : BanditHistory k n × (Fin k × ℝ) → ENNReal)
    (hf : Measurable f) :
    ∫⁻ ω, f (banditTrajPrefix k n ω, ω n) ∂(banditTrajMeasure ν π) =
      ∫⁻ ω, ∫⁻ y, f (banditTrajPrefix k n ω, y)
        ∂(banditStepKernel ν π n (banditTrajPrefix k n ω)) ∂(banditTrajMeasure ν π) := by
  cases n with
  | zero =>
    have hp : ∀ ω : ℕ → Fin k × ℝ, banditTrajPrefix k 0 ω = (fun t => t.elim0) := fun ω =>
      funext fun t => t.elim0
    simp only [hp]
    rw [lintegral_const, measure_univ, mul_one]
    have : ∫⁻ ω, f ((fun t => t.elim0), ω 0) ∂(banditTrajMeasure ν π) =
        ∫⁻ y, f ((fun t => t.elim0), y) ∂((banditTrajMeasure ν π).map (fun ω => ω 0)) := by
      rw [lintegral_map]
      · exact hf.comp (measurable_const.prodMk measurable_id)
      · exact measurable_pi_apply 0
    rw [this, marginal_zero]
  | succ m => exact lintegral_pair_succ ν π m f hf

lemma pair_law (n : ℕ) :
    (banditTrajMeasure ν π).map (fun ω => (banditTrajPrefix k n ω, ω n)) =
      ((banditTrajMeasure ν π).map (banditTrajPrefix k n)) ⊗ₘ (banditStepKernel ν π n) := by
  refine Measure.ext_of_lintegral _ fun f hf => ?_
  rw [lintegral_map hf (measurable_pair n), Measure.lintegral_compProd hf,
    lintegral_pair ν π n f hf]
  rw [lintegral_map]
  · exact hf.lintegral_kernel_prod_right'
  · exact measurable_banditTrajPrefix


lemma integral_pair (n : ℕ) (g : BanditHistory k n × (Fin k × ℝ) → ℝ)
    (hg : Measurable g)
    (hint : Integrable (fun ω => g (banditTrajPrefix k n ω, ω n)) (banditTrajMeasure ν π)) :
    ∫ ω, g (banditTrajPrefix k n ω, ω n) ∂(banditTrajMeasure ν π) =
      ∫ ω, ∫ y, g (banditTrajPrefix k n ω, y)
        ∂(banditStepKernel ν π n (banditTrajPrefix k n ω)) ∂(banditTrajMeasure ν π) := by
  have hint' : Integrable g ((banditTrajMeasure ν π).map (fun ω => (banditTrajPrefix k n ω, ω n))) := by
    rw [integrable_map_measure hg.aestronglyMeasurable (measurable_pair n).aemeasurable]
    exact hint
  have h1 : ∫ ω, g (banditTrajPrefix k n ω, ω n) ∂(banditTrajMeasure ν π) =
      ∫ z, g z ∂((banditTrajMeasure ν π).map (fun ω => (banditTrajPrefix k n ω, ω n))) := by
    rw [integral_map (measurable_pair n).aemeasurable hg.aestronglyMeasurable]
  rw [pair_law ν π n] at hint' h1
  rw [h1, Measure.integral_compProd hint']
  rw [integral_map measurable_banditTrajPrefix.aemeasurable]
  exact hg.stronglyMeasurable.integral_kernel_prod_right'.aestronglyMeasurable


lemma integrable_of_bdd {α : Type*} [MeasurableSpace α] (μ : Measure α) [IsFiniteMeasure μ]
    (f : α → ℝ) (hf : Measurable f) (C : ℝ) (hC : ∀ x, |f x| ≤ C) : Integrable f μ :=
  Integrable.of_bound hf.aestronglyMeasurable C (Filter.Eventually.of_forall fun x => by
    simpa [Real.norm_eq_abs] using hC x)

lemma condExp_pair (n : ℕ) (g : BanditHistory k n × (Fin k × ℝ) → ℝ)
    (hg : Measurable g) (C : ℝ) (hC : ∀ z, |g z| ≤ C) :
    (banditTrajMeasure ν π)[fun ω => g (banditTrajPrefix k n ω, ω n) | banditFiltration k n]
      =ᵐ[banditTrajMeasure ν π]
      fun ω => ∫ y, g (banditTrajPrefix k n ω, y)
        ∂(banditStepKernel ν π n (banditTrajPrefix k n ω)) := by
  have hmeasF : Measurable (fun ω : ℕ → Fin k × ℝ => g (banditTrajPrefix k n ω, ω n)) :=
    hg.comp (measurable_pair n)
  have hintF : Integrable (fun ω : ℕ → Fin k × ℝ => g (banditTrajPrefix k n ω, ω n))
      (banditTrajMeasure ν π) := integrable_of_bdd _ _ hmeasF C (fun ω => hC _)
  set φ : BanditHistory k n → ℝ := fun h => ∫ y, g (h, y) ∂(banditStepKernel ν π n h) with hφ
  have hφm : Measurable φ := hg.stronglyMeasurable.integral_kernel_prod_right'.measurable
  have hφb : ∀ h, |φ h| ≤ C := by
    intro h
    have := norm_integral_le_of_norm_le_const (μ := banditStepKernel ν π n h) (f := fun y => g (h, y))
      (C := C) (Filter.Eventually.of_forall fun y => by simpa [Real.norm_eq_abs] using hC (h, y))
    simpa [hφ, Real.norm_eq_abs] using this
  refine (ae_eq_condExp_of_forall_setIntegral_eq ((banditFiltration k).le n) hintF
    (fun s _ _ => ?_) (fun s hs _ => ?_) ?_).symm
  · exact (integrable_of_bdd _ _ (hφm.comp measurable_banditTrajPrefix) C
      (fun ω => hφb _)).integrableOn
  · obtain ⟨B, hB, rfl⟩ := hs
    have hset : MeasurableSet (banditTrajPrefix k n ⁻¹' B) := measurable_banditTrajPrefix hB
    set G : BanditHistory k n × (Fin k × ℝ) → ℝ := fun z => B.indicator (fun _ => (1 : ℝ)) z.1 * g z with hG
    have hGm : Measurable G := (measurable_const.indicator hB |>.comp measurable_fst).mul hg
    have hGb : ∀ z, |G z| ≤ C := by
      intro z
      by_cases h : z.1 ∈ B
      · simpa [hG, h] using hC z
      · have := abs_nonneg (g z)
        have := hC z
        simp [hG, h]
        linarith
    have key := integral_pair ν π n G hGm
      (integrable_of_bdd _ _ (hGm.comp (measurable_pair n)) C (fun ω => hGb _))
    rw [← integral_indicator hset, ← integral_indicator hset]
    have e1 : (banditTrajPrefix k n ⁻¹' B).indicator (fun ω => g (banditTrajPrefix k n ω, ω n)) =
        fun ω => G (banditTrajPrefix k n ω, ω n) := by
      funext ω
      by_cases h : banditTrajPrefix k n ω ∈ B
      · simp [hG, h]
      · simp [hG, h]
    have e2 : (banditTrajPrefix k n ⁻¹' B).indicator (fun ω => φ (banditTrajPrefix k n ω)) =
        fun ω => ∫ y, G (banditTrajPrefix k n ω, y)
          ∂(banditStepKernel ν π n (banditTrajPrefix k n ω)) := by
      funext ω
      by_cases h : banditTrajPrefix k n ω ∈ B
      · simp [hG, hφ, h]
      · simp [hG, hφ, h]
    rw [e1, e2, key]
  · have hsm : StronglyMeasurable[banditFiltration k n]
        (fun ω => φ (banditTrajPrefix k n ω)) :=
      (hφm.comp (comap_measurable (banditTrajPrefix k n))).stronglyMeasurable
    exact hsm.aestronglyMeasurable


lemma integral_step (n : ℕ) (h : BanditHistory k n) (Φ : Fin k × ℝ → ℝ) (hΦ : Measurable Φ)
    (C : ℝ) (hC : ∀ z, |Φ z| ≤ C) :
    ∫ y, Φ y ∂(banditStepKernel ν π n h) =
      ∫ a, ∫ x, Φ (a, x) ∂(ν.P a) ∂(π.select n h) := by
  unfold banditStepKernel
  rw [integral_compProd]
  · rfl
  · exact integrable_of_bdd _ _ hΦ C hC

end KeyLemma

section Arm

variable {k : ℕ} (ν : StochasticBandit k) (π : BanditPolicy k) (i : Fin k)

/-- truncation -/
noncomputable def tr (x : ℝ) (c : ℕ) : ℝ := if |x| ≤ c then x else 0

lemma abs_tr_le (x : ℝ) (c : ℕ) : |tr x c| ≤ c := by
  unfold tr; split_ifs with h
  · exact h
  · simp

lemma abs_tr_le_abs (x : ℝ) (c : ℕ) : |tr x c| ≤ |x| := by
  unfold tr; split_ifs with h
  · exact le_rfl
  · simp

lemma measurable_tr (c : ℕ) : Measurable (fun x : ℝ => tr x c) := by
  unfold tr
  exact Measurable.ite (measurableSet_le measurable_abs measurable_const) measurable_id measurable_const

lemma measurable_tr2 : Measurable (fun p : ℕ × ℝ => tr p.2 p.1) :=
  measurable_from_prod_countable_right (fun c => measurable_tr c)

/-- mean of truncation -/
noncomputable def mtr (c : ℕ) : ℝ := ∫ x, tr x c ∂(ν.P i)

lemma abs_mtr_le (c : ℕ) : |mtr ν i c| ≤ c := by
  unfold mtr
  have := norm_integral_le_of_norm_le_const (μ := ν.P i) (f := fun x => tr x c) (C := (c : ℝ))
    (Filter.Eventually.of_forall fun x => by simpa [Real.norm_eq_abs] using abs_tr_le x c)
  simpa [Real.norm_eq_abs] using this

lemma measurable_mtr2 : Measurable (fun c : ℕ => mtr ν i c) := measurable_from_nat

/-- the normalized centered truncated increment -/
noncomputable def Dfun {n : ℕ} (h : BanditHistory k n) (y : Fin k × ℝ) : ℝ :=
  if y.1 = i then
    (tr y.2 (armPullCount i h + 1) - mtr ν i (armPullCount i h + 1)) / ((armPullCount i h : ℝ) + 1)
  else 0

lemma armPullCount_eq_sum {n : ℕ} (h : BanditHistory k n) :
    armPullCount i h = ∑ t : Fin n, if (h t).1 = i then 1 else 0 := by
  classical
  unfold armPullCount
  rw [Set.toFinset_ofPred, Finset.card_filter]


lemma measurable_armPullCount {n : ℕ} : Measurable (fun h : BanditHistory k n => armPullCount i h) := by
  classical
  have : (fun h : BanditHistory k n => armPullCount i h) =
      fun h => ∑ t : Fin n, if (h t).1 = i then 1 else 0 := funext fun h => armPullCount_eq_sum i h
  rw [this]
  refine Finset.measurable_sum _ fun t _ => ?_
  have hset : MeasurableSet {h : BanditHistory k n | (h t).1 = i} :=
    (measurable_fst.comp (measurable_pi_apply t)) (measurableSet_singleton i)
  exact Measurable.ite hset measurable_const measurable_const

noncomputable def Ffun (c : ℕ) (x : ℝ) : ℝ :=
  (tr x (c + 1) - mtr ν i (c + 1)) / ((c : ℝ) + 1)

lemma measurable_Ffun : Measurable (fun q : ℕ × ℝ => Ffun ν i q.1 q.2) := by
  refine measurable_from_prod_countable_right (fun c => ?_)
  simp only [Ffun]
  exact Measurable.div_const ((measurable_tr (c + 1)).sub_const _) _

lemma Dfun_eq {n : ℕ} (h : BanditHistory k n) (y : Fin k × ℝ) :
    Dfun ν i h y = if y.1 = i then Ffun ν i (armPullCount i h) y.2 else 0 := rfl

lemma measurable_Dfun {n : ℕ} :
    Measurable (fun p : BanditHistory k n × (Fin k × ℝ) => Dfun ν i p.1 p.2) := by
  simp_rw [Dfun_eq]
  refine Measurable.ite ?_ ?_ measurable_const
  · exact (measurable_fst.comp measurable_snd) (measurableSet_singleton i)
  · exact measurable_Ffun ν i |>.comp (((measurable_armPullCount i).comp measurable_fst).prodMk
      (measurable_snd.comp measurable_snd))

lemma abs_Ffun_le (c : ℕ) (x : ℝ) : |Ffun ν i c x| ≤ 2 := by
  unfold Ffun
  have hc : (0 : ℝ) < (c : ℝ) + 1 := by positivity
  rw [abs_div, abs_of_pos hc, div_le_iff₀ hc]
  have h1 := abs_tr_le x (c + 1)
  have h2 := abs_mtr_le ν i (c + 1)
  have h3 := abs_sub (tr x (c + 1)) (mtr ν i (c + 1))
  push_cast at h1 h2
  linarith

lemma abs_Dfun_le {n : ℕ} (h : BanditHistory k n) (y : Fin k × ℝ) : |Dfun ν i h y| ≤ 2 := by
  rw [Dfun_eq]; split_ifs
  · exact abs_Ffun_le ν i _ _
  · simp

/-- pull count of arm `i` along a trajectory -/
def cntp (s : ℕ) (ω : ℕ → Fin k × ℝ) : ℕ := armPullCount i (banditTrajPrefix k s ω)

lemma cntp_eq (s : ℕ) (ω : ℕ → Fin k × ℝ) :
    cntp i s ω = ∑ r ∈ Finset.range s, if (ω r).1 = i then 1 else 0 := by
  unfold cntp
  rw [armPullCount_eq_sum]
  exact Fin.sum_univ_eq_sum_range (fun r => if (ω r).1 = i then 1 else 0) s

lemma cntp_succ (s : ℕ) (ω : ℕ → Fin k × ℝ) :
    cntp i (s + 1) ω = cntp i s ω + if (ω s).1 = i then 1 else 0 := by
  rw [cntp_eq, cntp_eq, Finset.sum_range_succ]

/-- the increments -/
noncomputable def dd (s : ℕ) (ω : ℕ → Fin k × ℝ) : ℝ :=
  Dfun ν i (banditTrajPrefix k s ω) (ω s)

/-- the martingale -/
noncomputable def Mt (t : ℕ) (ω : ℕ → Fin k × ℝ) : ℝ := ∑ s ∈ Finset.range t, dd ν i s ω

lemma abs_dd_le (s : ℕ) (ω : ℕ → Fin k × ℝ) : |dd ν i s ω| ≤ 2 := abs_Dfun_le ν i _ _

lemma measurable_dd (s : ℕ) : Measurable (dd ν i s) :=
  (measurable_Dfun ν i).comp (measurable_pair s)

lemma measurable_Mt (t : ℕ) : Measurable (Mt ν i t) :=
  Finset.measurable_sum _ fun s _ => measurable_dd ν i s

lemma Ffun_integral_zero (c : ℕ) : ∫ x, Ffun ν i c x ∂(ν.P i) = 0 := by
  unfold Ffun
  have hint : Integrable (fun x => tr x (c + 1)) (ν.P i) :=
    integrable_of_bdd _ _ (measurable_tr _) ((c + 1 : ℕ) : ℝ) (fun x => abs_tr_le x _)
  rw [integral_div, integral_sub hint (integrable_const _), integral_const]
  simp [mtr]

lemma Dfun_step_zero (n : ℕ) (h : BanditHistory k n) :
    ∫ y, Dfun ν i h y ∂(banditStepKernel ν π n h) = 0 := by
  rw [integral_step ν π n h (fun y => Dfun ν i h y)
    ((measurable_Dfun ν i).comp (measurable_const.prodMk measurable_id)) 2 (fun z => abs_Dfun_le ν i h z)]
  refine integral_eq_zero_of_ae (Filter.Eventually.of_forall fun a => ?_)
  by_cases ha : a = i
  · subst ha
    simp only [Dfun_eq, if_true, Pi.zero_apply]
    exact Ffun_integral_zero ν a _
  · simp [Dfun_eq, ha]

lemma condExp_dd (s : ℕ) :
    (banditTrajMeasure ν π)[dd ν i s | banditFiltration k s] =ᵐ[banditTrajMeasure ν π] 0 := by
  have := condExp_pair ν π s (fun z => Dfun ν i z.1 z.2) (measurable_Dfun ν i) 2
    (fun z => abs_Dfun_le ν i _ _)
  refine this.trans (Filter.Eventually.of_forall fun ω => ?_)
  exact Dfun_step_zero ν π i s _

lemma stronglyMeasurable_dd (s : ℕ) :
    StronglyMeasurable[banditFiltration k (s + 1)] (dd ν i s) := by
  let ψ : BanditHistory k (s + 1) → BanditHistory k s × (Fin k × ℝ) :=
    fun h => (fun t => h (Fin.castSucc t), h (Fin.last s))
  have hψ : Measurable ψ := by
    refine Measurable.prodMk ?_ (measurable_pi_apply _)
    exact measurable_pi_lambda _ fun t => measurable_pi_apply _
  have : dd ν i s = (fun p : BanditHistory k s × (Fin k × ℝ) => Dfun ν i p.1 p.2) ∘ ψ ∘
      banditTrajPrefix k (s + 1) := by
    funext ω; rfl
  rw [this]
  exact (((measurable_Dfun ν i).comp hψ).comp (comap_measurable (banditTrajPrefix k (s + 1)))).stronglyMeasurable

lemma stronglyAdapted_Mt : StronglyAdapted (banditFiltration k) (Mt ν i) := by
  intro t
  have : Mt ν i t = ∑ s ∈ Finset.range t, dd ν i s := by funext ω; simp [Mt]
  rw [this]
  refine Finset.stronglyMeasurable_sum _ fun s hs => ?_
  have hst : s + 1 ≤ t := Finset.mem_range.mp hs
  exact (stronglyMeasurable_dd ν i s).mono ((banditFiltration k).mono hst)

lemma integrable_Mt (t : ℕ) : Integrable (Mt ν i t) (banditTrajMeasure ν π) :=
  integrable_of_bdd _ _ (measurable_Mt ν i t) (2 * t) (fun ω => by
    unfold Mt
    calc |∑ s ∈ Finset.range t, dd ν i s ω| ≤ ∑ s ∈ Finset.range t, |dd ν i s ω| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ s ∈ Finset.range t, (2 : ℝ) := Finset.sum_le_sum fun s _ => abs_dd_le ν i s ω
      _ = 2 * t := by simp [mul_comm])

lemma martingale_Mt : Martingale (Mt ν i) (banditFiltration k) (banditTrajMeasure ν π) := by
  refine martingale_of_condExp_sub_eq_zero_nat (stronglyAdapted_Mt ν i) (integrable_Mt ν π i) fun s => ?_
  have : (Mt ν i (s + 1) - Mt ν i s) = dd ν i s := by
    funext ω; simp [Mt, Finset.sum_range_succ]
  rw [this]
  exact condExp_dd ν π i s


lemma inv_sq_sum_aux (r : ℝ) (hr : 0 < r) (N : ℕ) :
    (∑ j ∈ Finset.range N, if r ≤ (j : ℝ) + 1 then 1 / ((j : ℝ) + 1) ^ 2 else 0)
      + 2 / max ((N : ℝ) + 1) r ≤ 2 / r := by
  induction N with
  | zero =>
    simp only [Finset.range_zero, Finset.sum_empty, Nat.cast_zero, zero_add]
    have : r ≤ max 1 r := le_max_right _ _
    have h1 : 2 / max 1 r ≤ 2 / r := div_le_div_of_nonneg_left (by norm_num) hr this
    linarith
  | succ N ih =>
    rw [Finset.sum_range_succ]
    push_cast
    have hN : (0 : ℝ) < (N : ℝ) + 1 := by positivity
    by_cases h : r ≤ (N : ℝ) + 1
    · rw [if_pos h]
      rw [max_eq_left h] at ih
      have hm : max ((N : ℝ) + 1 + 1) r = (N : ℝ) + 1 + 1 := max_eq_left (by linarith)
      rw [hm]
      have : 1 / ((N : ℝ) + 1) ^ 2 + 2 / ((N : ℝ) + 1 + 1) ≤ 2 / ((N : ℝ) + 1) := by
        rw [div_add_div _ _ (by positivity) (by positivity), div_le_div_iff₀ (by positivity) (by positivity)]
        nlinarith [hN]
      linarith
    · rw [if_neg h]
      push_neg at h
      rw [max_eq_right h.le] at ih
      have : max ((N : ℝ) + 1 + 1) r ≥ r := le_max_right _ _
      have h1 : 2 / max ((N : ℝ) + 1 + 1) r ≤ 2 / r := div_le_div_of_nonneg_left (by norm_num) hr this
      linarith

lemma tr_sq_sum (x : ℝ) (N : ℕ) :
    ∑ j ∈ Finset.range N, (tr x (j + 1)) ^ 2 / ((j : ℝ) + 1) ^ 2 ≤ 2 * |x| := by
  rcases eq_or_lt_of_le (abs_nonneg x) with h0 | hpos
  · have : x = 0 := abs_eq_zero.mp h0.symm
    subst this
    simp [tr]
  · have key := inv_sq_sum_aux |x| hpos N
    have hmax : (0 : ℝ) ≤ 2 / max ((N : ℝ) + 1) |x| := by positivity
    have hS : (∑ j ∈ Finset.range N, if |x| ≤ (j : ℝ) + 1 then 1 / ((j : ℝ) + 1) ^ 2 else 0) ≤ 2 / |x| := by
      linarith
    have heq : ∑ j ∈ Finset.range N, (tr x (j + 1)) ^ 2 / ((j : ℝ) + 1) ^ 2 =
        x ^ 2 * ∑ j ∈ Finset.range N, (if |x| ≤ (j : ℝ) + 1 then 1 / ((j : ℝ) + 1) ^ 2 else 0) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      unfold tr
      push_cast
      split_ifs <;> simp [div_eq_mul_inv]
    rw [heq]
    calc x ^ 2 * _ ≤ x ^ 2 * (2 / |x|) := mul_le_mul_of_nonneg_left hS (sq_nonneg x)
      _ = 2 * |x| := by
        rw [← sq_abs x]; field_simp


lemma count_aux (r : ℝ) (hr : 0 ≤ r) (N : ℕ) :
    (∑ j ∈ Finset.range N, (if (j : ℝ) + 1 < r then (1 : ℝ) else 0) = N ∧ (N : ℝ) ≤ r) ∨
    ((∑ j ∈ Finset.range N, (if (j : ℝ) + 1 < r then (1 : ℝ) else 0)) + 1 ≤ N ∧
      (∑ j ∈ Finset.range N, (if (j : ℝ) + 1 < r then (1 : ℝ) else 0)) ≤ r ∧
      r ≤ (∑ j ∈ Finset.range N, (if (j : ℝ) + 1 < r then (1 : ℝ) else 0)) + 1) := by
  induction N with
  | zero => left; simp [hr]
  | succ N ih =>
    rw [Finset.sum_range_succ]
    push_cast
    rcases ih with ⟨h1, h2⟩ | ⟨h1, h2, h3⟩
    · by_cases h : (N : ℝ) + 1 < r
      · left; rw [if_pos h, h1]; exact ⟨rfl, h.le⟩
      · right; rw [if_neg h, h1]; push_neg at h
        refine ⟨by linarith, by linarith, by linarith⟩
    · right
      have : ¬ ((N : ℝ) + 1 < r) := by
        intro h; linarith
      rw [if_neg this]
      refine ⟨by linarith, by linarith, by linarith⟩

lemma count_le (x : ℝ) (N : ℕ) :
    ∑ j ∈ Finset.range N, (if (j : ℝ) + 1 < |x| then (1 : ℝ) else 0) ≤ |x| := by
  rcases count_aux |x| (abs_nonneg x) N with ⟨h1, h2⟩ | ⟨h1, h2, h3⟩
  · linarith
  · exact h2


/-- second moment weight -/
noncomputable def gg (c : ℕ) : ℝ := (∫ x, (tr x (c + 1)) ^ 2 ∂(ν.P i)) / ((c : ℝ) + 1) ^ 2

/-- tail probability weight -/
noncomputable def bb (c : ℕ) : ℝ := (ν.P i).real {x | (c : ℝ) + 1 < |x|}

lemma integrable_tr_sq (c : ℕ) : Integrable (fun x => (tr x c) ^ 2) (ν.P i) :=
  integrable_of_bdd _ _ ((measurable_tr c).pow_const 2) ((c : ℝ) ^ 2) (fun x => by
    rw [abs_pow]; exact pow_le_pow_left₀ (abs_nonneg _) (abs_tr_le x c) 2)

lemma gg_nonneg (c : ℕ) : 0 ≤ gg ν i c := by
  unfold gg; positivity

lemma gg_partial (hint : Integrable id (ν.P i)) (N : ℕ) :
    ∑ j ∈ Finset.range N, gg ν i j ≤ 2 * ∫ x, |x| ∂(ν.P i) := by
  unfold gg
  have h1 : ∀ j ∈ Finset.range N, (∫ x, (tr x (j + 1)) ^ 2 ∂(ν.P i)) / ((j : ℝ) + 1) ^ 2 =
      ∫ x, (tr x (j + 1)) ^ 2 / ((j : ℝ) + 1) ^ 2 ∂(ν.P i) := fun j _ => by
    rw [integral_div]
  rw [Finset.sum_congr rfl h1, ← integral_finset_sum]
  · rw [← integral_const_mul]
    refine integral_mono ?_ ?_ (fun x => tr_sq_sum x N)
    · exact integrable_finset_sum _ fun j _ => (integrable_tr_sq ν i (j + 1)).div_const _
    · exact hint.abs.const_mul 2
  · exact fun j _ => (integrable_tr_sq ν i (j + 1)).div_const _

lemma summable_gg (hint : Integrable id (ν.P i)) : Summable (gg ν i) :=
  summable_of_sum_range_le (gg_nonneg ν i) (gg_partial ν i hint)

lemma bb_partial (hint : Integrable id (ν.P i)) (N : ℕ) :
    ∑ j ∈ Finset.range N, bb ν i j ≤ ∫ x, |x| ∂(ν.P i) := by
  have h1 : ∀ j ∈ Finset.range N, bb ν i j =
      ∫ x, (if (j : ℝ) + 1 < |x| then (1 : ℝ) else 0) ∂(ν.P i) := fun j _ => by
    unfold bb
    have hs : MeasurableSet {x : ℝ | (j : ℝ) + 1 < |x|} := measurableSet_lt measurable_const measurable_abs
    have := integral_indicator_one (μ := ν.P i) hs
    rw [← this]
    congr 1
  have hm : ∀ j : ℕ, Measurable (fun x : ℝ => if (j : ℝ) + 1 < |x| then (1 : ℝ) else 0) := fun j =>
    Measurable.ite (measurableSet_lt measurable_const measurable_abs) measurable_const measurable_const
  have hi : ∀ j : ℕ, Integrable (fun x : ℝ => if (j : ℝ) + 1 < |x| then (1 : ℝ) else 0) (ν.P i) :=
    fun j => integrable_of_bdd _ _ (hm j) 1 (fun x => by split_ifs <;> simp)
  rw [Finset.sum_congr rfl h1, ← integral_finset_sum _ (fun j _ => hi j)]
  exact integral_mono (integrable_finset_sum _ fun j _ => hi j) hint.abs (fun x => count_le x N)

lemma bb_nonneg (c : ℕ) : 0 ≤ bb ν i c := measureReal_nonneg

lemma summable_bb (hint : Integrable id (ν.P i)) : Summable (bb ν i) :=
  summable_of_sum_range_le (bb_nonneg ν i) (bb_partial ν i hint)

lemma gg_le_one (c : ℕ) : gg ν i c ≤ 1 := by
  unfold gg
  have hc : (0 : ℝ) < ((c : ℝ) + 1) ^ 2 := by positivity
  rw [div_le_one hc]
  have : ∫ x, (tr x (c + 1)) ^ 2 ∂(ν.P i) ≤ ∫ _x, (((c + 1 : ℕ) : ℝ)) ^ 2 ∂(ν.P i) :=
    integral_mono (integrable_tr_sq ν i (c + 1)) (integrable_const _) (fun x => by
      simp only
      rw [← sq_abs (tr x (c + 1))]
      exact pow_le_pow_left₀ (abs_nonneg _) (abs_tr_le x (c + 1)) 2)
  simpa using this

lemma Ffun_sq_le (c : ℕ) : ∫ x, (Ffun ν i c x) ^ 2 ∂(ν.P i) ≤ gg ν i c := by
  have hX : AEMeasurable (fun x => tr x (c + 1)) (ν.P i) := (measurable_tr _).aemeasurable
  have hv := variance_eq_integral hX
  have hle := variance_le_expectation_sq (μ := ν.P i) (X := fun x => tr x (c + 1))
    (measurable_tr _).aestronglyMeasurable
  have heq : ∫ x, (Ffun ν i c x) ^ 2 ∂(ν.P i) =
      (∫ x, (tr x (c + 1) - ∫ x', tr x' (c + 1) ∂(ν.P i)) ^ 2 ∂(ν.P i)) / ((c : ℝ) + 1) ^ 2 := by
    rw [← integral_div]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    simp only [Ffun, mtr, div_pow]
  rw [heq]
  unfold gg
  refine div_le_div_of_nonneg_right ?_ (by positivity)
  rw [← hv]
  simpa [Pi.pow_apply] using hle

lemma integrable_inner {k : ℕ} (ν : StochasticBandit k) (π : BanditPolicy k) (n : ℕ)
    (g : BanditHistory k n × (Fin k × ℝ) → ℝ) (hg : Measurable g) (C : ℝ) (hC : ∀ z, |g z| ≤ C) :
    Integrable (fun ω => ∫ y, g (banditTrajPrefix k n ω, y)
        ∂(banditStepKernel ν π n (banditTrajPrefix k n ω))) (banditTrajMeasure ν π) := by
  have hφm : Measurable (fun h : BanditHistory k n => ∫ y, g (h, y) ∂(banditStepKernel ν π n h)) :=
    hg.stronglyMeasurable.integral_kernel_prod_right'.measurable
  refine integrable_of_bdd _ _ (hφm.comp measurable_banditTrajPrefix) C (fun ω => ?_)
  have := norm_integral_le_of_norm_le_const
    (μ := banditStepKernel ν π n (banditTrajPrefix k n ω)) (f := fun y => g (banditTrajPrefix k n ω, y))
    (C := C) (Filter.Eventually.of_forall fun y => by simpa [Real.norm_eq_abs] using hC _)
  simpa [Real.norm_eq_abs] using this

lemma measurable_ite_gg {n : ℕ} :
    Measurable (fun p : BanditHistory k n × (Fin k × ℝ) =>
      if p.2.1 = i then gg ν i (armPullCount i p.1) else 0) := by
  refine Measurable.ite ?_ ?_ measurable_const
  · exact (measurable_fst.comp measurable_snd) (measurableSet_singleton i)
  · exact (measurable_from_nat (f := fun c : ℕ => gg ν i c)).comp ((measurable_armPullCount i).comp measurable_fst)

lemma step_sq_le (n : ℕ) (h : BanditHistory k n) :
    ∫ y, (Dfun ν i h y) ^ 2 ∂(banditStepKernel ν π n h) ≤
      ∫ y, (if y.1 = i then gg ν i (armPullCount i h) else 0) ∂(banditStepKernel ν π n h) := by
  rw [integral_step ν π n h (fun y => (Dfun ν i h y) ^ 2)
    (((measurable_Dfun ν i).comp (measurable_const.prodMk measurable_id)).pow_const 2) 4
    (fun z => by
      have := abs_Dfun_le ν i h z
      rw [abs_pow]; nlinarith [abs_nonneg (Dfun ν i h z)]),
    integral_step ν π n h (fun y => if y.1 = i then gg ν i (armPullCount i h) else 0)
    (Measurable.ite ((measurable_fst) (measurableSet_singleton i)) measurable_const measurable_const) 1
    (fun z => by
      split_ifs
      · rw [abs_of_nonneg (gg_nonneg ν i _)]; exact gg_le_one ν i _
      · simp)]
  refine integral_mono (Integrable.of_finite) (Integrable.of_finite) (fun a => ?_)
  by_cases ha : a = i
  · subst ha
    simp only [Dfun_eq, if_true]
    rw [integral_const]
    simp only [probReal_univ, one_smul]
    exact Ffun_sq_le ν a _
  · simp [Dfun_eq, ha]

noncomputable def g1 {n : ℕ} : BanditHistory k n × (Fin k × ℝ) → ℝ := fun z => (Dfun ν i z.1 z.2) ^ 2

noncomputable def g2 {n : ℕ} : BanditHistory k n × (Fin k × ℝ) → ℝ :=
  fun z => if z.2.1 = i then gg ν i (armPullCount i z.1) else 0

lemma measurable_g1 {n : ℕ} : Measurable (g1 ν i (n := n)) := (measurable_Dfun ν i).pow_const 2

lemma measurable_g2 {n : ℕ} : Measurable (g2 ν i (n := n)) := measurable_ite_gg ν i

lemma abs_g1_le {n : ℕ} (z : BanditHistory k n × (Fin k × ℝ)) : |g1 ν i z| ≤ 4 := by
  have := abs_Dfun_le ν i z.1 z.2
  unfold g1
  simp only [abs_pow]; nlinarith [abs_nonneg (Dfun ν i z.1 z.2)]

lemma abs_g2_le {n : ℕ} (z : BanditHistory k n × (Fin k × ℝ)) : |g2 ν i z| ≤ 1 := by
  unfold g2
  split_ifs
  · rw [abs_of_nonneg (gg_nonneg ν i _)]; exact gg_le_one ν i _
  · simp

lemma E_dd_sq_le (s : ℕ) :
    ∫ ω, (dd ν i s ω) ^ 2 ∂(banditTrajMeasure ν π) ≤
      ∫ ω, (if (ω s).1 = i then gg ν i (cntp i s ω) else 0) ∂(banditTrajMeasure ν π) := by
  have h1 := integral_pair ν π s (g1 ν i) (measurable_g1 ν i)
    (integrable_of_bdd _ _ ((measurable_g1 ν i).comp (measurable_pair s)) 4 (fun ω => abs_g1_le ν i _))
  have h2 := integral_pair ν π s (g2 ν i) (measurable_g2 ν i)
    (integrable_of_bdd _ _ ((measurable_g2 ν i).comp (measurable_pair s)) 1 (fun ω => abs_g2_le ν i _))
  have e1 : ∫ ω, (dd ν i s ω) ^ 2 ∂(banditTrajMeasure ν π) =
      ∫ ω, g1 ν i (banditTrajPrefix k s ω, ω s) ∂(banditTrajMeasure ν π) := rfl
  have e2 : ∫ ω, (if (ω s).1 = i then gg ν i (cntp i s ω) else 0) ∂(banditTrajMeasure ν π) =
      ∫ ω, g2 ν i (banditTrajPrefix k s ω, ω s) ∂(banditTrajMeasure ν π) := rfl
  rw [e1, e2, h1, h2]
  refine integral_mono (integrable_inner ν π s (g1 ν i) (measurable_g1 ν i) 4 (abs_g1_le ν i))
    (integrable_inner ν π s (g2 ν i) (measurable_g2 ν i) 1 (abs_g2_le ν i)) (fun ω => ?_)
  exact step_sq_le ν π i s _

lemma sum_pull (G : ℕ → ℝ) (t : ℕ) (ω : ℕ → Fin k × ℝ) :
    ∑ s ∈ Finset.range t, (if (ω s).1 = i then G (cntp i s ω) else 0) =
      ∑ j ∈ Finset.range (cntp i t ω), G j := by
  induction t with
  | zero => simp [cntp_eq]
  | succ t ih =>
    rw [Finset.sum_range_succ, ih, cntp_succ]
    by_cases h : (ω t).1 = i
    · simp [h, Finset.sum_range_succ]
    · simp [h]

lemma abs_Mt_le (t : ℕ) (ω : ℕ → Fin k × ℝ) : |Mt ν i t ω| ≤ 2 * t := by
  unfold Mt
  calc |∑ s ∈ Finset.range t, dd ν i s ω| ≤ ∑ s ∈ Finset.range t, |dd ν i s ω| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ s ∈ Finset.range t, (2 : ℝ) := Finset.sum_le_sum fun s _ => abs_dd_le ν i s ω
    _ = 2 * t := by simp [mul_comm]

lemma integrable_dd (s : ℕ) : Integrable (dd ν i s) (banditTrajMeasure ν π) :=
  integrable_of_bdd _ _ (measurable_dd ν i s) 2 (abs_dd_le ν i s)

lemma Mt_mul_dd_integral (t : ℕ) :
    ∫ ω, Mt ν i t ω * dd ν i t ω ∂(banditTrajMeasure ν π) = 0 := by
  have hint : Integrable (fun ω => Mt ν i t ω * dd ν i t ω) (banditTrajMeasure ν π) :=
    integrable_of_bdd _ _ ((measurable_Mt ν i t).mul (measurable_dd ν i t)) (2 * t * 2) (fun ω => by
      rw [abs_mul]
      exact mul_le_mul (abs_Mt_le ν i t ω) (abs_dd_le ν i t ω) (abs_nonneg _) (by positivity))
  have h1 := condExp_mul_of_stronglyMeasurable_left (μ := banditTrajMeasure ν π)
    (m := banditFiltration k t) (stronglyAdapted_Mt ν i t) hint (integrable_dd ν π i t)
  have h2 := condExp_dd ν π i t
  rw [← integral_condExp ((banditFiltration k).le t)]
  have : (banditTrajMeasure ν π)[fun ω => Mt ν i t ω * dd ν i t ω | banditFiltration k t]
      =ᵐ[banditTrajMeasure ν π] 0 := by
    filter_upwards [h1, h2] with ω hω1 hω2
    have hω1' : ((banditTrajMeasure ν π)[fun ω => Mt ν i t ω * dd ν i t ω | banditFiltration k t]) ω =
        Mt ν i t ω * ((banditTrajMeasure ν π)[dd ν i t | banditFiltration k t]) ω := hω1
    rw [hω1', hω2]; simp
  rw [integral_congr_ae this]; simp

lemma second_moment_eq (t : ℕ) :
    ∫ ω, (Mt ν i t ω) ^ 2 ∂(banditTrajMeasure ν π) =
      ∑ s ∈ Finset.range t, ∫ ω, (dd ν i s ω) ^ 2 ∂(banditTrajMeasure ν π) := by
  induction t with
  | zero => simp [Mt]
  | succ t ih =>
    rw [Finset.sum_range_succ, ← ih]
    have e : ∀ ω, (Mt ν i (t + 1) ω) ^ 2 =
        (Mt ν i t ω) ^ 2 + 2 * (Mt ν i t ω * dd ν i t ω) + (dd ν i t ω) ^ 2 := by
      intro ω; simp only [Mt, Finset.sum_range_succ]; ring
    simp_rw [e]
    have i1 : Integrable (fun ω => (Mt ν i t ω) ^ 2) (banditTrajMeasure ν π) :=
      integrable_of_bdd _ _ ((measurable_Mt ν i t).pow_const 2) ((2 * t) ^ 2) (fun ω => by
        rw [abs_pow]; exact pow_le_pow_left₀ (abs_nonneg _) (abs_Mt_le ν i t ω) 2)
    have i2 : Integrable (fun ω => Mt ν i t ω * dd ν i t ω) (banditTrajMeasure ν π) :=
      integrable_of_bdd _ _ ((measurable_Mt ν i t).mul (measurable_dd ν i t)) (2 * t * 2) (fun ω => by
        rw [abs_mul]
        exact mul_le_mul (abs_Mt_le ν i t ω) (abs_dd_le ν i t ω) (abs_nonneg _) (by positivity))
    have i3 : Integrable (fun ω => (dd ν i t ω) ^ 2) (banditTrajMeasure ν π) :=
      integrable_of_bdd _ _ ((measurable_dd ν i t).pow_const 2) (2 ^ 2) (fun ω => by
        rw [abs_pow]; exact pow_le_pow_left₀ (abs_nonneg _) (abs_dd_le ν i t ω) 2)
    have h12 : Integrable (fun ω => (Mt ν i t ω) ^ 2 + 2 * (Mt ν i t ω * dd ν i t ω))
        (banditTrajMeasure ν π) := i1.add (i2.const_mul 2)
    rw [integral_add h12 i3, integral_add i1 (i2.const_mul 2),
      integral_const_mul, Mt_mul_dd_integral ν π i t]
    ring

lemma second_moment_le (hint : Integrable id (ν.P i)) (t : ℕ) :
    ∫ ω, (Mt ν i t ω) ^ 2 ∂(banditTrajMeasure ν π) ≤ ∑' j, gg ν i j := by
  rw [second_moment_eq]
  have hle : ∑ s ∈ Finset.range t, ∫ ω, (dd ν i s ω) ^ 2 ∂(banditTrajMeasure ν π) ≤
      ∑ s ∈ Finset.range t, ∫ ω, (if (ω s).1 = i then gg ν i (cntp i s ω) else 0)
        ∂(banditTrajMeasure ν π) :=
    Finset.sum_le_sum fun s _ => E_dd_sq_le ν π i s
  refine hle.trans ?_
  have hi : ∀ s, Integrable (fun ω : ℕ → Fin k × ℝ => (if (ω s).1 = i then gg ν i (cntp i s ω) else 0))
      (banditTrajMeasure ν π) := by
    intro s
    have := integrable_of_bdd (banditTrajMeasure ν π) _
      ((measurable_g2 ν i (n := s)).comp (measurable_pair s)) 1 (fun ω => abs_g2_le ν i _)
    exact this
  rw [← integral_finset_sum _ (fun s _ => hi s)]
  have : ∀ ω : ℕ → Fin k × ℝ, ∑ s ∈ Finset.range t, (if (ω s).1 = i then gg ν i (cntp i s ω) else 0) ≤ ∑' j, gg ν i j := by
    intro ω
    rw [sum_pull i]
    exact (summable_gg ν i hint).sum_le_tsum _ (fun j _ => gg_nonneg ν i j)
  calc _ ≤ ∫ _ω, (∑' j, gg ν i j) ∂(banditTrajMeasure ν π) :=
        integral_mono (integrable_finset_sum _ fun s _ => hi s) (integrable_const _) this
    _ = ∑' j, gg ν i j := by simp

lemma eLpNorm_Mt_le (hint : Integrable id (ν.P i)) (t : ℕ) :
    eLpNorm (Mt ν i t) 1 (banditTrajMeasure ν π) ≤ ((1 + ∑' j, gg ν i j).toNNReal : ENNReal) := by
  have hI : Integrable (Mt ν i t) (banditTrajMeasure ν π) := integrable_Mt ν π i t
  have hI2 : Integrable (fun ω => (Mt ν i t ω) ^ 2) (banditTrajMeasure ν π) :=
    integrable_of_bdd _ _ ((measurable_Mt ν i t).pow_const 2) ((2 * t) ^ 2) (fun ω => by
      rw [abs_pow]; exact pow_le_pow_left₀ (abs_nonneg _) (abs_Mt_le ν i t ω) 2)
  have hI3 : Integrable (fun ω => 1 + (Mt ν i t ω) ^ 2) (banditTrajMeasure ν π) :=
    (integrable_const (1 : ℝ)).add hI2
  rw [eLpNorm_one_eq_lintegral_enorm, ← ofReal_integral_norm_eq_lintegral_enorm hI]
  have h1 : ∫ ω, ‖Mt ν i t ω‖ ∂(banditTrajMeasure ν π) ≤ 1 + ∑' j, gg ν i j := by
    calc ∫ ω, ‖Mt ν i t ω‖ ∂(banditTrajMeasure ν π)
        ≤ ∫ ω, (1 + (Mt ν i t ω) ^ 2) ∂(banditTrajMeasure ν π) :=
          integral_mono hI.norm hI3 (fun ω => by
            simp only [Real.norm_eq_abs]
            nlinarith [sq_abs (Mt ν i t ω), abs_nonneg (Mt ν i t ω), sq_nonneg (|Mt ν i t ω| - 1)])
      _ = 1 + ∫ ω, (Mt ν i t ω) ^ 2 ∂(banditTrajMeasure ν π) := by
          rw [integral_add (integrable_const (1 : ℝ)) hI2]; simp
      _ ≤ 1 + ∑' j, gg ν i j := by
          have := second_moment_le ν π i hint t
          linarith
  calc ENNReal.ofReal (∫ ω, ‖Mt ν i t ω‖ ∂(banditTrajMeasure ν π))
      ≤ ENNReal.ofReal (1 + ∑' j, gg ν i j) := ENNReal.ofReal_le_ofReal h1
    _ = ((1 + ∑' j, gg ν i j).toNNReal : ENNReal) := rfl

lemma Mt_converges (hint : Integrable id (ν.P i)) :
    ∀ᵐ ω ∂(banditTrajMeasure ν π), ∃ c, Tendsto (fun t => Mt ν i t ω) atTop (𝓝 c) :=
  (martingale_Mt ν π i).submartingale.exists_ae_tendsto_of_bdd (eLpNorm_Mt_le ν π i hint)

/-- exceedance indicator -/
noncomputable def g3 {n : ℕ} : BanditHistory k n × (Fin k × ℝ) → ℝ :=
  fun z => if z.2.1 = i ∧ (armPullCount i z.1 : ℝ) + 1 < |z.2.2| then 1 else 0

noncomputable def g4 {n : ℕ} : BanditHistory k n × (Fin k × ℝ) → ℝ :=
  fun z => if z.2.1 = i then bb ν i (armPullCount i z.1) else 0

lemma measurable_g3 {n : ℕ} : Measurable (g3 i (n := n)) := by
  unfold g3
  refine Measurable.ite ?_ measurable_const measurable_const
  refine MeasurableSet.inter ?_ ?_
  · exact (measurable_fst.comp measurable_snd) (measurableSet_singleton i)
  · exact measurableSet_lt
      ((measurable_from_nat (f := fun c : ℕ => (c : ℝ) + 1)).comp
        ((measurable_armPullCount i).comp measurable_fst))
      (measurable_abs.comp (measurable_snd.comp measurable_snd))

lemma measurable_g4 {n : ℕ} : Measurable (g4 ν i (n := n)) := by
  unfold g4
  refine Measurable.ite ?_ ?_ measurable_const
  · exact (measurable_fst.comp measurable_snd) (measurableSet_singleton i)
  · exact (measurable_from_nat (f := fun c : ℕ => bb ν i c)).comp ((measurable_armPullCount i).comp measurable_fst)

lemma abs_g3_le {n : ℕ} (z : BanditHistory k n × (Fin k × ℝ)) : |g3 i z| ≤ 1 := by
  unfold g3; split_ifs <;> simp

lemma bb_le_one (c : ℕ) : bb ν i c ≤ 1 := by
  unfold bb; exact measureReal_le_one

lemma abs_g4_le {n : ℕ} (z : BanditHistory k n × (Fin k × ℝ)) : |g4 ν i z| ≤ 1 := by
  unfold g4; split_ifs
  · rw [abs_of_nonneg (bb_nonneg ν i _)]; exact bb_le_one ν i _
  · simp

lemma step_g3_g4 (n : ℕ) (h : BanditHistory k n) :
    ∫ y, g3 i (h, y) ∂(banditStepKernel ν π n h) = ∫ y, g4 ν i (h, y) ∂(banditStepKernel ν π n h) := by
  rw [integral_step ν π n h (fun y => g3 i (h, y))
    ((measurable_g3 i).comp (measurable_const.prodMk measurable_id)) 1 (fun z => abs_g3_le i _),
    integral_step ν π n h (fun y => g4 ν i (h, y))
    ((measurable_g4 ν i).comp (measurable_const.prodMk measurable_id)) 1 (fun z => abs_g4_le ν i _)]
  refine integral_congr_ae (Filter.Eventually.of_forall fun a => ?_)
  by_cases ha : a = i
  · subst ha
    simp only [g3, g4, true_and, if_true]
    have hs : MeasurableSet {x : ℝ | (armPullCount a h : ℝ) + 1 < |x|} :=
      measurableSet_lt measurable_const measurable_abs
    have := integral_indicator_one (μ := ν.P a) hs
    rw [integral_const, probReal_univ, one_smul]
    unfold bb
    rw [← this]
    congr 1
  · simp [g3, g4, ha]

/-- exceedance along a path -/
noncomputable def ee (s : ℕ) (ω : ℕ → Fin k × ℝ) : ℝ := g3 i (banditTrajPrefix k s ω, ω s)

lemma measurable_ee (s : ℕ) : Measurable (ee i s (k := k)) := (measurable_g3 i).comp (measurable_pair s)

lemma ee_nonneg (s : ℕ) (ω : ℕ → Fin k × ℝ) : 0 ≤ ee i s ω := by
  unfold ee g3; split_ifs <;> simp

lemma ee_eq (s : ℕ) (ω : ℕ → Fin k × ℝ) :
    ee i s ω = if (ω s).1 = i ∧ (cntp i s ω : ℝ) + 1 < |(ω s).2| then 1 else 0 := rfl

lemma E_ee (s : ℕ) :
    ∫ ω, ee i s ω ∂(banditTrajMeasure ν π) =
      ∫ ω, (if (ω s).1 = i then bb ν i (cntp i s ω) else 0) ∂(banditTrajMeasure ν π) := by
  have h1 := integral_pair ν π s (g3 i) (measurable_g3 i)
    (integrable_of_bdd _ _ ((measurable_g3 i).comp (measurable_pair s)) 1 (fun ω => abs_g3_le i _))
  have h2 := integral_pair ν π s (g4 ν i) (measurable_g4 ν i)
    (integrable_of_bdd _ _ ((measurable_g4 ν i).comp (measurable_pair s)) 1 (fun ω => abs_g4_le ν i _))
  have e1 : ∫ ω, ee i s ω ∂(banditTrajMeasure ν π) =
      ∫ ω, g3 i (banditTrajPrefix k s ω, ω s) ∂(banditTrajMeasure ν π) := rfl
  have e2 : ∫ ω, (if (ω s).1 = i then bb ν i (cntp i s ω) else 0) ∂(banditTrajMeasure ν π) =
      ∫ ω, g4 ν i (banditTrajPrefix k s ω, ω s) ∂(banditTrajMeasure ν π) := rfl
  rw [e1, e2, h1, h2]
  exact integral_congr_ae (Filter.Eventually.of_forall fun ω => step_g3_g4 ν π i s _)

/-- cumulative exceedances -/
noncomputable def Zt (t : ℕ) (ω : ℕ → Fin k × ℝ) : ℝ := ∑ s ∈ Finset.range t, ee i s ω

lemma ee_01 (s : ℕ) (ω : ℕ → Fin k × ℝ) : ee i s ω = 0 ∨ ee i s ω = 1 := by
  unfold ee g3; split_ifs <;> simp

lemma Zt_mono (ω : ℕ → Fin k × ℝ) : Monotone (fun t => Zt i t ω) := by
  refine monotone_nat_of_le_succ fun t => ?_
  simp only [Zt, Finset.sum_range_succ]
  linarith [ee_nonneg i t ω]

lemma measurable_Zt (t : ℕ) : Measurable (Zt i t (k := k)) :=
  Finset.measurable_sum _ fun s _ => measurable_ee i s

lemma integral_Zt_le (hint : Integrable id (ν.P i)) (t : ℕ) :
    ∫ ω, Zt i t ω ∂(banditTrajMeasure ν π) ≤ ∑' j, bb ν i j := by
  have hi : ∀ s, Integrable (fun ω : ℕ → Fin k × ℝ => ee i s ω) (banditTrajMeasure ν π) := fun s =>
    integrable_of_bdd _ _ (measurable_ee i s) 1 (fun ω => by
      unfold ee; exact abs_g3_le i _)
  have hi2 : ∀ s, Integrable (fun ω : ℕ → Fin k × ℝ => (if (ω s).1 = i then bb ν i (cntp i s ω) else 0))
      (banditTrajMeasure ν π) := fun s =>
    integrable_of_bdd _ _ ((measurable_g4 ν i (n := s)).comp (measurable_pair s)) 1
      (fun ω => abs_g4_le ν i (banditTrajPrefix k s ω, ω s))
  have e : ∫ ω, Zt i t ω ∂(banditTrajMeasure ν π) =
      ∫ ω, ∑ s ∈ Finset.range t, (if (ω s).1 = i then bb ν i (cntp i s ω) else 0) ∂(banditTrajMeasure ν π) := by
    unfold Zt
    rw [integral_finset_sum _ (fun s _ => hi s), integral_finset_sum _ (fun s _ => hi2 s)]
    exact Finset.sum_congr rfl fun s _ => E_ee ν π i s
  rw [e]
  have : ∀ ω : ℕ → Fin k × ℝ, ∑ s ∈ Finset.range t, (if (ω s).1 = i then bb ν i (cntp i s ω) else 0) ≤ ∑' j, bb ν i j := by
    intro ω
    rw [sum_pull i]
    exact (summable_bb ν i hint).sum_le_tsum _ (fun j _ => bb_nonneg ν i j)
  calc _ ≤ ∫ _ω, (∑' j, bb ν i j) ∂(banditTrajMeasure ν π) :=
        integral_mono (integrable_finset_sum _ fun s _ => hi2 s) (integrable_const _) this
    _ = ∑' j, bb ν i j := by simp

lemma ee_eventually_zero (hint : Integrable id (ν.P i)) :
    ∀ᵐ ω ∂(banditTrajMeasure ν π), ∀ᶠ s in atTop, ee i s ω = 0 := by
  have hF : ∀ t, Measurable (fun ω => ENNReal.ofReal (Zt i t ω)) := fun t =>
    ENNReal.measurable_ofReal.comp (measurable_Zt i t)
  have hmono : Monotone (fun t ω => ENNReal.ofReal (Zt i t ω)) := fun a b hab ω =>
    ENNReal.ofReal_le_ofReal (Zt_mono i ω hab)
  have hZnn : ∀ t ω, 0 ≤ Zt i t ω := fun t ω => Finset.sum_nonneg fun s _ => ee_nonneg i s ω
  have hlint : ∀ t, ∫⁻ ω, ENNReal.ofReal (Zt i t ω) ∂(banditTrajMeasure ν π) ≤
      ENNReal.ofReal (∑' j, bb ν i j) := by
    intro t
    have hI : Integrable (Zt i t) (banditTrajMeasure ν π) :=
      integrable_of_bdd _ _ (measurable_Zt i t) t (fun ω => by
        rw [abs_of_nonneg (hZnn t ω)]
        unfold Zt
        calc ∑ s ∈ Finset.range t, ee i s ω ≤ ∑ s ∈ Finset.range t, (1 : ℝ) :=
              Finset.sum_le_sum fun s _ => by
                rcases ee_01 i s ω with h | h <;> simp [h]
          _ = t := by simp)
    rw [← ofReal_integral_eq_lintegral_ofReal hI (Filter.Eventually.of_forall (hZnn t))]
    exact ENNReal.ofReal_le_ofReal (integral_Zt_le ν π i hint t)
  have hsup : ∫⁻ ω, ⨆ t, ENNReal.ofReal (Zt i t ω) ∂(banditTrajMeasure ν π) ≠ ⊤ := by
    rw [lintegral_iSup hF hmono]
    exact ne_of_lt (lt_of_le_of_lt (iSup_le hlint) ENNReal.ofReal_lt_top)
  filter_upwards [ae_lt_top (Measurable.iSup hF) hsup] with ω hω
  have hbdd : BddAbove (Set.range fun t => Zt i t ω) := by
    refine ⟨(⨆ t, ENNReal.ofReal (Zt i t ω)).toReal, ?_⟩
    rintro _ ⟨t, rfl⟩
    have h1 : ENNReal.ofReal (Zt i t ω) ≤ ⨆ t, ENNReal.ofReal (Zt i t ω) := le_iSup (fun t => ENNReal.ofReal (Zt i t ω)) t
    have := ENNReal.toReal_mono hω.ne h1
    rwa [ENNReal.toReal_ofReal (hZnn t ω)] at this
  have hconv := tendsto_atTop_ciSup (Zt_mono i ω) hbdd
  have hdiff : Tendsto (fun s => Zt i (s + 1) ω - Zt i s ω) atTop (𝓝 0) := by
    have := (hconv.comp (tendsto_add_atTop_nat 1)).sub hconv
    simpa using this
  have hev : ∀ᶠ s in atTop, |Zt i (s + 1) ω - Zt i s ω| < 1 / 2 := by
    have h0 := hdiff.abs
    rw [abs_zero] at h0
    exact h0.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2))
  filter_upwards [hev] with s hs
  have : Zt i (s + 1) ω - Zt i s ω = ee i s ω := by simp [Zt, Finset.sum_range_succ]
  rw [this] at hs
  rcases ee_01 i s ω with h | h
  · exact h
  · rw [h] at hs; norm_num at hs

lemma mtr_tendsto (hint : Integrable id (ν.P i)) :
    Tendsto (fun j : ℕ => mtr ν i (j + 1)) atTop (𝓝 (banditArmMean ν i)) := by
  unfold mtr banditArmMean
  refine tendsto_integral_of_dominated_convergence (fun x => |x|)
    (fun j => (measurable_tr (j + 1)).aestronglyMeasurable) hint.abs ?_ ?_
  · intro j
    exact Filter.Eventually.of_forall fun x => by
      simpa [Real.norm_eq_abs] using abs_tr_le_abs x (j + 1)
  · refine Filter.Eventually.of_forall fun x => ?_
    refine tendsto_const_nhds.congr' ?_
    obtain ⟨N, hN⟩ := exists_nat_ge |x|
    filter_upwards [Filter.eventually_ge_atTop N] with j hj
    unfold tr
    rw [if_pos]
    have : (N : ℝ) ≤ j := by exact_mod_cast hj
    push_cast
    linarith

lemma cntp_mono (ω : ℕ → Fin k × ℝ) : Monotone (fun n => cntp i n ω) :=
  monotone_nat_of_le_succ fun n => by rw [cntp_succ]; omega

lemma dd_eq (s : ℕ) (ω : ℕ → Fin k × ℝ) :
    dd ν i s ω = (if (ω s).1 = i then tr (ω s).2 (cntp i s ω + 1) - mtr ν i (cntp i s ω + 1) else 0)
      / ((cntp i s ω : ℝ) + 1) := by
  unfold dd Dfun
  change (if (ω s).1 = i then _ else _) = _
  by_cases h : (ω s).1 = i
  · simp [h, cntp]
  · simp [h]

theorem arm_slln (hint : Integrable id (ν.P i)) :
    ∀ᵐ ω ∂(banditTrajMeasure ν π), Tendsto (fun n => cntp i n ω) atTop atTop →
      Tendsto (fun n => (∑ s ∈ Finset.range n, if (ω s).1 = i then (ω s).2 else 0) /
        (cntp i n ω : ℝ)) atTop (𝓝 (banditArmMean ν i)) := by
  filter_upwards [Mt_converges ν π i hint, ee_eventually_zero ν π i hint] with ω hconv hee hT
  obtain ⟨L, hL⟩ := hconv
  set μi := banditArmMean ν i with hμi
  have hc_top : Tendsto (fun n => (cntp i n ω : ℝ) + 1) atTop atTop :=
    tendsto_atTop_add_const_right _ _ (tendsto_natCast_atTop_atTop.comp hT)
  have hc_pos : ∀ n, 0 < (cntp i n ω : ℝ) + 1 := fun n => by positivity
  have hc_mono : Monotone (fun n => (cntp i n ω : ℝ) + 1) := fun a b hab => by
    have := cntp_mono i ω hab
    have : (cntp i a ω : ℝ) ≤ cntp i b ω := by exact_mod_cast this
    linarith
  set x : ℕ → ℝ := fun s => if (ω s).1 = i then tr (ω s).2 (cntp i s ω + 1) - mtr ν i (cntp i s ω + 1) else 0
    with hx
  have hMt : ∀ n, Mt ν i n ω = ∑ s ∈ Finset.range n, x s / ((cntp i s ω : ℝ) + 1) := by
    intro n; unfold Mt
    exact Finset.sum_congr rfl fun s _ => dd_eq ν i s ω
  have hK := kronecker x (fun n => (cntp i n ω : ℝ) + 1) hc_pos hc_mono hc_top L
    (by simpa [hMt] using hL)
  set P : ℕ → ℝ := fun n => ∑ s ∈ Finset.range n, if (ω s).1 = i then tr (ω s).2 (cntp i s ω + 1) else 0 with hP
  set Y : ℕ → ℝ := fun n => ∑ s ∈ Finset.range n, if (ω s).1 = i then (ω s).2 else 0 with hY
  set E : ℕ → ℝ := fun n => Y n - P n with hE
  have hxs : ∀ n, ∑ s ∈ Finset.range n, x s =
      P n - ∑ j ∈ Finset.range (cntp i n ω), mtr ν i (j + 1) := by
    intro n
    rw [← sum_pull i (fun j => mtr ν i (j + 1)) n ω, hP, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun s _ => ?_
    simp only [hx]
    split_ifs <;> ring
  -- E is eventually constant
  obtain ⟨s0, hs0⟩ := Filter.eventually_atTop.mp hee
  have hEconst : ∀ n, s0 ≤ n → E n = E s0 := by
    intro n hn
    induction n, hn using Nat.le_induction with
    | base => rfl
    | succ n hn ih =>
      rw [← ih]
      have h0 := hs0 n hn
      rw [ee_eq] at h0
      simp only [hE, hY, hP, Finset.sum_range_succ]
      by_cases hA : (ω n).1 = i
      · have : |(ω n).2| ≤ ((cntp i n ω + 1 : ℕ) : ℝ) := by
          by_contra hcon
          push_neg at hcon
          rw [if_pos ⟨hA, by push_cast at hcon; exact hcon⟩] at h0
          exact one_ne_zero h0
        have htr : tr (ω n).2 (cntp i n ω + 1) = (ω n).2 := by
          unfold tr; rw [if_pos this]
        simp [hA, htr]
      · simp [hA]
  have hE0 : Tendsto (fun n => E n / ((cntp i n ω : ℝ) + 1)) atTop (𝓝 0) := by
    have h1 : Tendsto (fun n => E s0 / ((cntp i n ω : ℝ) + 1)) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop hc_top
    refine h1.congr' ?_
    filter_upwards [Filter.eventually_ge_atTop s0] with n hn
    rw [hEconst n hn]
  have hces := (mtr_tendsto ν i hint).cesaro.comp hT
  have hratio : Tendsto (fun n => (cntp i n ω : ℝ) / ((cntp i n ω : ℝ) + 1)) atTop (𝓝 1) := by
    have h1 : Tendsto (fun n => 1 - 1 / ((cntp i n ω : ℝ) + 1)) atTop (𝓝 1) := by
      have := (tendsto_const_nhds (x := (1 : ℝ))).div_atTop hc_top
      simpa using (tendsto_const_nhds (x := (1 : ℝ))).sub this
    refine h1.congr fun n => ?_
    have := (hc_pos n).ne'
    field_simp
    ring
  have hmain : Tendsto (fun n => Y n / ((cntp i n ω : ℝ) + 1)) atTop (𝓝 μi) := by
    have h1 : Tendsto (fun n => (∑ s ∈ Finset.range n, x s) / ((cntp i n ω : ℝ) + 1) +
        ((cntp i n ω : ℝ) / ((cntp i n ω : ℝ) + 1)) *
          (((cntp i n ω : ℕ) : ℝ)⁻¹ * ∑ j ∈ Finset.range (cntp i n ω), mtr ν i (j + 1)) +
        E n / ((cntp i n ω : ℝ) + 1)) atTop (𝓝 (0 + 1 * μi + 0)) :=
      (hK.add (hratio.mul hces)).add hE0
    rw [show (0 + 1 * μi + 0 : ℝ) = μi by ring] at h1
    refine h1.congr' ?_
    filter_upwards [hT.eventually_gt_atTop 0] with n hn
    have hnpos : (0 : ℝ) < cntp i n ω := by exact_mod_cast hn
    have hb := (hc_pos n).ne'
    have hn' := hnpos.ne'
    have : Y n = (∑ s ∈ Finset.range n, x s) + (cntp i n ω : ℝ) * ((cntp i n ω : ℝ)⁻¹ *
        ∑ j ∈ Finset.range (cntp i n ω), mtr ν i (j + 1)) + E n := by
      rw [hxs n]
      simp only [hE]
      field_simp
      ring
    rw [this]
    field_simp
  have hfin : Tendsto (fun n => Y n / ((cntp i n ω : ℝ) + 1) * (((cntp i n ω : ℝ) + 1) / (cntp i n ω : ℝ)))
      atTop (𝓝 (μi * 1)) := by
    refine hmain.mul ?_
    have := hratio.inv₀ one_ne_zero
    simpa using this
  rw [mul_one] at hfin
  refine hfin.congr' ?_
  filter_upwards [hT.eventually_gt_atTop 0] with n hn
  have hnpos : (0 : ℝ) < cntp i n ω := by exact_mod_cast hn
  have hb := (hc_pos n).ne'
  field_simp
  rfl

end Arm


section Rule

variable (ν : StochasticBandit 2) (σ : ForcedSchedule)

lemma rule_choice_ae :
    ∀ᵐ ω ∂(banditTrajMeasure ν (rule σ)), ∀ n, (ω n).1 = ruleChoice σ n (banditTrajPrefix 2 n ω) := by
  rw [ae_all_iff]
  intro n
  let f : BanditHistory 2 n × (Fin 2 × ℝ) → ENNReal :=
    fun z => if z.2.1 = ruleChoice σ n z.1 then 0 else 1
  have hfm : Measurable f := by
    refine Measurable.ite ?_ measurable_const measurable_const
    exact measurableSet_eq_fun (measurable_fst.comp measurable_snd)
      ((measurable_ruleChoice σ n).comp measurable_fst)
  have key := lintegral_pair ν (rule σ) n f hfm
  have hinner : ∀ h : BanditHistory 2 n, ∫⁻ y, f (h, y) ∂(banditStepKernel ν (rule σ) n h) = 0 := by
    intro h
    unfold banditStepKernel
    rw [Kernel.lintegral_compProd _ _ h (f := fun y => f (h, y))
      (hfm.comp (measurable_const.prodMk measurable_id))]
    simp only [rule, Kernel.deterministic_apply]
    rw [lintegral_dirac' _ (measurable_of_finite _)]
    simp [f]
  simp only [hinner, lintegral_zero] at key
  have h0 : ∫⁻ ω, f (banditTrajPrefix 2 n ω, ω n) ∂(banditTrajMeasure ν (rule σ)) = 0 := key
  have hm2 : Measurable (fun ω : ℕ → Fin 2 × ℝ => f (banditTrajPrefix 2 n ω, ω n)) :=
    hfm.comp (measurable_pair n)
  have h0' := (lintegral_eq_zero_iff hm2).mp h0
  filter_upwards [h0'] with ω hω
  by_contra hne
  have : f (banditTrajPrefix 2 n ω, ω n) = 1 := by simp [f, hne]
  have h2 : f (banditTrajPrefix 2 n ω, ω n) = 0 := hω
  rw [this] at h2
  exact one_ne_zero h2

lemma emp_eq (i : Fin 2) (n : ℕ) (ω : ℕ → Fin 2 × ℝ) :
    armEmpiricalMean i (banditTrajPrefix 2 n ω) =
      (∑ s ∈ Finset.range n, if (ω s).1 = i then (ω s).2 else 0) / (cntp i n ω : ℝ) := by
  classical
  unfold armEmpiricalMean
  congr 1
  rw [Set.toFinset_ofPred, Finset.sum_filter]
  exact Fin.sum_univ_eq_sum_range (fun s => if (ω s).1 = i then (ω s).2 else 0) n

lemma tendsto_cntp_of_forced (i : Fin 2) (f : ℕ → ℕ) (hf : StrictMono f) (hf1 : ∀ j, 1 ≤ f j)
    (ω : ℕ → Fin 2 × ℝ) (hω : ∀ j, (ω (f j - 1)).1 = i) :
    Tendsto (fun n => cntp i n ω) atTop atTop := by
  rw [tendsto_atTop]
  intro M
  rw [Filter.eventually_atTop]
  refine ⟨f M, fun n hn => ?_⟩
  rw [cntp_eq]
  let T : Finset ℕ := (Finset.range M).image (fun j => f j - 1)
  have hinj : Set.InjOn (fun j => f j - 1) (Finset.range M : Set ℕ) := by
    intro a _ b _ hab
    have := hf1 a; have := hf1 b
    have : f a = f b := by simp only at hab; omega
    exact hf.injective this
  have hcard : T.card = M := by
    rw [Finset.card_image_of_injOn hinj]; simp
  have hsub : T ⊆ Finset.range n := by
    intro s hs
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hs
    have hj' : j < M := Finset.mem_range.mp hj
    have := hf hj'
    rw [Finset.mem_range]
    have := hf1 j
    omega
  calc M = ∑ s ∈ T, (if (ω s).1 = i then 1 else 0) := by
        rw [← hcard, Finset.card_eq_sum_ones]
        refine Finset.sum_congr rfl fun s hs => ?_
        obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hs
        simp [hω j]
    _ ≤ ∑ s ∈ Finset.range n, (if (ω s).1 = i then 1 else 0) :=
        Finset.sum_le_sum_of_subset hsub

lemma forced_a_ae : ∀ᵐ ω ∂(banditTrajMeasure ν (rule σ)),
    Tendsto (fun n => cntp 0 n ω) atTop atTop := by
  filter_upwards [rule_choice_ae ν σ] with ω hω
  refine tendsto_cntp_of_forced 0 σ.a σ.a_strictMono (fun j => ?_) ω (fun j => ?_)
  · have := σ.a_strictMono.monotone (Nat.zero_le j)
    rw [σ.a_zero] at this; exact this
  · rw [hω]
    unfold ruleChoice
    have h1 : σ.a j - 1 + 1 ∈ Set.range σ.a := by
      have := σ.a_strictMono.monotone (Nat.zero_le j)
      rw [σ.a_zero] at this
      exact ⟨j, by omega⟩
    simp [h1]

lemma forced_b_ae : ∀ᵐ ω ∂(banditTrajMeasure ν (rule σ)),
    Tendsto (fun n => cntp 1 n ω) atTop atTop := by
  filter_upwards [rule_choice_ae ν σ] with ω hω
  refine tendsto_cntp_of_forced 1 σ.b σ.b_strictMono (fun j => ?_) ω (fun j => ?_)
  · have := σ.b_strictMono.monotone (Nat.zero_le j)
    rw [σ.b_zero] at this; omega
  · rw [hω]
    unfold ruleChoice
    have h0 := σ.b_strictMono.monotone (Nat.zero_le j)
    rw [σ.b_zero] at h0
    have h1 : σ.b j - 1 + 1 ∈ Set.range σ.b := ⟨j, by omega⟩
    have h2 : σ.b j - 1 + 1 ∉ Set.range σ.a := by
      intro h
      exact Set.disjoint_left.mp σ.disjoint h h1
    simp [h1, h2]

open Classical in
lemma cnt_le_forced (c : Fin 2) (ω : ℕ → Fin 2 × ℝ) (N0 : ℕ)
    (hN : ∀ n, N0 ≤ n → (ω n).1 = c → n + 1 ∈ Set.range σ.a ∪ Set.range σ.b) (n : ℕ) :
    cntp c n ω ≤ N0 + ((Finset.Icc 1 n).filter (fun i => i ∈ Set.range σ.a ∪ Set.range σ.b)).card := by
  rw [cntp_eq]
  have h1 : ∑ s ∈ Finset.range n, (if (ω s).1 = c then 1 else 0) ≤
      ∑ s ∈ Finset.range n, ((if s < N0 then 1 else 0) +
        (if s + 1 ∈ Set.range σ.a ∪ Set.range σ.b then 1 else 0)) := by
    refine Finset.sum_le_sum fun s _ => ?_
    by_cases hs : s < N0
    · simp only [hs, if_true]
      split_ifs <;> omega
    · simp only [hs, if_false, zero_add]
      by_cases hc : (ω s).1 = c
      · rw [if_pos hc, if_pos (hN s (not_lt.mp hs) hc)]
      · simp [hc]
  refine h1.trans ?_
  rw [Finset.sum_add_distrib]
  have h2 : ∑ s ∈ Finset.range n, (if s < N0 then 1 else 0) ≤ N0 := by
    rw [← Finset.card_filter]
    calc ((Finset.range n).filter (fun s => s < N0)).card ≤ (Finset.range N0).card :=
          Finset.card_le_card (fun s hs => by
            simp only [Finset.mem_filter, Finset.mem_range] at hs ⊢; exact hs.2)
      _ = N0 := Finset.card_range _
  have h3 : ∑ s ∈ Finset.range n, (if s + 1 ∈ Set.range σ.a ∪ Set.range σ.b then 1 else 0) ≤
      ((Finset.Icc 1 n).filter (fun i => i ∈ Set.range σ.a ∪ Set.range σ.b)).card := by
    rw [← Finset.card_filter]
    refine Finset.card_le_card_of_injOn (fun s => s + 1) (fun s hs => ?_) (fun a _ b _ h => by simpa using h)
    rw [Finset.mem_coe] at hs
    rw [Finset.mem_filter, Finset.mem_range] at hs
    rw [Finset.mem_coe, Finset.mem_filter, Finset.mem_Icc]
    exact ⟨⟨Nat.le_add_left 1 s, hs.1⟩, hs.2⟩
  omega

lemma wrong_dens (c : Fin 2) (ω : ℕ → Fin 2 × ℝ) (N0 : ℕ)
    (hN : ∀ n, N0 ≤ n → (ω n).1 = c → n + 1 ∈ Set.range σ.a ∪ Set.range σ.b) :
    Tendsto (fun n => (cntp c n ω : ℝ) / n) atTop (𝓝 0) := by
  classical
  have hd := σ.density_zero
  have h0 : Tendsto (fun n : ℕ => (N0 : ℝ) / n) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
  have hsum := h0.add hd
  rw [add_zero] at hsum
  refine squeeze_zero' (Filter.Eventually.of_forall fun n => by positivity) ?_ hsum
  filter_upwards [Filter.eventually_gt_atTop 0] with n hn
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  rw [← add_div]
  refine div_le_div_of_nonneg_right ?_ hnR.le
  have := cnt_le_forced σ c ω N0 hN n
  exact_mod_cast this

lemma cnt_cast (i : Fin 2) (n : ℕ) (ω : ℕ → Fin 2 × ℝ) :
    (cntp i n ω : ℝ) = ∑ s ∈ Finset.range n, (if (ω s).1 = i then (1 : ℝ) else 0) := by
  rw [cntp_eq]; push_cast
  refine Finset.sum_congr rfl fun s _ => ?_
  split_ifs <;> simp

lemma cnt_sum (n : ℕ) (ω : ℕ → Fin 2 × ℝ) : cntp 0 n ω + cntp 1 n ω = n := by
  rw [cntp_eq, cntp_eq, ← Finset.sum_add_distrib]
  have : ∀ s ∈ Finset.range n, ((if (ω s).1 = 0 then 1 else 0) + (if (ω s).1 = 1 then 1 else 0)) = 1 := by
    intro s _
    rcases Fin.exists_fin_two.mp ⟨(ω s).1, rfl⟩ with h | h <;> simp [h]
  rw [Finset.sum_congr rfl this]; simp

lemma sum_split (n : ℕ) (ω : ℕ → Fin 2 × ℝ) (F : Fin 2 × ℝ → ℝ) :
    ∑ s ∈ Finset.range n, F (ω s) =
      (∑ s ∈ Finset.range n, if (ω s).1 = 0 then F (ω s) else 0) +
      (∑ s ∈ Finset.range n, if (ω s).1 = 1 then F (ω s) else 0) := by
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun s _ => ?_
  rcases Fin.exists_fin_two.mp ⟨(ω s).1, rfl⟩ with h | h <;> simp [h]

lemma det_main (ω : ℕ → Fin 2 × ℝ)
    (hch : ∀ n, (ω n).1 = ruleChoice σ n (banditTrajPrefix 2 n ω))
    (hA : Tendsto (fun n => cntp 0 n ω) atTop atTop)
    (hB : Tendsto (fun n => cntp 1 n ω) atTop atTop)
    (a b : ℝ)
    (h0 : Tendsto (fun n => (∑ s ∈ Finset.range n, if (ω s).1 = 0 then (ω s).2 else 0) /
      (cntp 0 n ω : ℝ)) atTop (𝓝 a))
    (h1 : Tendsto (fun n => (∑ s ∈ Finset.range n, if (ω s).1 = 1 then (ω s).2 else 0) /
      (cntp 1 n ω : ℝ)) atTop (𝓝 b))
    (m : Fin 2 → ℝ) (hm0 : m 0 = a) (hm1 : m 1 = b) :
    Tendsto (fun n => (∑ s ∈ Finset.range n, m (ω s).1) / (n : ℝ)) atTop (𝓝 (max a b)) ∧
    Tendsto (fun n => partialSum n ω / (n : ℝ)) atTop (𝓝 (max a b)) := by
  classical
  have hq : ∀ n, ∑ s ∈ Finset.range n, m (ω s).1 = (cntp 0 n ω : ℝ) * a + (cntp 1 n ω : ℝ) * b := by
    intro n
    rw [cnt_cast, cnt_cast, Finset.sum_mul, Finset.sum_mul, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun s _ => ?_
    rcases Fin.exists_fin_two.mp ⟨(ω s).1, rfl⟩ with h | h <;> simp [h, hm0, hm1]
  have key := combine a b (fun n => cntp 0 n ω) (fun n => cntp 1 n ω) (fun n => cnt_sum n ω)
    (fun n => partialSum n ω)
    (fun n => ∑ s ∈ Finset.range n, if (ω s).1 = 0 then (ω s).2 else 0)
    (fun n => ∑ s ∈ Finset.range n, if (ω s).1 = 1 then (ω s).2 else 0)
    (fun n => by
      unfold partialSum
      exact sum_split n ω (fun z => z.2))
    h0 h1 hA hB ?_ ?_
  · simp_rw [hq]; exact key
  · intro hab
    have hev := h0.eventually_lt h1 hab
    obtain ⟨N0, hN0⟩ := Filter.eventually_atTop.mp hev
    refine wrong_dens σ 0 ω N0 (fun n hn hA0 => ?_)
    by_contra hnU
    have hna : n + 1 ∉ Set.range σ.a := fun h => hnU (Or.inl h)
    have hnb : n + 1 ∉ Set.range σ.b := fun h => hnU (Or.inr h)
    have hc := hch n
    unfold ruleChoice at hc
    rw [if_neg hna, if_neg hnb, emp_eq, emp_eq] at hc
    have := hN0 n hn
    rw [hA0] at hc
    split_ifs at hc with hlt
    · exact absurd hlt (not_lt.mpr this.le)
    · exact absurd hc (by decide)
  · intro hba
    have hev := h1.eventually_lt h0 hba
    obtain ⟨N0, hN0⟩ := Filter.eventually_atTop.mp hev
    refine wrong_dens σ 1 ω N0 (fun n hn hA1 => ?_)
    by_contra hnU
    have hna : n + 1 ∉ Set.range σ.a := fun h => hnU (Or.inl h)
    have hnb : n + 1 ∉ Set.range σ.b := fun h => hnU (Or.inr h)
    have hc := hch n
    unfold ruleChoice at hc
    rw [if_neg hna, if_neg hnb, emp_eq, emp_eq] at hc
    have := hN0 n hn
    rw [if_pos this] at hc
    rw [hA1] at hc
    exact absurd hc (by decide)

theorem average_reward_tendsto_max_ae_core (ν : StochasticBandit 2)
    (hint : ∀ i, Integrable id (ν.P i)) (σ : ForcedSchedule) :
    ∀ᵐ ω ∂(banditTrajMeasure ν (rule σ)),
      Tendsto (fun n : ℕ => partialSum n ω / (n : ℝ)) atTop
        (𝓝 (max (banditArmMean ν 0) (banditArmMean ν 1))) := by
  filter_upwards [rule_choice_ae ν σ, forced_a_ae ν σ, forced_b_ae ν σ,
    arm_slln ν (rule σ) 0 (hint 0), arm_slln ν (rule σ) 1 (hint 1)] with ω hch hA hB s0 s1
  exact (det_main σ ω hch hA hB _ _ (s0 hA) (s1 hB) (fun a => banditArmMean ν a) rfl rfl).2

lemma main_q_ae (ν : StochasticBandit 2) (hint : ∀ i, Integrable id (ν.P i)) (σ : ForcedSchedule) :
    ∀ᵐ ω ∂(banditTrajMeasure ν (rule σ)),
      Tendsto (fun n : ℕ => (∑ s ∈ Finset.range n, banditArmMean ν (ω s).1) / (n : ℝ)) atTop
        (𝓝 (max (banditArmMean ν 0) (banditArmMean ν 1))) := by
  filter_upwards [rule_choice_ae ν σ, forced_a_ae ν σ, forced_b_ae ν σ,
    arm_slln ν (rule σ) 0 (hint 0), arm_slln ν (rule σ) 1 (hint 1)] with ω hch hA hB s0 s1
  exact (det_main σ ω hch hA hB _ _ (s0 hA) (s1 hB) (fun a => banditArmMean ν a) rfl rfl).1

end Rule

section Expect

variable {k : ℕ} (ν : StochasticBandit k) (π : BanditPolicy k)

/-- total absolute first moment -/
noncomputable def Cenorm : ENNReal := ∑ a, ∫⁻ x, ‖x‖ₑ ∂(ν.P a)

lemma Cenorm_lt_top (hint : ∀ a, Integrable id (ν.P a)) : Cenorm ν < ⊤ := by
  unfold Cenorm
  refine ENNReal.sum_lt_top.mpr fun a _ => ?_
  exact (hint a).hasFiniteIntegral

lemma lintegral_enorm_step_le (n : ℕ) (h : BanditHistory k n) :
    ∫⁻ y, ‖y.2‖ₑ ∂(banditStepKernel ν π n h) ≤ Cenorm ν := by
  unfold banditStepKernel
  rw [Kernel.lintegral_compProd _ _ h (f := fun y => ‖y.2‖ₑ) measurable_snd.enorm]
  calc _ ≤ ∫⁻ _b, Cenorm ν ∂(π.select n h) := by
        refine lintegral_mono fun b => ?_
        unfold Cenorm
        exact Finset.single_le_sum (f := fun a => ∫⁻ x, ‖x‖ₑ ∂(ν.P a)) (fun _ _ => zero_le) (Finset.mem_univ b)
    _ = Cenorm ν := by simp

lemma integrable_step_snd (hint : ∀ a, Integrable id (ν.P a)) (n : ℕ) (h : BanditHistory k n) :
    Integrable (fun y : Fin k × ℝ => y.2) (banditStepKernel ν π n h) := by
  refine ⟨measurable_snd.aestronglyMeasurable, ?_⟩
  exact lt_of_le_of_lt (lintegral_enorm_step_le ν π n h) (Cenorm_lt_top ν hint)

lemma integrable_X (hint : ∀ a, Integrable id (ν.P a)) (s : ℕ) :
    Integrable (fun ω : ℕ → Fin k × ℝ => (ω s).2) (banditTrajMeasure ν π) := by
  refine ⟨(measurable_pi_apply s |>.snd).aestronglyMeasurable, ?_⟩
  have key := lintegral_pair ν π s (fun z => ‖z.2.2‖ₑ)
    (measurable_snd.comp measurable_snd).enorm
  have hb : ∫⁻ ω, ‖(ω s).2‖ₑ ∂(banditTrajMeasure ν π) ≤ Cenorm ν := by
    calc _ = ∫⁻ ω, ∫⁻ y, ‖y.2‖ₑ ∂(banditStepKernel ν π s (banditTrajPrefix k s ω)) ∂(banditTrajMeasure ν π) := key
      _ ≤ ∫⁻ _ω, Cenorm ν ∂(banditTrajMeasure ν π) :=
          lintegral_mono fun ω => lintegral_enorm_step_le ν π s _
      _ = Cenorm ν := by simp
  exact lt_of_le_of_lt hb (Cenorm_lt_top ν hint)

lemma mean_bdd (a : Fin k) : |banditArmMean ν a| ≤ ∑ b, |banditArmMean ν b| :=
  Finset.single_le_sum (f := fun b => |banditArmMean ν b|) (fun _ _ => abs_nonneg _) (Finset.mem_univ a)

lemma step_snd_integral (hint : ∀ a, Integrable id (ν.P a)) (n : ℕ) (h : BanditHistory k n) :
    ∫ y, y.2 ∂(banditStepKernel ν π n h) = ∫ y, banditArmMean ν y.1 ∂(banditStepKernel ν π n h) := by
  have hi := integrable_step_snd ν π hint n h
  have hR := integral_step ν π n h (fun y => banditArmMean ν y.1)
    ((measurable_of_finite (fun a : Fin k => banditArmMean ν a)).comp measurable_fst) (∑ b, |banditArmMean ν b|)
    (fun z => mean_bdd ν z.1)
  rw [hR]
  unfold banditStepKernel at hi ⊢
  rw [integral_compProd hi]
  refine integral_congr_ae (Filter.Eventually.of_forall fun a => ?_)
  simp only [integral_const, probReal_univ, one_smul]
  rfl

lemma E_X (hint : ∀ a, Integrable id (ν.P a)) (s : ℕ) :
    ∫ ω, (ω s).2 ∂(banditTrajMeasure ν π) = ∫ ω, banditArmMean ν (ω s).1 ∂(banditTrajMeasure ν π) := by
  have h1 := integral_pair ν π s (fun z => z.2.2) (measurable_snd.comp measurable_snd)
    (integrable_X ν π hint s)
  have h2 := integral_pair ν π s (fun z => banditArmMean ν z.2.1)
    ((measurable_of_finite (fun a : Fin k => banditArmMean ν a)).comp (measurable_fst.comp measurable_snd))
    (integrable_of_bdd _ _ ((measurable_of_finite (fun a : Fin k => banditArmMean ν a)).comp
      ((measurable_fst.comp measurable_snd).comp (measurable_pair s))) (∑ b, |banditArmMean ν b|)
      (fun ω => mean_bdd ν _))
  simp only at h1 h2
  rw [h1, h2]
  exact integral_congr_ae (Filter.Eventually.of_forall fun ω => step_snd_integral ν π hint s _)

end Expect

section Thm2

theorem expected_average_tendsto_max_core (ν : StochasticBandit 2)
    (hint : ∀ i, Integrable id (ν.P i)) (σ : ForcedSchedule) :
    Tendsto (fun n : ℕ => ∫ ω, partialSum n ω / (n : ℝ) ∂(banditTrajMeasure ν (rule σ)))
      atTop (𝓝 (max (banditArmMean ν 0) (banditArmMean ν 1))) := by
  set μ := banditTrajMeasure ν (rule σ) with hμ
  set B : ℝ := ∑ b, |banditArmMean ν b| with hB
  have hmeas : ∀ n : ℕ, Measurable (fun ω : ℕ → Fin 2 × ℝ =>
      (∑ s ∈ Finset.range n, banditArmMean ν (ω s).1) / (n : ℝ)) := by
    intro n
    refine Measurable.div_const (Finset.measurable_sum _ fun s _ => ?_) _
    exact (measurable_of_finite (fun a : Fin 2 => banditArmMean ν a)).comp
      (measurable_fst.comp (measurable_pi_apply s))
  have hbound : ∀ n : ℕ, ∀ ω : ℕ → Fin 2 × ℝ,
      |(∑ s ∈ Finset.range n, banditArmMean ν (ω s).1) / (n : ℝ)| ≤ B := by
    intro n ω
    have hB0 : 0 ≤ B := Finset.sum_nonneg fun _ _ => abs_nonneg _
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp [hB0]
    · have hnR : (0 : ℝ) < n := by exact_mod_cast hn
      rw [abs_div, abs_of_pos hnR, div_le_iff₀ hnR]
      calc |∑ s ∈ Finset.range n, banditArmMean ν (ω s).1|
          ≤ ∑ s ∈ Finset.range n, |banditArmMean ν (ω s).1| := Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ s ∈ Finset.range n, B := Finset.sum_le_sum fun s _ => mean_bdd ν (ω s).1
        _ = B * n := by simp [mul_comm]
  have heq : ∀ n : ℕ, ∫ ω, partialSum n ω / (n : ℝ) ∂μ =
      ∫ ω, (∑ s ∈ Finset.range n, banditArmMean ν (ω s).1) / (n : ℝ) ∂μ := by
    intro n
    rw [integral_div, integral_div]
    congr 1
    have h1 : ∫ ω, partialSum n ω ∂μ = ∑ s ∈ Finset.range n, ∫ ω, (ω s).2 ∂μ := by
      unfold partialSum
      rw [integral_finset_sum _ (fun s _ => integrable_X ν (rule σ) hint s)]
    have h2 : ∫ ω, (∑ s ∈ Finset.range n, banditArmMean ν (ω s).1) ∂μ =
        ∑ s ∈ Finset.range n, ∫ ω, banditArmMean ν (ω s).1 ∂μ := by
      rw [integral_finset_sum _ (fun s _ => ?_)]
      exact integrable_of_bdd _ _ ((measurable_of_finite (fun a : Fin 2 => banditArmMean ν a)).comp
        (measurable_fst.comp (measurable_pi_apply s))) B (fun ω => mean_bdd ν _)
    rw [h1, h2]
    exact Finset.sum_congr rfl fun s _ => E_X ν (rule σ) hint s
  simp_rw [heq]
  have := tendsto_integral_of_dominated_convergence (μ := μ) (fun _ : ℕ → Fin 2 × ℝ => B)
    (fun n => (hmeas n).aestronglyMeasurable) (integrable_const B)
    (fun n => Filter.Eventually.of_forall fun ω => by rw [Real.norm_eq_abs]; exact hbound n ω)
    (main_q_ae ν hint σ)
  simpa using this

theorem forced_sampling_loss_tendsto_zero_core (ν : StochasticBandit 2)
    (hint : ∀ i, Integrable id (ν.P i)) (σ : ForcedSchedule) :
    Tendsto (fun n : ℕ => loss ν (rule σ) n) atTop (𝓝 0) := by
  have h := expected_average_tendsto_max_core ν hint σ
  have h2 := (tendsto_const_nhds (x := max (banditArmMean ν 0) (banditArmMean ν 1))).sub h
  simpa [loss] using h2

end Thm2

end RobbinsSeqDesign.ForcedSampling

open RobbinsSeqDesign.ForcedSampling


theorem solution (ν : StochasticBandit 2)
    (hint : ∀ i, Integrable id (ν.P i)) (σ : ForcedSchedule) :
    Tendsto (fun n : ℕ => ∫ ω, partialSum n ω / (n : ℝ) ∂(banditTrajMeasure ν (rule σ)))
      atTop (𝓝 (max (banditArmMean ν 0) (banditArmMean ν 1))) := by
  exact expected_average_tendsto_max_core ν hint σ
