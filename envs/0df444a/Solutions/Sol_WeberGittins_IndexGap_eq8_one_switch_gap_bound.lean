-- Prove2me | solution 1 for WeberGittins.IndexGap.eq8_one_switch_gap_bound
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-11-11T17:32:46.928795+00:00
-- url     : https://prove2.me/submissions/9d18c75b-f0be-4d3c-a1df-1c969160e71d

import Mathlib
import Definitions.Def_GittinsIndex
import Definitions.Def_GittinsPrevailingChargeValue
import Definitions.Def_WeberGittins_IndexGap_SwitchPolicies
import Theorems.Thm_WeberGittins_Suboptimality_theorem2_suboptimality_bound

set_option autoImplicit false

/-! BELL for df742747: port of bf11615d optimal-stopping lemmas to measurable data. -/

open BanditAlgorithm in
/-- Positive stopping time (local copy). -/
def DfbPosStop {S : Type*} [MeasurableSpace S] (τ : (ℕ → S) → ℕ∞) : Prop :=
  IsTrajStoppingTime τ ∧ ∀ ω, 1 ≤ τ ω

/-- First hitting time at or after time 1 (local copy). -/
noncomputable def dfbHit {S : Type*} (Z : Set S) (ω : ℕ → S) : ℕ∞ :=
  ⨅ t : {t : ℕ // 1 ≤ t ∧ ω t ∈ Z}, ((t : ℕ) : ℕ∞)

open MeasureTheory ProbabilityTheory in
private lemma p2mbf_kint {S : Type*} [MeasurableSpace S] (P : Kernel S S) [IsMarkovKernel P]
    {g : S → ℝ} (hg : Measurable g) : Measurable (fun y ↦ ∫ z, g z ∂P y) := by
  have := ((hg.comp measurable_snd).stronglyMeasurable).integral_kernel_prod_right' (κ := P)
  exact this.measurable

open MeasureTheory ProbabilityTheory BanditAlgorithm in
private lemma p2mbf_prob {S : Type*} [MeasurableSpace S] (P : Kernel S S) [IsMarkovKernel P]
    (x : S) : IsProbabilityMeasure (markovChainMeasure P x) := by
  unfold markovChainMeasure; infer_instance

open MeasureTheory ProbabilityTheory BanditAlgorithm in
private lemma p2mbf_marg0 {S : Type*} [MeasurableSpace S] (P : Kernel S S) [IsMarkovKernel P]
    (x : S) : (markovChainMeasure P x).map (Preorder.frestrictLe 0) =
      Measure.dirac (fun _ ↦ x) := by
  rw [markovChainMeasure, Kernel.trajMeasure,
    Measure.map_comp _ _ (Preorder.measurable_frestrictLe 0), Kernel.traj_map_frestrictLe,
    Kernel.partialTraj_self, Measure.id_comp, Measure.map_dirac' (MeasurableEquiv.measurable _)]
  congr 1

open MeasureTheory ProbabilityTheory BanditAlgorithm in
private lemma p2mbf_int0 {S : Type*} [MeasurableSpace S] (P : Kernel S S) [IsMarkovKernel P]
    (x : S) (F : S → ℝ) (hF : Measurable F) :
    ∫ ω, F (ω 0) ∂markovChainMeasure P x = F x := by
  have hFm : Measurable (fun h : (Π _i : Finset.Iic 0, S) ↦ F (h ⟨0, Finset.mem_Iic.2 le_rfl⟩)) :=
    hF.comp (measurable_pi_apply _)
  have h1 := integral_map (μ := markovChainMeasure P x) (Preorder.measurable_frestrictLe 0).aemeasurable
    hFm.aestronglyMeasurable
  rw [p2mbf_marg0, integral_dirac' _ _ hFm.stronglyMeasurable] at h1
  exact h1.symm

open MeasureTheory ProbabilityTheory BanditAlgorithm in
private lemma p2mbf_meas_lt {S : Type*} [MeasurableSpace S] (τ : (ℕ → S) → ℕ∞)
    (hτ : IsTrajStoppingTime τ) (t : ℕ) : MeasurableSet {ω : ℕ → S | (t : ℕ∞) < τ ω} := by
  have h1 : MeasurableSet {ω : ℕ → S | τ ω ≤ (t : ℕ∞)} := by
    obtain ⟨s, hs, hse⟩ := hτ t
    rw [← hse]
    exact (measurable_pi_lambda _ (fun i ↦ measurable_pi_apply _)) hs
  have : {ω : ℕ → S | (t : ℕ∞) < τ ω} = {ω | τ ω ≤ (t : ℕ∞)}ᶜ := by
    ext ω; simp [not_le]
  rw [this]
  exact h1.compl

open MeasureTheory ProbabilityTheory BanditAlgorithm in
private lemma p2mbf_filt_lt {S : Type*} [MeasurableSpace S] (τ : (ℕ → S) → ℕ∞)
    (hτ : IsTrajStoppingTime τ) (t : ℕ) :
    MeasurableSet[trajectoryFiltration S t] {ω : ℕ → S | (t : ℕ∞) < τ ω} := by
  have : {ω : ℕ → S | (t : ℕ∞) < τ ω} = {ω | τ ω ≤ (t : ℕ∞)}ᶜ := by
    ext ω; simp [not_le]
  rw [this]
  exact (hτ t).compl

open MeasureTheory ProbabilityTheory BanditAlgorithm in
private lemma p2mbf_int_of_bound {α : Type*} [MeasurableSpace α] (μ : Measure α)
    [IsFiniteMeasure μ] (F : α → ℝ) (hF : Measurable F) (B : ℝ) (hB : ∀ x, |F x| ≤ B) :
    Integrable F μ :=
  Integrable.of_bound hF.aestronglyMeasurable B
    (Filter.Eventually.of_forall fun x ↦ by rw [Real.norm_eq_abs]; exact hB x)

open MeasureTheory ProbabilityTheory BanditAlgorithm in
private lemma p2mbf_abs_int_le {α : Type*} [MeasurableSpace α] (μ : Measure α)
    [IsProbabilityMeasure μ] (F : α → ℝ) (B : ℝ) (hB : ∀ x, |F x| ≤ B) :
    |∫ x, F x ∂μ| ≤ B := by
  have := norm_integral_le_of_norm_le_const (μ := μ) (f := F) (C := B)
    (Filter.Eventually.of_forall fun x ↦ by rw [Real.norm_eq_abs]; exact hB x)
  rwa [probReal_univ, mul_one, Real.norm_eq_abs] at this

open MeasureTheory ProbabilityTheory BanditAlgorithm in
private lemma p2mbf_term_bound {S : Type*} (a : ℝ) (ha0 : 0 ≤ a) (f : S → ℝ) (Bf : ℝ)
    (hBf : 0 ≤ Bf) (hf : ∀ y, |f y| ≤ Bf) (τ : (ℕ → S) → ℕ∞) (ω : ℕ → S) (t : ℕ) :
    ‖(if (t : ℕ∞) < τ ω then a ^ t * f (ω t) else 0)‖ ≤ Bf * a ^ t := by
  split_ifs
  · rw [Real.norm_eq_abs, abs_mul, abs_pow, abs_of_nonneg ha0, mul_comm]
    exact mul_le_mul_of_nonneg_right (hf _) (pow_nonneg ha0 t)
  · simp only [norm_zero]; positivity

open MeasureTheory ProbabilityTheory BanditAlgorithm in
private lemma p2mbf_summable {S : Type*} (a : ℝ) (ha0 : 0 ≤ a) (ha1 : a < 1) (f : S → ℝ)
    (Bf : ℝ) (hBf : 0 ≤ Bf) (hf : ∀ y, |f y| ≤ Bf) (τ : (ℕ → S) → ℕ∞) (ω : ℕ → S) :
    Summable (fun t : ℕ ↦ if (t : ℕ∞) < τ ω then a ^ t * f (ω t) else 0) :=
  Summable.of_norm_bounded ((summable_geometric_of_lt_one ha0 ha1).mul_left Bf)
    (p2mbf_term_bound a ha0 f Bf hBf hf τ ω)

open MeasureTheory ProbabilityTheory BanditAlgorithm in
private lemma p2mbf_dss_bound {S : Type*} (a : ℝ) (ha0 : 0 ≤ a) (ha1 : a < 1) (f : S → ℝ)
    (Bf : ℝ) (hBf : 0 ≤ Bf) (hf : ∀ y, |f y| ≤ Bf) (τ : (ℕ → S) → ℕ∞) (ω : ℕ → S) :
    |discountedStoppedSum a f τ ω| ≤ Bf / (1 - a) := by
  unfold discountedStoppedSum
  have hg : HasSum (fun t : ℕ ↦ Bf * a ^ t) (Bf * (1 - a)⁻¹) :=
    (hasSum_geometric_of_lt_one ha0 ha1).mul_left Bf
  have := tsum_of_norm_bounded hg (p2mbf_term_bound a ha0 f Bf hBf hf τ ω)
  rw [Real.norm_eq_abs] at this
  rwa [div_eq_mul_inv]

open MeasureTheory ProbabilityTheory BanditAlgorithm in
private lemma p2mbf_tail {S : Type*} (a : ℝ) (ha0 : 0 ≤ a) (ha1 : a < 1) (f : S → ℝ)
    (Bf : ℝ) (hBf : 0 ≤ Bf) (hf : ∀ y, |f y| ≤ Bf) (τ : (ℕ → S) → ℕ∞) (ω : ℕ → S) (N : ℕ) :
    |discountedStoppedSum a f τ ω -
        ∑ t ∈ Finset.range N, (if (t : ℕ∞) < τ ω then a ^ t * f (ω t) else 0)| ≤
      Bf * a ^ N / (1 - a) := by
  unfold discountedStoppedSum
  have hs := p2mbf_summable a ha0 ha1 f Bf hBf hf τ ω
  rw [← hs.sum_add_tsum_nat_add N, add_sub_cancel_left]
  have hg : HasSum (fun t : ℕ ↦ Bf * a ^ N * a ^ t) (Bf * a ^ N * (1 - a)⁻¹) :=
    (hasSum_geometric_of_lt_one ha0 ha1).mul_left (Bf * a ^ N)
  have := tsum_of_norm_bounded hg (fun t ↦ by
    have h := p2mbf_term_bound a ha0 f Bf hBf hf τ ω (t + N)
    calc _ ≤ Bf * a ^ (t + N) := h
      _ = Bf * a ^ N * a ^ t := by ring)
  rw [Real.norm_eq_abs] at this
  rwa [div_eq_mul_inv]

open MeasureTheory ProbabilityTheory BanditAlgorithm in
private lemma p2mbf_dss_meas {S : Type*} [MeasurableSpace S] (a : ℝ) (f : S → ℝ)
    (hf : Measurable f) (τ : (ℕ → S) → ℕ∞) (hτ : IsTrajStoppingTime τ) :
    Measurable (discountedStoppedSum a f τ) := by
  unfold discountedStoppedSum
  exact Measurable.tsum fun t ↦ Measurable.ite (p2mbf_meas_lt τ hτ t)
    (measurable_const.mul (hf.comp (measurable_pi_apply t))) measurable_const

open MeasureTheory ProbabilityTheory BanditAlgorithm in
private lemma p2mbf_dss_int {S : Type*} [MeasurableSpace S]
    (P : Kernel S S) [IsMarkovKernel P] (x : S) (a : ℝ) (ha0 : 0 ≤ a) (ha1 : a < 1)
    (f : S → ℝ) (Bf : ℝ) (hBf : 0 ≤ Bf) (hf : ∀ y, |f y| ≤ Bf) (τ : (ℕ → S) → ℕ∞)
    (hτ : IsTrajStoppingTime τ) (hfm : Measurable f) :
    Integrable (discountedStoppedSum a f τ) (markovChainMeasure P x) := by
  haveI := p2mbf_prob P x
  exact p2mbf_int_of_bound _ _ (p2mbf_dss_meas a f hfm τ hτ) (Bf / (1 - a))
    (p2mbf_dss_bound a ha0 ha1 f Bf hBf hf τ)

open MeasureTheory ProbabilityTheory BanditAlgorithm in
private lemma p2mbf_dss_neg {S : Type*} (a : ℝ) (f : S → ℝ) (τ : (ℕ → S) → ℕ∞)
    (ω : ℕ → S) :
    discountedStoppedSum a (fun y ↦ -f y) τ ω = -discountedStoppedSum a f τ ω := by
  unfold discountedStoppedSum
  rw [← tsum_neg]
  refine tsum_congr fun t ↦ ?_
  split_ifs <;> ring

open MeasureTheory ProbabilityTheory BanditAlgorithm in
private lemma p2mbf_markov {S : Type*} [MeasurableSpace S]
    (P : Kernel S S) [IsMarkovKernel P] (x : S) (s : ℕ) (A : Set (ℕ → S))
    (hA : MeasurableSet[trajectoryFiltration S s] A) (g : S → ℝ) (Bg : ℝ)
    (hg : ∀ y, |g y| ≤ Bg) (hgm : Measurable g) :
    ∫ ω, A.indicator (fun ω ↦ g (ω (s + 1))) ω ∂markovChainMeasure P x =
      ∫ ω, A.indicator (fun ω ↦ ∫ z, g z ∂P (ω s)) ω ∂markovChainMeasure P x := by
  haveI := p2mbf_prob P x
  obtain ⟨B, hB, rfl⟩ := MeasurableSpace.measurableSet_comap.1 hA
  have hPgm : Measurable (fun y ↦ ∫ z, g z ∂P y) := p2mbf_kint P hgm
  have hmap : (markovChainMeasure P x).map (Preorder.frestrictLe s) ⊗ₘ markovChainStep P s =
      (markovChainMeasure P x).map (fun ω ↦ (Preorder.frestrictLe s ω, ω (s + 1))) :=
    Kernel.map_frestrictLe_trajMeasure_compProd_eq_map_trajMeasure (X := fun _ : ℕ ↦ S)
      (μ₀ := Measure.dirac x) (κ := markovChainStep P) (a := s)
  have hΦ : Measurable (fun ω : ℕ → S ↦ (Preorder.frestrictLe s ω, ω (s + 1))) :=
    (Preorder.measurable_frestrictLe s).prodMk (measurable_pi_apply (s + 1))
  have hFm : Measurable ((B ×ˢ (Set.univ : Set S)).indicator
      (fun p : (Π _i : Finset.Iic s, S) × S ↦ g p.2)) :=
    (hgm.comp measurable_snd).indicator (hB.prod MeasurableSet.univ)
  have hFint : Integrable ((B ×ˢ (Set.univ : Set S)).indicator
      (fun p : (Π _i : Finset.Iic s, S) × S ↦ g p.2))
      ((markovChainMeasure P x).map (Preorder.frestrictLe s) ⊗ₘ markovChainStep P s) :=
    p2mbf_int_of_bound _ _ hFm Bg (fun p ↦ by
      by_cases hp : p ∈ B ×ˢ (Set.univ : Set S)
      · rw [Set.indicator_of_mem hp]; exact hg _
      · rw [Set.indicator_of_notMem hp, abs_zero]; exact le_trans (abs_nonneg _) (hg p.2))
  have hGm : Measurable (B.indicator
      (fun h : (Π _i : Finset.Iic s, S) ↦ ∫ z, g z ∂P (h ⟨s, Finset.mem_Iic.2 le_rfl⟩))) :=
    (hPgm.comp (measurable_pi_apply _)).indicator hB
  calc ∫ ω, ((fun ω (i : Finset.Iic s) ↦ ω i.1) ⁻¹' B).indicator (fun ω ↦ g (ω (s + 1))) ω
        ∂markovChainMeasure P x
      = ∫ ω, (B ×ˢ (Set.univ : Set S)).indicator
          (fun p : (Π _i : Finset.Iic s, S) × S ↦ g p.2)
          (Preorder.frestrictLe s ω, ω (s + 1)) ∂markovChainMeasure P x := by
        refine integral_congr_ae (Filter.Eventually.of_forall fun ω ↦ ?_)
        dsimp only
        by_cases h : Preorder.frestrictLe s ω ∈ B
        · rw [Set.indicator_of_mem (show ω ∈ (fun ω (i : Finset.Iic s) ↦ ω i.1) ⁻¹' B from h),
            Set.indicator_of_mem (show (Preorder.frestrictLe s ω, ω (s + 1)) ∈
              B ×ˢ (Set.univ : Set S) from ⟨h, trivial⟩)]
        · rw [Set.indicator_of_notMem
              (show ω ∉ (fun ω (i : Finset.Iic s) ↦ ω i.1) ⁻¹' B from h),
            Set.indicator_of_notMem (show (Preorder.frestrictLe s ω, ω (s + 1)) ∉
              B ×ˢ (Set.univ : Set S) from fun hh ↦ h hh.1)]
    _ = ∫ p, (B ×ˢ (Set.univ : Set S)).indicator
          (fun p : (Π _i : Finset.Iic s, S) × S ↦ g p.2) p
          ∂((markovChainMeasure P x).map (fun ω ↦ (Preorder.frestrictLe s ω, ω (s + 1)))) :=
        (integral_map hΦ.aemeasurable hFm.aestronglyMeasurable).symm
    _ = ∫ p, (B ×ˢ (Set.univ : Set S)).indicator
          (fun p : (Π _i : Finset.Iic s, S) × S ↦ g p.2) p
          ∂((markovChainMeasure P x).map (Preorder.frestrictLe s) ⊗ₘ markovChainStep P s) := by
        rw [hmap]
    _ = ∫ h, ∫ y, (B ×ˢ (Set.univ : Set S)).indicator
          (fun p : (Π _i : Finset.Iic s, S) × S ↦ g p.2) (h, y) ∂(markovChainStep P s h)
          ∂((markovChainMeasure P x).map (Preorder.frestrictLe s)) :=
        Measure.integral_compProd hFint
    _ = ∫ h, B.indicator
          (fun h : (Π _i : Finset.Iic s, S) ↦ ∫ z, g z ∂P (h ⟨s, Finset.mem_Iic.2 le_rfl⟩)) h
          ∂((markovChainMeasure P x).map (Preorder.frestrictLe s)) := by
        refine integral_congr_ae (Filter.Eventually.of_forall fun h ↦ ?_)
        have hk : markovChainStep P s h = P (h ⟨s, Finset.mem_Iic.2 le_rfl⟩) := by
          rw [markovChainStep, Kernel.comap_apply]
        simp only
        rw [hk]
        by_cases hh : h ∈ B
        · rw [Set.indicator_of_mem hh]
          refine integral_congr_ae (Filter.Eventually.of_forall fun y ↦ ?_)
          exact Set.indicator_of_mem
            (show (h, y) ∈ B ×ˢ (Set.univ : Set S) from ⟨hh, trivial⟩) _
        · rw [Set.indicator_of_notMem hh]
          exact integral_eq_zero_of_ae (Filter.Eventually.of_forall fun y ↦
            Set.indicator_of_notMem (fun hh' ↦ hh hh'.1) _)
    _ = ∫ ω, B.indicator
          (fun h : (Π _i : Finset.Iic s, S) ↦ ∫ z, g z ∂P (h ⟨s, Finset.mem_Iic.2 le_rfl⟩))
          (Preorder.frestrictLe s ω) ∂markovChainMeasure P x :=
        integral_map (Preorder.measurable_frestrictLe s).aemeasurable hGm.aestronglyMeasurable
    _ = ∫ ω, ((fun ω (i : Finset.Iic s) ↦ ω i.1) ⁻¹' B).indicator
          (fun ω ↦ ∫ z, g z ∂P (ω s)) ω ∂markovChainMeasure P x := by
        refine integral_congr_ae (Filter.Eventually.of_forall fun ω ↦ ?_)
        dsimp only
        by_cases h : Preorder.frestrictLe s ω ∈ B
        · rw [Set.indicator_of_mem h,
            Set.indicator_of_mem (show ω ∈ (fun ω (i : Finset.Iic s) ↦ ω i.1) ⁻¹' B from h)]
          rfl
        · rw [Set.indicator_of_notMem h, Set.indicator_of_notMem
            (show ω ∉ (fun ω (i : Finset.Iic s) ↦ ω i.1) ⁻¹' B from h)]

open MeasureTheory ProbabilityTheory BanditAlgorithm in
private lemma p2mbf_core {S : Type*} [MeasurableSpace S]
    (P : Kernel S S) [IsMarkovKernel P] (a : ℝ) (ha0 : 0 ≤ a) (ha1 : a < 1)
    (f G : S → ℝ) (Bf BG : ℝ) (hBf : 0 ≤ Bf) (hf : ∀ y, |f y| ≤ Bf) (hG : ∀ y, |G y| ≤ BG)
    (τ : (ℕ → S) → ℕ∞) (hτ : IsTrajStoppingTime τ) (hτ1 : ∀ ω, 1 ≤ τ ω)
    (H : ∀ (ω : ℕ → S) (n : ℕ),
      (if ((n + 1 : ℕ) : ℕ∞) < τ ω then f (ω (n + 1)) + a * ∫ z, G z ∂P (ω (n + 1)) else 0) ≤
        (if (n : ℕ∞) < τ ω then G (ω (n + 1)) else 0))
    (x : S) (hfm : Measurable f) (hGm : Measurable G) :
    ∫ ω, discountedStoppedSum a f τ ω ∂markovChainMeasure P x ≤
      f x + a * ∫ z, G z ∂P x := by
  haveI hprob := p2mbf_prob P x
  have hBG : 0 ≤ BG := le_trans (abs_nonneg _) (hG x)
  have hPGb : ∀ y, |∫ z, G z ∂P y| ≤ BG := fun y ↦ p2mbf_abs_int_le (P y) G BG hG
  have hPGm : Measurable (fun y ↦ ∫ z, G z ∂P y) := p2mbf_kint P hGm
  have htm : ∀ t : ℕ, Measurable
      (fun ω : ℕ → S ↦ if (t : ℕ∞) < τ ω then a ^ t * f (ω t) else 0) :=
    fun t ↦ Measurable.ite (p2mbf_meas_lt τ hτ t)
      (measurable_const.mul (hfm.comp (measurable_pi_apply t))) measurable_const
  have htint : ∀ t : ℕ, Integrable
      (fun ω : ℕ → S ↦ if (t : ℕ∞) < τ ω then a ^ t * f (ω t) else 0)
      (markovChainMeasure P x) := fun t ↦
    p2mbf_int_of_bound _ _ (htm t) (Bf * a ^ t) (fun ω ↦ by
      have := p2mbf_term_bound a ha0 f Bf hBf hf τ ω t
      rwa [Real.norm_eq_abs] at this)
  have hYint : ∀ N : ℕ, Integrable (fun ω : ℕ → S ↦ ∑ t ∈ Finset.range N,
      (if (t : ℕ∞) < τ ω then a ^ t * f (ω t) else 0)) (markovChainMeasure P x) :=
    fun N ↦ integrable_finset_sum _ (fun t _ ↦ htint t)
  have hLint : ∀ n : ℕ, Integrable (fun ω : ℕ → S ↦
      if (n : ℕ∞) < τ ω then a ^ (n + 1) * ∫ z, G z ∂P (ω n) else 0)
      (markovChainMeasure P x) := by
    intro n
    refine p2mbf_int_of_bound _ _ ?_ (a ^ (n + 1) * BG) (fun ω ↦ ?_)
    · exact Measurable.ite (p2mbf_meas_lt τ hτ n)
        (measurable_const.mul (hPGm.comp (measurable_pi_apply n))) measurable_const
    · split_ifs
      · rw [abs_mul, abs_pow, abs_of_nonneg ha0]
        exact mul_le_mul_of_nonneg_left (hPGb _) (pow_nonneg ha0 _)
      · simp only [abs_zero]; positivity
  have hM1int : ∀ n : ℕ, Integrable (fun ω : ℕ → S ↦
      {ω : ℕ → S | (n : ℕ∞) < τ ω}.indicator (fun ω ↦ G (ω (n + 1))) ω)
      (markovChainMeasure P x) := fun n ↦
    (p2mbf_int_of_bound _ _ (hGm.comp (measurable_pi_apply (n + 1))) BG
      (fun ω ↦ hG _)).indicator (p2mbf_meas_lt τ hτ n)
  have hM2int : ∀ n : ℕ, Integrable (fun ω : ℕ → S ↦
      {ω : ℕ → S | (n : ℕ∞) < τ ω}.indicator (fun ω ↦ ∫ z, G z ∂P (ω n)) ω)
      (markovChainMeasure P x) := fun n ↦
    (p2mbf_int_of_bound _ _ (hPGm.comp (measurable_pi_apply n)) BG
      (fun ω ↦ hPGb _)).indicator (p2mbf_meas_lt τ hτ n)
  have hstep : ∀ n : ℕ,
      ∫ ω, ((∑ t ∈ Finset.range (n + 1 + 1),
          (if (t : ℕ∞) < τ ω then a ^ t * f (ω t) else 0)) +
          (if ((n + 1 : ℕ) : ℕ∞) < τ ω then a ^ (n + 1 + 1) * ∫ z, G z ∂P (ω (n + 1)) else 0))
          ∂markovChainMeasure P x ≤
      ∫ ω, ((∑ t ∈ Finset.range (n + 1),
          (if (t : ℕ∞) < τ ω then a ^ t * f (ω t) else 0)) +
          (if (n : ℕ∞) < τ ω then a ^ (n + 1) * ∫ z, G z ∂P (ω n) else 0))
          ∂markovChainMeasure P x := by
    intro n
    have hmk := p2mbf_markov P x n {ω : ℕ → S | (n : ℕ∞) < τ ω} (p2mbf_filt_lt τ hτ n) G BG hG hGm
    have hpath : ∀ ω : ℕ → S,
        (∑ t ∈ Finset.range (n + 1 + 1), (if (t : ℕ∞) < τ ω then a ^ t * f (ω t) else 0)) +
          (if ((n + 1 : ℕ) : ℕ∞) < τ ω then a ^ (n + 1 + 1) * ∫ z, G z ∂P (ω (n + 1))
            else 0) ≤
        ((∑ t ∈ Finset.range (n + 1), (if (t : ℕ∞) < τ ω then a ^ t * f (ω t) else 0)) +
          (if (n : ℕ∞) < τ ω then a ^ (n + 1) * ∫ z, G z ∂P (ω n) else 0)) +
          (a ^ (n + 1) * {ω : ℕ → S | (n : ℕ∞) < τ ω}.indicator (fun ω ↦ G (ω (n + 1))) ω -
           a ^ (n + 1) * {ω : ℕ → S | (n : ℕ∞) < τ ω}.indicator
              (fun ω ↦ ∫ z, G z ∂P (ω n)) ω) := by
      intro ω
      have hH := H ω n
      have hp : 0 ≤ a ^ (n + 1) := pow_nonneg ha0 _
      have hmono : ((n + 1 : ℕ) : ℕ∞) < τ ω → (n : ℕ∞) < τ ω :=
        fun h ↦ lt_trans (by exact_mod_cast Nat.lt_succ_self n) h
      rw [Finset.sum_range_succ _ (n + 1)]
      simp only [Set.indicator_apply, Set.mem_setOf_eq]
      by_cases h1 : ((n + 1 : ℕ) : ℕ∞) < τ ω
      · have h0 := hmono h1
        simp only [if_pos h1, if_pos h0] at hH ⊢
        have key := mul_le_mul_of_nonneg_left hH hp
        rw [pow_succ a (n + 1)]
        nlinarith [key]
      · by_cases h0 : (n : ℕ∞) < τ ω
        · simp only [if_neg h1, if_pos h0] at hH ⊢
          nlinarith [mul_nonneg hp hH]
        · simp only [if_neg h1, if_neg h0]
          linarith
    calc _ ≤ ∫ ω, (((∑ t ∈ Finset.range (n + 1),
            (if (t : ℕ∞) < τ ω then a ^ t * f (ω t) else 0)) +
            (if (n : ℕ∞) < τ ω then a ^ (n + 1) * ∫ z, G z ∂P (ω n) else 0)) +
            (a ^ (n + 1) * {ω : ℕ → S | (n : ℕ∞) < τ ω}.indicator (fun ω ↦ G (ω (n + 1))) ω -
             a ^ (n + 1) * {ω : ℕ → S | (n : ℕ∞) < τ ω}.indicator
                (fun ω ↦ ∫ z, G z ∂P (ω n)) ω)) ∂markovChainMeasure P x :=
          integral_mono (((hYint (n + 1 + 1)).add (hLint (n + 1))))
            (((hYint (n + 1)).add (hLint n)).add
              (((hM1int n).const_mul _).sub ((hM2int n).const_mul _))) hpath
      _ = _ := by
          have hA : Integrable (fun ω : ℕ → S ↦ (∑ t ∈ Finset.range (n + 1),
              (if (t : ℕ∞) < τ ω then a ^ t * f (ω t) else 0)) +
              (if (n : ℕ∞) < τ ω then a ^ (n + 1) * ∫ z, G z ∂P (ω n) else 0))
              (markovChainMeasure P x) := (hYint (n + 1)).add (hLint n)
          have hB1 : Integrable (fun ω : ℕ → S ↦
              a ^ (n + 1) * {ω : ℕ → S | (n : ℕ∞) < τ ω}.indicator (fun ω ↦ G (ω (n + 1))) ω)
              (markovChainMeasure P x) := (hM1int n).const_mul _
          have hB2 : Integrable (fun ω : ℕ → S ↦
              a ^ (n + 1) * {ω : ℕ → S | (n : ℕ∞) < τ ω}.indicator
                (fun ω ↦ ∫ z, G z ∂P (ω n)) ω) (markovChainMeasure P x) :=
            (hM2int n).const_mul _
          have hB : Integrable (fun ω : ℕ → S ↦
              a ^ (n + 1) * {ω : ℕ → S | (n : ℕ∞) < τ ω}.indicator (fun ω ↦ G (ω (n + 1))) ω -
              a ^ (n + 1) * {ω : ℕ → S | (n : ℕ∞) < τ ω}.indicator
                (fun ω ↦ ∫ z, G z ∂P (ω n)) ω) (markovChainMeasure P x) := hB1.sub hB2
          rw [integral_add hA hB, integral_sub hB1 hB2, integral_const_mul, integral_const_mul, hmk]
          ring
  have h0pos : ∀ ω, ((0 : ℕ) : ℕ∞) < τ ω := fun ω ↦
    lt_of_lt_of_le (by norm_num) (hτ1 ω)
  have hbase : ∫ ω, ((∑ t ∈ Finset.range (0 + 1),
          (if (t : ℕ∞) < τ ω then a ^ t * f (ω t) else 0)) +
          (if ((0 : ℕ) : ℕ∞) < τ ω then a ^ (0 + 1) * ∫ z, G z ∂P (ω 0) else 0))
          ∂markovChainMeasure P x = f x + a * ∫ z, G z ∂P x := by
    have : (fun ω : ℕ → S ↦ (∑ t ∈ Finset.range (0 + 1),
          (if (t : ℕ∞) < τ ω then a ^ t * f (ω t) else 0)) +
          (if ((0 : ℕ) : ℕ∞) < τ ω then a ^ (0 + 1) * ∫ z, G z ∂P (ω 0) else 0)) =
        fun ω ↦ (fun y ↦ f y + a * ∫ z, G z ∂P y) (ω 0) := by
      funext ω
      simp only [zero_add, Finset.sum_range_one, if_pos (h0pos ω), pow_zero, one_mul, pow_one]
    rw [this]
    exact p2mbf_int0 P x (fun y ↦ f y + a * ∫ z, G z ∂P y) (hfm.add (measurable_const.mul hPGm))
  have hinv : ∀ n : ℕ, ∫ ω, ((∑ t ∈ Finset.range (n + 1),
          (if (t : ℕ∞) < τ ω then a ^ t * f (ω t) else 0)) +
          (if (n : ℕ∞) < τ ω then a ^ (n + 1) * ∫ z, G z ∂P (ω n) else 0))
          ∂markovChainMeasure P x ≤ f x + a * ∫ z, G z ∂P x := by
    intro n
    induction n with
    | zero => exact hbase.le
    | succ n ih => exact (hstep n).trans ih
  have hfinal : ∀ n : ℕ, ∫ ω, discountedStoppedSum a f τ ω ∂markovChainMeasure P x ≤
      (f x + a * ∫ z, G z ∂P x) + a ^ (n + 1) * (BG + Bf / (1 - a)) := by
    intro n
    have h1 := hinv n
    rw [integral_add (hYint (n + 1)) (hLint n)] at h1
    have h2 : |∫ ω, (if (n : ℕ∞) < τ ω then a ^ (n + 1) * ∫ z, G z ∂P (ω n) else 0)
        ∂markovChainMeasure P x| ≤ a ^ (n + 1) * BG := by
      refine p2mbf_abs_int_le _ _ _ (fun ω ↦ ?_)
      split_ifs
      · rw [abs_mul, abs_pow, abs_of_nonneg ha0]
        exact mul_le_mul_of_nonneg_left (hPGb _) (pow_nonneg ha0 _)
      · simp only [abs_zero]; exact mul_nonneg (pow_nonneg ha0 _) hBG
    have h3 : |∫ ω, (discountedStoppedSum a f τ ω - ∑ t ∈ Finset.range (n + 1),
        (if (t : ℕ∞) < τ ω then a ^ t * f (ω t) else 0)) ∂markovChainMeasure P x| ≤
        Bf * a ^ (n + 1) / (1 - a) :=
      p2mbf_abs_int_le _ _ _ (fun ω ↦ p2mbf_tail a ha0 ha1 f Bf hBf hf τ ω (n + 1))
    rw [integral_sub (p2mbf_dss_int P x a ha0 ha1 f Bf hBf hf τ hτ hfm) (hYint (n + 1))] at h3
    have h2' := (abs_le.1 h2).1
    have h3' := (abs_le.1 h3).2
    have e : Bf * a ^ (n + 1) / (1 - a) = a ^ (n + 1) * (Bf / (1 - a)) := by ring
    rw [e] at h3'
    nlinarith
  have hlim0 : Filter.Tendsto (fun n : ℕ ↦ a ^ (n + 1)) Filter.atTop (nhds 0) :=
    (tendsto_pow_atTop_nhds_zero_of_lt_one ha0 ha1).comp (Filter.tendsto_add_atTop_nat 1)
  have hlim := (hlim0.mul_const (BG + Bf / (1 - a))).const_add (f x + a * ∫ z, G z ∂P x)
  rw [zero_mul, add_zero] at hlim
  exact ge_of_tendsto' hlim hfinal

open MeasureTheory ProbabilityTheory in
private lemma p2mbf_fix {S : Type*} [MeasurableSpace S]
    (P : Kernel S S) [IsMarkovKernel P] (a : ℝ) (ha0 : 0 ≤ a) (ha1 : a < 1)
    (f : S → ℝ) (Bf : ℝ) (hBf : 0 ≤ Bf) (hf : ∀ y, |f y| ≤ Bf) (hfm : Measurable f) :
    ∃ G : S → ℝ, Measurable G ∧ (∀ y, |G y| ≤ Bf / (1 - a)) ∧
      ∀ y, G y = max 0 (f y + a * ∫ z, G z ∂P y) := by
  have h1a : 0 < 1 - a := by linarith
  let T : (S → ℝ) → (S → ℝ) := fun u y ↦ max 0 (f y + a * ∫ z, u z ∂P y)
  have hmax0 : ∀ p : ℝ, |max 0 p| ≤ |p| := by
    intro p
    rcases le_total 0 p with h | h
    · rw [max_eq_right h]
    · rw [max_eq_left h, abs_zero]; exact abs_nonneg p
  have hmax : ∀ p q : ℝ, |max 0 p - max 0 q| ≤ |p - q| := by
    intro p q
    rw [max_comm 0 p, max_comm 0 q]; exact abs_max_sub_max_le_abs p q 0
  have hcontr : ∀ (u v : S → ℝ) (Bu Bv D : ℝ), Measurable u → Measurable v →
      (∀ z, |u z| ≤ Bu) → (∀ z, |v z| ≤ Bv) →
      (∀ z, |u z - v z| ≤ D) → ∀ y, |T u y - T v y| ≤ a * D := by
    intro u v Bu Bv D hum hvm hu hv huv y
    have hui : Integrable u (P y) := p2mbf_int_of_bound _ _ hum Bu hu
    have hvi : Integrable v (P y) := p2mbf_int_of_bound _ _ hvm Bv hv
    have hI : |∫ z, u z ∂P y - ∫ z, v z ∂P y| ≤ D := by
      rw [← integral_sub hui hvi]; exact p2mbf_abs_int_le (P y) _ D huv
    calc |T u y - T v y|
        ≤ |(f y + a * ∫ z, u z ∂P y) - (f y + a * ∫ z, v z ∂P y)| := hmax _ _
      _ = a * |∫ z, u z ∂P y - ∫ z, v z ∂P y| := by
          rw [show (f y + a * ∫ z, u z ∂P y) - (f y + a * ∫ z, v z ∂P y) =
            a * (∫ z, u z ∂P y - ∫ z, v z ∂P y) by ring, abs_mul, abs_of_nonneg ha0]
      _ ≤ a * D := mul_le_mul_of_nonneg_left hI ha0
  have hbd : ∀ u : S → ℝ, (∀ z, |u z| ≤ Bf / (1 - a)) → ∀ y, |T u y| ≤ Bf / (1 - a) := by
    intro u hu y
    have hI : |∫ z, u z ∂P y| ≤ Bf / (1 - a) := p2mbf_abs_int_le (P y) u _ hu
    calc |T u y| ≤ |f y + a * ∫ z, u z ∂P y| := hmax0 _
      _ ≤ |f y| + |a * ∫ z, u z ∂P y| := abs_add_le _ _
      _ = |f y| + a * |∫ z, u z ∂P y| := by rw [abs_mul, abs_of_nonneg ha0]
      _ ≤ Bf + a * (Bf / (1 - a)) := add_le_add (hf y) (mul_le_mul_of_nonneg_left hI ha0)
      _ = Bf / (1 - a) := by field_simp; ring
  let seq : ℕ → S → ℝ := fun k ↦ T^[k] 0
  have hseq_succ : ∀ k, seq (k + 1) = T (seq k) := fun k ↦ Function.iterate_succ_apply' T k 0
  have hseqb : ∀ k y, |seq k y| ≤ Bf / (1 - a) := by
    intro k
    induction k with
    | zero => intro y; show |(0 : ℝ)| ≤ _; rw [abs_zero]; positivity
    | succ k ih => rw [hseq_succ]; exact hbd _ ih
  have hseqm : ∀ k, Measurable (seq k) := by
    intro k
    induction k with
    | zero => exact (measurable_const : Measurable (fun _ : S ↦ (0 : ℝ)))
    | succ k ih =>
        rw [hseq_succ]
        exact measurable_const.max (hfm.add (measurable_const.mul (p2mbf_kint P ih)))
  have hdiff : ∀ k y, |seq (k + 1) y - seq k y| ≤ Bf * a ^ k := by
    intro k
    induction k with
    | zero =>
        intro y
        show |T 0 y - 0| ≤ Bf * a ^ 0
        have : T 0 y = max 0 (f y + a * ∫ z, (0 : S → ℝ) z ∂P y) := rfl
        rw [this, sub_zero, pow_zero, mul_one]
        simp only [Pi.zero_apply, integral_zero, mul_zero, add_zero]
        exact (hmax0 _).trans (hf y)
    | succ k ih =>
        intro y
        calc |seq (k + 1 + 1) y - seq (k + 1) y| = |T (seq (k + 1)) y - T (seq k) y| := by
              rw [hseq_succ (k + 1), hseq_succ k]
          _ ≤ a * (Bf * a ^ k) := hcontr _ _ _ _ _ (hseqm _) (hseqm _) (hseqb (k + 1)) (hseqb k) ih y
          _ = Bf * a ^ (k + 1) := by ring
  have hgeo : ∀ y k, dist (seq k y) (seq (k + 1) y) ≤ Bf * a ^ k := fun y k ↦ by
    rw [Real.dist_eq, abs_sub_comm]; exact hdiff k y
  have hcauchy : ∀ y, CauchySeq (fun k ↦ seq k y) := fun y ↦
    cauchySeq_of_le_geometric a Bf ha1 (hgeo y)
  choose G hG using fun y ↦ cauchySeq_tendsto_of_complete (hcauchy y)
  have hGm : Measurable G := measurable_of_tendsto_metrizable hseqm (tendsto_pi_nhds.2 hG)
  have hGk : ∀ k y, |seq k y - G y| ≤ Bf * a ^ k / (1 - a) := fun k y ↦ by
    have := dist_le_of_le_geometric_of_tendsto a Bf ha1 (hgeo y) (hG y) k
    rwa [Real.dist_eq] at this
  have hGb : ∀ y, |G y| ≤ Bf / (1 - a) := fun y ↦ by
    have := hGk 0 y
    have h0 : seq 0 y = 0 := rfl
    rwa [h0, zero_sub, abs_neg, pow_zero, mul_one] at this
  refine ⟨G, hGm, hGb, fun y ↦ ?_⟩
  have hT : Filter.Tendsto (fun k ↦ seq (k + 1) y) Filter.atTop (nhds (T G y)) := by
    rw [tendsto_iff_dist_tendsto_zero]
    have hlim : Filter.Tendsto (fun k : ℕ ↦ a * (Bf * a ^ k / (1 - a))) Filter.atTop (nhds 0) := by
      have := (((tendsto_pow_atTop_nhds_zero_of_lt_one ha0 ha1).const_mul Bf).div_const
        (1 - a)).const_mul a
      simpa using this
    refine squeeze_zero (fun _ ↦ dist_nonneg) (fun k ↦ ?_) hlim
    rw [Real.dist_eq, hseq_succ k]
    exact hcontr _ _ _ _ _ (hseqm k) hGm (hseqb k) hGb (hGk k) y
  have hT' : Filter.Tendsto (fun k ↦ seq (k + 1) y) Filter.atTop (nhds (G y)) :=
    (hG y).comp (Filter.tendsto_add_atTop_nat 1)
  exact tendsto_nhds_unique hT' hT

open MeasureTheory ProbabilityTheory BanditAlgorithm in
private lemma p2mbf_hit_le {S : Type*} [MeasurableSpace S] (Z : Set S) (ω : ℕ → S) (n : ℕ) :
    dfbHit Z ω ≤ (n : ℕ∞) ↔ ∃ s : ℕ, 1 ≤ s ∧ s ≤ n ∧ ω s ∈ Z := by
  unfold dfbHit
  constructor
  · intro h
    by_contra hne
    push_neg at hne
    have hle : ((n + 1 : ℕ) : ℕ∞) ≤ ⨅ t : {t : ℕ // 1 ≤ t ∧ ω t ∈ Z}, ((t : ℕ) : ℕ∞) := by
      refine le_iInf fun t ↦ ?_
      have : n < t.1 := by
        by_contra h'
        push_neg at h'
        exact hne t.1 t.2.1 h' t.2.2
      exact_mod_cast this
    have := hle.trans h
    norm_cast at this
    omega
  · rintro ⟨s, hs1, hsn, hs⟩
    exact (iInf_le (fun t : {t : ℕ // 1 ≤ t ∧ ω t ∈ Z} ↦ ((t : ℕ) : ℕ∞)) ⟨s, hs1, hs⟩).trans
      (by exact_mod_cast hsn)

open MeasureTheory ProbabilityTheory BanditAlgorithm in
private lemma p2mbf_hit_stop {S : Type*} [MeasurableSpace S]
    (Z : Set S) (hZ : MeasurableSet Z) : DfbPosStop (dfbHit Z) := by
  refine ⟨fun n ↦ ?_, fun ω ↦ ?_⟩
  · have : {ω : ℕ → S | dfbHit Z ω ≤ (n : ℕ∞)} =
        (fun ω (i : Finset.Iic n) ↦ ω i.1) ⁻¹'
          ⋃ i : Finset.Iic n, {h : (Π _i : Finset.Iic n, S) | 1 ≤ i.1 ∧ h i ∈ Z} := by
      ext ω
      simp only [Set.mem_setOf_eq, p2mbf_hit_le, Set.mem_preimage, Set.mem_iUnion]
      constructor
      · rintro ⟨s, hs1, hsn, hs⟩
        exact ⟨⟨s, Finset.mem_Iic.2 hsn⟩, hs1, hs⟩
      · rintro ⟨⟨s, hs⟩, hs1, hsZ⟩
        exact ⟨s, hs1, Finset.mem_Iic.1 hs, hsZ⟩
    rw [this]
    refine MeasurableSpace.measurableSet_comap.2 ⟨_, ?_, rfl⟩
    refine MeasurableSet.iUnion fun i ↦ ?_
    by_cases hi : 1 ≤ i.1
    · simp only [hi, true_and]
      exact measurable_pi_apply i hZ
    · simp only [hi, false_and, Set.setOf_false]
      exact MeasurableSet.empty
  · unfold dfbHit
    refine le_iInf fun t ↦ ?_
    exact_mod_cast t.2.1

open MeasureTheory ProbabilityTheory BanditAlgorithm in
private lemma p2mbf_upper {S : Type*} [MeasurableSpace S]
    (P : Kernel S S) [IsMarkovKernel P] (a : ℝ) (ha0 : 0 ≤ a) (ha1 : a < 1)
    (f G : S → ℝ) (Bf BG : ℝ) (hBf : 0 ≤ Bf) (hf : ∀ y, |f y| ≤ Bf) (hG : ∀ y, |G y| ≤ BG)
    (hGfix : ∀ y, G y = max 0 (f y + a * ∫ z, G z ∂P y))
    (τ : (ℕ → S) → ℕ∞) (hτ : DfbPosStop τ) (x : S)
    (hfm : Measurable f) (hGm : Measurable G) :
    ∫ ω, discountedStoppedSum a f τ ω ∂markovChainMeasure P x ≤
      f x + a * ∫ z, G z ∂P x := by
  refine p2mbf_core P a ha0 ha1 f G Bf BG hBf hf hG τ hτ.1 hτ.2 (fun ω n ↦ ?_) x hfm hGm
  by_cases h1 : ((n + 1 : ℕ) : ℕ∞) < τ ω
  · have h0 : (n : ℕ∞) < τ ω := lt_trans (by exact_mod_cast Nat.lt_succ_self n) h1
    rw [if_pos h1, if_pos h0, hGfix (ω (n + 1))]
    exact le_max_right _ _
  · rw [if_neg h1]
    split_ifs
    · rw [hGfix (ω (n + 1))]; exact le_max_left _ _
    · exact le_rfl

open MeasureTheory ProbabilityTheory BanditAlgorithm in
private lemma p2mbf_lower {S : Type*} [MeasurableSpace S]
    (P : Kernel S S) [IsMarkovKernel P] (a : ℝ) (ha0 : 0 ≤ a) (ha1 : a < 1)
    (f G : S → ℝ) (Bf BG : ℝ) (hBf : 0 ≤ Bf) (hf : ∀ y, |f y| ≤ Bf) (hG : ∀ y, |G y| ≤ BG)
    (hGfix : ∀ y, G y = max 0 (f y + a * ∫ z, G z ∂P y)) (Z : Set S)
    (hZ1 : ∀ z ∈ Z, f z + a * ∫ w, G w ∂P z ≤ 0)
    (hZ2 : ∀ z ∉ Z, 0 ≤ f z + a * ∫ w, G w ∂P z) (x : S)
    (hZm : MeasurableSet Z) (hfm : Measurable f) (hGm : Measurable G) :
    f x + a * ∫ z, G z ∂P x ≤
      ∫ ω, discountedStoppedSum a f (dfbHit Z) ω ∂markovChainMeasure P x := by
  have hstop := p2mbf_hit_stop Z hZm
  have hcore := p2mbf_core P a ha0 ha1 (fun y ↦ -f y) (fun y ↦ -G y) Bf BG hBf
    (fun y ↦ by simpa using hf y) (fun y ↦ by simpa using hG y) (dfbHit Z) hstop.1 hstop.2
    ?_ x hfm.neg hGm.neg
  · simp only [p2mbf_dss_neg, integral_neg, mul_neg] at hcore
    linarith
  · intro ω n
    simp only [integral_neg, mul_neg]
    by_cases h1 : ((n + 1 : ℕ) : ℕ∞) < dfbHit Z ω
    · have h0 : (n : ℕ∞) < dfbHit Z ω := lt_trans (by exact_mod_cast Nat.lt_succ_self n) h1
      rw [if_pos h1, if_pos h0]
      have hnot : ω (n + 1) ∉ Z := by
        intro hin
        exact (not_le.2 h1) ((p2mbf_hit_le Z ω (n + 1)).2 ⟨n + 1, by omega, le_rfl, hin⟩)
      have hK := hZ2 _ hnot
      rw [hGfix (ω (n + 1)), max_eq_right hK]
      linarith
    · rw [if_neg h1]
      by_cases h0 : (n : ℕ∞) < dfbHit Z ω
      · rw [if_pos h0]
        have hin : ω (n + 1) ∈ Z := by
          obtain ⟨s, hs1, hsn, hs⟩ := (p2mbf_hit_le Z ω (n + 1)).1 (not_lt.1 h1)
          by_cases hsn' : s ≤ n
          · exact absurd ((p2mbf_hit_le Z ω n).2 ⟨s, hs1, hsn', hs⟩) (not_le.2 h0)
          · have : s = n + 1 := by omega
            rw [← this]; exact hs
        have hK := hZ1 _ hin
        rw [hGfix (ω (n + 1)), max_eq_left hK]
        simp
      · rw [if_neg h0]

private lemma dfb_sup_eq {A : Set ℝ} {g : ℝ} (hup : ∀ v ∈ A, v ≤ g) (h0 : 0 ≤ g)
    (hatt : g = 0 ∨ g ∈ A) : sSup (insert 0 A) = g := by
  have hup' : ∀ v ∈ insert (0 : ℝ) A, v ≤ g := by
    rintro v (rfl | hv)
    · exact h0
    · exact hup v hv
  have hbdd : BddAbove (insert (0 : ℝ) A) := ⟨g, hup'⟩
  refine le_antisymm (csSup_le (Set.insert_nonempty _ _) hup') ?_
  rcases hatt with h | h
  · rw [h]; exact le_csSup hbdd (Set.mem_insert _ _)
  · exact le_csSup hbdd (Set.mem_insert_of_mem _ h)

open MeasureTheory ProbabilityTheory BanditAlgorithm in
/-- BELL (with a bound): Bellman equation for the retirement value. -/
theorem DF742747B_bell' {S : Type*} [MeasurableSpace S] (P : Kernel S S) [IsMarkovKernel P]
    {r : S → ℝ} (hr : Measurable r) (hrb : WeberGittins.Suboptimality.RewardsNonnegBounded r)
    {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1) (p : ℝ) :
    Measurable (gittinsRetirementValue P r α p) ∧
    (∃ B : ℝ, ∀ y, |gittinsRetirementValue P r α p y| ≤ B) ∧
    ∀ y, gittinsRetirementValue P r α p y =
      max 0 (r y - p + α * ∫ z, gittinsRetirementValue P r α p z ∂P y) := by
  obtain ⟨hr0, C, hC⟩ := hrb
  let f : S → ℝ := fun y ↦ r y - p
  have hfm : Measurable f := hr.sub measurable_const
  have hf : ∀ y, |f y| ≤ |C| + |p| := fun y ↦ by
    have h1 := hr0 y
    have h2 := hC y
    refine abs_le.2 ⟨?_, ?_⟩
    · show -(|C| + |p|) ≤ r y - p
      linarith [abs_nonneg C, neg_abs_le p, le_abs_self p]
    · show r y - p ≤ |C| + |p|
      linarith [le_abs_self C, neg_le_abs p]
  have hBf : 0 ≤ |C| + |p| := by positivity
  obtain ⟨G, hGm, hGb, hGfix⟩ := p2mbf_fix P α hα0.le hα1 f (|C| + |p|) hBf hf hfm
  have hPGm : Measurable (fun y ↦ ∫ z, G z ∂P y) := p2mbf_kint P hGm
  have key : ∀ y, gittinsRetirementValue P r α p y = G y := by
    intro y
    unfold gittinsRetirementValue
    have hupper : ∀ τ : (ℕ → S) → ℕ∞, IsTrajStoppingTime τ → (∀ ω, 1 ≤ τ ω) →
        ∫ ω, discountedStoppedSum α f τ ω ∂markovChainMeasure P y ≤ f y + α * ∫ z, G z ∂P y :=
      fun τ hτ hτ1 ↦ p2mbf_upper P α hα0.le hα1 f G _ _ hBf hf hGb hGfix τ ⟨hτ, hτ1⟩ y hfm hGm
    refine dfb_sup_eq ?_ ?_ ?_
    · rintro v ⟨τ, hτ, hτ1, rfl⟩
      refine (hupper τ hτ hτ1).trans ?_
      rw [hGfix y]; exact le_max_right _ _
    · rw [hGfix y]; exact le_max_left _ _
    · rcases le_or_gt (f y + α * ∫ z, G z ∂P y) 0 with h | h
      · left; rw [hGfix y, max_eq_left h]
      · right
        let Z : Set S := {z | f z + α * ∫ w, G w ∂P z ≤ 0}
        have hZm : MeasurableSet Z := measurableSet_le (hfm.add (measurable_const.mul hPGm))
          measurable_const
        have hstop := p2mbf_hit_stop Z hZm
        have hlow := p2mbf_lower P α hα0.le hα1 f G _ _ hBf hf hGb hGfix Z (fun z hz ↦ hz)
          (fun z hz ↦ le_of_lt (not_le.1 hz)) y hZm hfm hGm
        refine ⟨dfbHit Z, hstop.1, hstop.2, ?_⟩
        rw [hGfix y, max_eq_right h.le]
        exact le_antisymm hlow (hupper _ hstop.1 hstop.2)
  have hfun : gittinsRetirementValue P r α p = G := funext key
  refine ⟨hfun ▸ hGm, ⟨_, fun y ↦ by rw [hfun]; exact hGb y⟩, fun y ↦ ?_⟩
  rw [hfun]
  exact hGfix y

open MeasureTheory ProbabilityTheory BanditAlgorithm in
/-- BELL: Bellman equation for the retirement value (measurable bounded nonnegative `r`). -/
theorem DF742747B_bell {S : Type*} [MeasurableSpace S] (P : Kernel S S) [IsMarkovKernel P]
    {r : S → ℝ} (hr : Measurable r) (hrb : WeberGittins.Suboptimality.RewardsNonnegBounded r)
    {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1) (p : ℝ) :
    Measurable (gittinsRetirementValue P r α p) ∧
    ∀ y, gittinsRetirementValue P r α p y =
      max 0 (r y - p + α * ∫ z, gittinsRetirementValue P r α p z ∂P y) :=
  ⟨(DF742747B_bell' P hr hrb hα0 hα1 p).1, (DF742747B_bell' P hr hrb hα0 hα1 p).2.2⟩

open MeasureTheory ProbabilityTheory BanditAlgorithm in
private lemma dfb_parts {S : Type*} [MeasurableSpace S] (P : Kernel S S) [IsMarkovKernel P]
    {r : S → ℝ} (hr : Measurable r) (hr0 : ∀ y, 0 ≤ r y) {C : ℝ} (hC : ∀ y, r y ≤ C)
    {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1) (c : ℝ) (y : S)
    (τ : (ℕ → S) → ℕ∞) (hτ : IsTrajStoppingTime τ) (hτ1 : ∀ ω, 1 ≤ τ ω) :
    (∫ ω, discountedStoppedSum α (fun y ↦ r y - c) τ ω ∂markovChainMeasure P y =
      (∫ ω, discountedStoppedSum α r τ ω ∂markovChainMeasure P y) -
        c * ∫ ω, discountedStoppedSum α (fun _ ↦ (1 : ℝ)) τ ω ∂markovChainMeasure P y) ∧
    1 ≤ ∫ ω, discountedStoppedSum α (fun _ ↦ (1 : ℝ)) τ ω ∂markovChainMeasure P y ∧
    ∫ ω, discountedStoppedSum α (fun _ ↦ (1 : ℝ)) τ ω ∂markovChainMeasure P y ≤ 1 / (1 - α) ∧
    ∫ ω, discountedStoppedSum α r τ ω ∂markovChainMeasure P y ≤
      C * ∫ ω, discountedStoppedSum α (fun _ ↦ (1 : ℝ)) τ ω ∂markovChainMeasure P y := by
  haveI := p2mbf_prob P y
  have hC0 : 0 ≤ C := (hr0 y).trans (hC y)
  have hrb : ∀ z, |r z| ≤ C := fun z ↦ abs_le.2 ⟨by linarith [hr0 z], hC z⟩
  have h1b : ∀ z : S, |(fun _ : S ↦ (1 : ℝ)) z| ≤ 1 := fun z ↦ by simp
  have hs_r : ∀ ω, Summable (fun t : ℕ ↦ if (t : ℕ∞) < τ ω then α ^ t * r (ω t) else 0) :=
    fun ω ↦ p2mbf_summable α hα0.le hα1 r C hC0 hrb τ ω
  have hs_1 : ∀ ω, Summable (fun t : ℕ ↦
      if (t : ℕ∞) < τ ω then α ^ t * (fun _ : S ↦ (1 : ℝ)) (ω t) else 0) :=
    fun ω ↦ p2mbf_summable α hα0.le hα1 _ 1 zero_le_one h1b τ ω
  have hIr := p2mbf_dss_int P y α hα0.le hα1 r C hC0 hrb τ hτ hr
  have hI1 := p2mbf_dss_int P y α hα0.le hα1 (fun _ ↦ (1 : ℝ)) 1 zero_le_one h1b τ hτ
    measurable_const
  have hpt : ∀ ω, discountedStoppedSum α (fun y ↦ r y - c) τ ω =
      discountedStoppedSum α r τ ω - c * discountedStoppedSum α (fun _ ↦ (1 : ℝ)) τ ω := by
    intro ω
    unfold discountedStoppedSum
    rw [← tsum_mul_left, ← (hs_r ω).tsum_sub ((hs_1 ω).mul_left c)]
    refine tsum_congr fun t ↦ ?_
    split_ifs <;> ring
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp_rw [hpt]
    rw [integral_sub hIr (hI1.const_mul c), integral_const_mul]
  · have hge : ∀ ω, (1 : ℝ) ≤ discountedStoppedSum α (fun _ ↦ (1 : ℝ)) τ ω := by
      intro ω
      have h0 : (0 : ℕ∞) < τ ω := lt_of_lt_of_le (by norm_num) (hτ1 ω)
      have := (hs_1 ω).le_tsum 0 (fun t _ ↦ by split_ifs <;> positivity)
      simpa [discountedStoppedSum, h0] using this
    have := integral_mono (integrable_const (1 : ℝ)) hI1 hge
    simpa using this
  · have hb : ∀ ω, |discountedStoppedSum α (fun _ ↦ (1 : ℝ)) τ ω| ≤ 1 / (1 - α) := fun ω ↦
      p2mbf_dss_bound α hα0.le hα1 (fun _ ↦ (1 : ℝ)) 1 zero_le_one h1b τ ω
    exact (le_abs_self _).trans (p2mbf_abs_int_le _ _ _ hb)
  · rw [← integral_const_mul]
    refine integral_mono hIr (hI1.const_mul C) fun ω ↦ ?_
    show discountedStoppedSum α r τ ω ≤ C * discountedStoppedSum α (fun _ ↦ (1 : ℝ)) τ ω
    unfold discountedStoppedSum
    rw [← tsum_mul_left]
    refine (hs_r ω).tsum_le_tsum (fun t ↦ ?_) ((hs_1 ω).mul_left C)
    split_ifs
    · have h1 := hC (ω t)
      have h2 := pow_nonneg hα0.le t
      nlinarith
    · simp

open MeasureTheory ProbabilityTheory BanditAlgorithm in
private lemma dfb_gset {S : Type*} [MeasurableSpace S] (P : Kernel S S) [IsMarkovKernel P]
    {r : S → ℝ} (hr : Measurable r) (hrb : WeberGittins.Suboptimality.RewardsNonnegBounded r)
    {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1) (z : S) :
    BddAbove {g : ℝ | ∃ τ : (ℕ → S) → ℕ∞, IsTrajStoppingTime τ ∧ (∀ ω, 1 ≤ τ ω) ∧
      g = (∫ ω, discountedStoppedSum α r τ ω ∂markovChainMeasure P z) /
        (∫ ω, discountedStoppedSum α (fun _ ↦ 1) τ ω ∂markovChainMeasure P z)} ∧
    {g : ℝ | ∃ τ : (ℕ → S) → ℕ∞, IsTrajStoppingTime τ ∧ (∀ ω, 1 ≤ τ ω) ∧
      g = (∫ ω, discountedStoppedSum α r τ ω ∂markovChainMeasure P z) /
        (∫ ω, discountedStoppedSum α (fun _ ↦ 1) τ ω ∂markovChainMeasure P z)}.Nonempty := by
  obtain ⟨hr0, C, hC⟩ := hrb
  refine ⟨⟨C, ?_⟩, ⟨_, fun _ ↦ 1, fun n ↦ MeasurableSet.const _, fun _ ↦ le_rfl, rfl⟩⟩
  rintro g ⟨τ, hτ, hτ1, rfl⟩
  obtain ⟨-, hD1, -, hNC⟩ := dfb_parts P hr hr0 hC hα0 hα1 0 z τ hτ hτ1
  rw [div_le_iff₀ (by linarith)]
  exact hNC

open MeasureTheory ProbabilityTheory BanditAlgorithm in
/-- The retirement value vanishes once the charge reaches the index. -/
theorem DF742747B_ret_zero {S : Type*} [MeasurableSpace S] (P : Kernel S S) [IsMarkovKernel P]
    {r : S → ℝ} (hr : Measurable r) (hrb : WeberGittins.Suboptimality.RewardsNonnegBounded r)
    {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1) (c : ℝ) (z : S) (hz : gittinsIndex P r α z ≤ c) :
    gittinsRetirementValue P r α c z = 0 := by
  have hbdd := (dfb_gset P hr hrb hα0 hα1 z).1
  obtain ⟨hr0, C, hC⟩ := hrb
  unfold gittinsRetirementValue
  refine dfb_sup_eq ?_ le_rfl (Or.inl rfl)
  rintro v ⟨τ, hτ, hτ1, rfl⟩
  obtain ⟨he, hD1, -, -⟩ := dfb_parts P hr hr0 hC hα0 hα1 c z τ hτ hτ1
  have hratio := le_csSup hbdd ⟨τ, hτ, hτ1, rfl⟩
  have hratio' : _ ≤ gittinsIndex P r α z := hratio
  rw [div_le_iff₀ (by linarith)] at hratio'
  rw [he]
  nlinarith

open MeasureTheory ProbabilityTheory BanditAlgorithm in
/-- STEP: per-step fair-game identity for a charge at most the index. -/
theorem DF742747B_step {S : Type*} [MeasurableSpace S] (P : Kernel S S) [IsMarkovKernel P]
    {r : S → ℝ} (hr : Measurable r) (hrb : WeberGittins.Suboptimality.RewardsNonnegBounded r)
    {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1) (p : ℝ) (y : S) (hp : p ≤ gittinsIndex P r α y) :
    gittinsRetirementValue P r α p y =
      r y - p + α * ∫ z, gittinsRetirementValue P r α (min p (gittinsIndex P r α z)) z ∂P y := by
  obtain ⟨hRm, ⟨BR, hBR⟩, hR⟩ := DF742747B_bell' P hr hrb hα0 hα1 p
  have hcongr : (fun z ↦ gittinsRetirementValue P r α (min p (gittinsIndex P r α z)) z) =
      gittinsRetirementValue P r α p := by
    funext z
    rcases le_total p (gittinsIndex P r α z) with h | h
    · rw [min_eq_left h]
    · rw [min_eq_right h, DF742747B_ret_zero P hr hrb hα0 hα1 _ z le_rfl,
        DF742747B_ret_zero P hr hrb hα0 hα1 _ z h]
  have hne := (dfb_gset P hr hrb hα0 hα1 y).2
  obtain ⟨hr0, C, hC⟩ := hrb
  rw [hcongr, hR y, max_eq_right]
  obtain ⟨W, hW⟩ : ∃ W, W = r y - p + α * ∫ z, gittinsRetirementValue P r α p z ∂P y := ⟨_, rfl⟩
  rw [← hW]
  by_contra hneg
  push_neg at hneg
  have h1a : 0 < 1 - α := by linarith
  have hε : 0 < (-W) * (1 - α) / 2 := by
    have : 0 < -W := by linarith
    positivity
  obtain ⟨g, ⟨τ, hτ, hτ1, rfl⟩, hg⟩ := exists_lt_of_lt_csSup hne
    (show gittinsIndex P r α y - (-W) * (1 - α) / 2 < gittinsIndex P r α y by linarith)
  obtain ⟨he, hD1, hDu, -⟩ := dfb_parts P hr hr0 hC hα0 hα1 p y τ hτ hτ1
  obtain ⟨N, hN⟩ : ∃ N, N = ∫ ω, discountedStoppedSum α r τ ω ∂markovChainMeasure P y := ⟨_, rfl⟩
  obtain ⟨D, hD⟩ : ∃ D, D =
      ∫ ω, discountedStoppedSum α (fun _ ↦ (1 : ℝ)) τ ω ∂markovChainMeasure P y := ⟨_, rfl⟩
  rw [← hN, ← hD] at he
  rw [← hD] at hD1 hDu
  have hg' : gittinsIndex P r α y - (-W) * (1 - α) / 2 < N / D := by
    rw [hN, hD]; exact hg
  have hDpos : 0 < D := by linarith
  rw [lt_div_iff₀ hDpos] at hg'
  have hfB : ∀ z, |(fun z ↦ r z - p) z| ≤ |C| + |p| := fun z ↦ by
    have h1 := hr0 z
    have h2 := hC z
    refine abs_le.2 ⟨?_, ?_⟩
    · show -(|C| + |p|) ≤ r z - p
      linarith [abs_nonneg C, neg_abs_le p, le_abs_self p]
    · show r z - p ≤ |C| + |p|
      linarith [le_abs_self C, neg_le_abs p]
  have hup := p2mbf_upper P α hα0.le hα1 (fun z ↦ r z - p) (gittinsRetirementValue P r α p)
    (|C| + |p|) BR (by positivity) hfB hBR hR τ ⟨hτ, hτ1⟩ y (hr.sub measurable_const) hRm
  have hup' : N - p * D ≤ W := by
    rw [hW, ← he]; exact hup
  have hDu' : D * (1 - α) ≤ 1 := (le_div_iff₀ h1a).1 hDu
  have hεD : (-W) * (1 - α) / 2 * D ≤ (-W) / 2 := by
    have : 0 ≤ -W / 2 := by linarith
    nlinarith [mul_le_mul_of_nonneg_left hDu' this]
  nlinarith [mul_nonneg (sub_nonneg.2 hp) hDpos.le]

/-! ## K1 support (session 5) -/

private lemma dfb_fB {S : Type*} {r : S → ℝ} (hr0 : ∀ y, 0 ≤ r y) {C : ℝ} (hC : ∀ y, r y ≤ C)
    (q : ℝ) (z : S) : |r z - q| ≤ |C| + |q| := by
  have h1 := hr0 z
  have h2 := hC z
  refine abs_le.2 ⟨?_, ?_⟩
  · linarith [abs_nonneg C, neg_abs_le q, le_abs_self q]
  · linarith [le_abs_self C, neg_le_abs q]

open MeasureTheory ProbabilityTheory BanditAlgorithm in
private lemma dfb_dss_nonneg {S : Type*} {α : ℝ} (hα0 : 0 < α) (f : S → ℝ) (hf : ∀ y, 0 ≤ f y)
    (τ : (ℕ → S) → ℕ∞) (ω : ℕ → S) : 0 ≤ discountedStoppedSum α f τ ω :=
  tsum_nonneg fun t ↦ by
    split_ifs
    · exact mul_nonneg (pow_nonneg hα0.le t) (hf _)
    · exact le_rfl

open MeasureTheory ProbabilityTheory BanditAlgorithm in
private lemma dfb_ret_bdd {S : Type*} [MeasurableSpace S] (P : Kernel S S) [IsMarkovKernel P]
    {r : S → ℝ} (hr0 : ∀ y, 0 ≤ r y) {C : ℝ} (hC : ∀ y, r y ≤ C)
    {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1) (q : ℝ) (y : S) :
    ∀ v ∈ insert (0 : ℝ) {v : ℝ | ∃ τ : (ℕ → S) → ℕ∞, IsTrajStoppingTime τ ∧ (∀ ω, 1 ≤ τ ω) ∧
      v = ∫ ω, discountedStoppedSum α (fun y ↦ r y - q) τ ω ∂markovChainMeasure P y},
      v ≤ (|C| + |q|) / (1 - α) := by
  haveI := p2mbf_prob P y
  have h1a : 0 < 1 - α := by linarith
  rintro v (rfl | ⟨τ, hτ, hτ1, rfl⟩)
  · positivity
  · exact (le_abs_self _).trans (p2mbf_abs_int_le _ _ _ (fun ω ↦
      p2mbf_dss_bound α hα0.le hα1 (fun z ↦ r z - q) _ (by positivity) (dfb_fB hr0 hC q) τ ω))

open MeasureTheory ProbabilityTheory BanditAlgorithm in
/-- Bounds for the retirement value. -/
theorem DF742747B_ret_bounds {S : Type*} [MeasurableSpace S] (P : Kernel S S) [IsMarkovKernel P]
    {r : S → ℝ} (hr0 : ∀ y, 0 ≤ r y) {C : ℝ} (hC : ∀ y, r y ≤ C)
    {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1) (q : ℝ) (y : S) :
    0 ≤ gittinsRetirementValue P r α q y ∧
      gittinsRetirementValue P r α q y ≤ (|C| + |q|) / (1 - α) := by
  have hb := dfb_ret_bdd P hr0 hC hα0 hα1 q y
  exact ⟨le_csSup ⟨_, hb⟩ (Set.mem_insert _ _), csSup_le (Set.insert_nonempty _ _) hb⟩

open MeasureTheory ProbabilityTheory BanditAlgorithm in
/-- The retirement value is `1/(1-α)`-Lipschitz in the charge. -/
theorem DF742747B_ret_lip {S : Type*} [MeasurableSpace S] (P : Kernel S S) [IsMarkovKernel P]
    {r : S → ℝ} (hr : Measurable r) (hr0 : ∀ y, 0 ≤ r y) {C : ℝ} (hC : ∀ y, r y ≤ C)
    {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1) (p q : ℝ) (y : S) :
    gittinsRetirementValue P r α p y ≤ gittinsRetirementValue P r α q y + |p - q| / (1 - α) := by
  have hbq := dfb_ret_bdd P hr0 hC hα0 hα1 q y
  have h1a : 0 < 1 - α := by linarith
  have hL : 0 ≤ |p - q| / (1 - α) := by positivity
  have hq0 := (DF742747B_ret_bounds P hr0 hC hα0 hα1 q y).1
  refine (csSup_le (Set.insert_nonempty _ _) ?_ : (sSup _ : ℝ) ≤ _)
  rintro v (rfl | ⟨τ, hτ, hτ1, rfl⟩)
  · linarith
  · obtain ⟨hep, hD1, hDu, -⟩ := dfb_parts P hr hr0 hC hα0 hα1 p y τ hτ hτ1
    obtain ⟨heq, -, -, -⟩ := dfb_parts P hr hr0 hC hα0 hα1 q y τ hτ hτ1
    have hmem : ∫ ω, discountedStoppedSum α (fun y ↦ r y - q) τ ω ∂markovChainMeasure P y ≤
        gittinsRetirementValue P r α q y :=
      le_csSup ⟨_, hbq⟩ (Set.mem_insert_of_mem _ ⟨τ, hτ, hτ1, rfl⟩)
    rw [hep]
    rw [heq] at hmem
    have hDu' := (le_div_iff₀ h1a).1 hDu
    have hDL : |p - q| * (∫ ω, discountedStoppedSum α (fun _ ↦ (1 : ℝ)) τ ω
        ∂markovChainMeasure P y) ≤ |p - q| / (1 - α) := by
      rw [le_div_iff₀ h1a]
      nlinarith [mul_le_mul_of_nonneg_left hDu' (abs_nonneg (p - q))]
    have hqp : q - p ≤ |p - q| := by linarith [neg_abs_le (p - q)]
    nlinarith [mul_le_mul_of_nonneg_right hqp (show (0 : ℝ) ≤ _ from le_trans zero_le_one hD1)]

open MeasureTheory ProbabilityTheory BanditAlgorithm in
/-- Joint measurability of the retirement value in (charge, state). -/
theorem DF742747B_ret_meas2 {S : Type*} [MeasurableSpace S] (P : Kernel S S) [IsMarkovKernel P]
    {r : S → ℝ} (hr : Measurable r) (hrb : WeberGittins.Suboptimality.RewardsNonnegBounded r)
    {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1) :
    Measurable (fun z : ℝ × S ↦ gittinsRetirementValue P r α z.1 z.2) := by
  obtain ⟨hr0, C, hC⟩ := id hrb
  have h1a : 0 < 1 - α := by linarith
  have hcont : ∀ y, Continuous (fun p ↦ gittinsRetirementValue P r α p y) := by
    intro y
    rw [Metric.continuous_iff]
    intro b ε hε
    refine ⟨ε * (1 - α), by positivity, fun a ha ↦ ?_⟩
    rw [Real.dist_eq] at ha ⊢
    have h1 := DF742747B_ret_lip P hr hr0 hC hα0 hα1 a b y
    have h2 := DF742747B_ret_lip P hr hr0 hC hα0 hα1 b a y
    rw [abs_sub_comm b a] at h2
    have : |a - b| / (1 - α) < ε := by rw [div_lt_iff₀ h1a]; exact ha
    rw [abs_lt]; constructor <;> linarith
  exact measurable_uncurry_of_continuous_of_measurable
    (u := fun p y ↦ gittinsRetirementValue P r α p y) hcont
    (fun p ↦ (DF742747B_bell P hr hrb hα0 hα1 p).1)

open MeasureTheory ProbabilityTheory BanditAlgorithm in
/-- The Gittins index lies in `[0, C]`. -/
theorem DF742747B_gi_bounds {S : Type*} [MeasurableSpace S] (P : Kernel S S) [IsMarkovKernel P]
    {r : S → ℝ} (hr : Measurable r) (hr0 : ∀ y, 0 ≤ r y) {C : ℝ} (hC : ∀ y, r y ≤ C)
    {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1) (z : S) :
    0 ≤ gittinsIndex P r α z ∧ gittinsIndex P r α z ≤ C := by
  obtain ⟨hbdd, hne⟩ := dfb_gset P hr ⟨hr0, C, hC⟩ hα0 hα1 z
  refine ⟨?_, ?_⟩
  · obtain ⟨_, τ, hτ, hτ1, rfl⟩ := hne
    refine le_trans ?_ (le_csSup hbdd ⟨τ, hτ, hτ1, rfl⟩)
    exact div_nonneg (integral_nonneg fun ω ↦ dfb_dss_nonneg hα0 r hr0 τ ω)
      (integral_nonneg fun ω ↦ dfb_dss_nonneg hα0 _ (fun _ ↦ zero_le_one) τ ω)
  · refine (csSup_le hne ?_ : (sSup _ : ℝ) ≤ _)
    rintro g ⟨τ, hτ, hτ1, rfl⟩
    obtain ⟨-, hD1, -, hNC⟩ := dfb_parts P hr hr0 hC hα0 hα1 0 z τ hτ hτ1
    rw [div_le_iff₀ (by linarith)]
    exact hNC

/-- Truncation of a bandit history is measurable. -/
theorem DF742747B_trunc_meas {k n : ℕ} {S : Type*} [MeasurableSpace S] :
    Measurable (BanditAlgorithm.truncateMarkovBanditHistory (k := k) (n := n) (S := S)) := by
  unfold BanditAlgorithm.truncateMarkovBanditHistory
  refine Measurable.prodMk ?_ ?_
  · exact measurable_pi_lambda _ (fun i ↦ (measurable_pi_apply _).comp measurable_fst)
  · exact measurable_fst.comp ((measurable_pi_apply _).comp measurable_fst)

open BanditAlgorithm in
/-- Prevailing charges are measurable functions of the history. -/
theorem DF742747B_chpc_meas {k : ℕ} {S : Type*} [MeasurableSpace S] {g : S → ℝ}
    (hg : Measurable g) : ∀ (n : ℕ) (i : Fin k),
      Measurable (fun h : MarkovBanditHistory k S n ↦ currentHistoryPrevailingCharge g n h i)
  | 0, i => hg.comp ((measurable_pi_apply i).comp measurable_snd)
  | n + 1, i => by
      have e : (fun h : MarkovBanditHistory k S (n + 1) ↦
          currentHistoryPrevailingCharge g (n + 1) h i) = fun h ↦
          min (currentHistoryPrevailingCharge g n (truncateMarkovBanditHistory h) i)
            (g (h.2 i)) := by
        funext h; rfl
      rw [e]
      exact ((DF742747B_chpc_meas hg n i).comp DF742747B_trunc_meas).min
        (hg.comp ((measurable_pi_apply i).comp measurable_snd))

open BanditAlgorithm in
/-- Prevailing charges stay in `[lo, hi]` when the index does. -/
theorem DF742747B_chpc_bounds {k : ℕ} {S : Type*} (g : S → ℝ) {lo hi : ℝ}
    (hg : ∀ y, lo ≤ g y ∧ g y ≤ hi) : ∀ (n : ℕ) (h : MarkovBanditHistory k S n) (i : Fin k),
      lo ≤ currentHistoryPrevailingCharge g n h i ∧ currentHistoryPrevailingCharge g n h i ≤ hi
  | 0, h, i => hg _
  | n + 1, h, i => by
      simp only [currentHistoryPrevailingCharge]
      exact ⟨le_min (DF742747B_chpc_bounds g hg n _ i).1 (hg _).1,
        (min_le_right _ _).trans (hg _).2⟩

open BanditAlgorithm in
/-- The prevailing charge never exceeds the current index. -/
theorem DF742747B_chpc_le {k : ℕ} {S : Type*} (g : S → ℝ) :
    ∀ (n : ℕ) (h : MarkovBanditHistory k S n) (i : Fin k),
      currentHistoryPrevailingCharge g n h i ≤ g (h.2 i)
  | 0, _, _ => le_rfl
  | n + 1, h, i => by
      simp only [currentHistoryPrevailingCharge]
      exact min_le_right _ _

open BanditAlgorithm in
/-- Prevailing charges after one more round. -/
theorem DF742747B_chpc_snoc {k n : ℕ} {S : Type*} (g : S → ℝ) (h : MarkovBanditHistory k S n)
    (a : Fin k) (y : S) (i : Fin k) :
    currentHistoryPrevailingCharge g (n + 1)
      ((Fin.snoc (α := fun _ ↦ (Fin k → S) × Fin k) h.1 (h.2, a),
        Function.update h.2 a y) : MarkovBanditHistory k S (n + 1)) i =
      if i = a then min (currentHistoryPrevailingCharge g n h a) (g y)
      else currentHistoryPrevailingCharge g n h i := by
  have htr : truncateMarkovBanditHistory
      ((Fin.snoc (α := fun _ ↦ (Fin k → S) × Fin k) h.1 (h.2, a),
        Function.update h.2 a y) : MarkovBanditHistory k S (n + 1)) = h := by
    simp [truncateMarkovBanditHistory, Fin.init_snoc, Fin.snoc_last]
  simp only [currentHistoryPrevailingCharge, htr]
  split_ifs with hi
  · subst hi; simp
  · rw [Function.update_of_ne hi]; exact min_eq_left (DF742747B_chpc_le g n h i)

open BanditAlgorithm in
theorem DF742747B_trunc_snoc {k n : ℕ} {S : Type*} (p : MarkovBanditHistory k S n × (Fin k × S)) :
    truncateMarkovBanditHistory
      ((Fin.snoc (α := fun _ ↦ (Fin k → S) × Fin k) p.1.1 (p.1.2, p.2.1),
        Function.update p.1.2 p.2.1 p.2.2) : MarkovBanditHistory k S (n + 1)) = p.1 := by
  simp [truncateMarkovBanditHistory, Fin.init_snoc, Fin.snoc_last]

/-- A finite sum of uniformly bounded terms. -/
theorem DF742747B_sum_bound {k : ℕ} (f : Fin k → ℝ) {B : ℝ} (hf : ∀ i, |f i| ≤ B)
    (s : Finset (Fin k)) : |∑ i ∈ s, f i| ≤ k * B := by
  calc |∑ i ∈ s, f i| ≤ ∑ i ∈ s, |f i| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i, |f i| :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun i _ _ ↦ abs_nonneg _)
    _ ≤ ∑ _i : Fin k, B := Finset.sum_le_sum fun i _ ↦ hf i
    _ = k * B := by simp

/-- Bound for the combination used in the one-step identity. -/
theorem DF742747B_comb_bound (β a b c d e A B' C' D' E' : ℝ) (ha : |a| ≤ A) (hb : |b| ≤ B')
    (hc : |c| ≤ C') (hd : |d| ≤ D') (he : |e| ≤ E') :
    |β * a + (b + (1 - β) * c - d - e)| ≤ |β| * A + B' + |1 - β| * C' + D' + E' := by
  have h1 : |β * a| ≤ |β| * A := by
    rw [abs_mul]; exact mul_le_mul_of_nonneg_left ha (abs_nonneg β)
  have h3 : |(1 - β) * c| ≤ |1 - β| * C' := by
    rw [abs_mul]; exact mul_le_mul_of_nonneg_left hc (abs_nonneg _)
  refine abs_le.2 ⟨?_, ?_⟩ <;>
  linarith [neg_abs_le (β * a), le_abs_self (β * a), neg_abs_le ((1 - β) * c),
    le_abs_self ((1 - β) * c), neg_abs_le b, le_abs_self b, neg_abs_le d, le_abs_self d,
    neg_abs_le e, le_abs_self e]

open MeasureTheory ProbabilityTheory BanditAlgorithm in
theorem DF742747B_T_meas {k : ℕ} {S : Type*} [MeasurableSpace S] (P : Kernel S S)
    [IsMarkovKernel P] {r : S → ℝ} (hr : Measurable r)
    (hrb : WeberGittins.Suboptimality.RewardsNonnegBounded r)
    {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hγ : Measurable (gittinsIndex P r β))
    (m : ℕ) (i : Fin k) :
    Measurable (fun h : MarkovBanditHistory k S m ↦ gittinsRetirementValue P r β
        (currentHistoryPrevailingCharge (gittinsIndex P r β) m h i) (h.2 i)) := by
  have hp : Measurable (fun h : MarkovBanditHistory k S m ↦
      (currentHistoryPrevailingCharge (gittinsIndex P r β) m h i, h.2 i)) :=
    (DF742747B_chpc_meas hγ m i).prodMk ((measurable_pi_apply i).comp measurable_snd)
  have := (DF742747B_ret_meas2 P hr hrb hβ0 hβ1).comp hp
  exact this

open MeasureTheory ProbabilityTheory BanditAlgorithm in
theorem DF742747B_T_bound {k : ℕ} {S : Type*} [MeasurableSpace S] (P : Kernel S S)
    [IsMarkovKernel P] {r : S → ℝ} (hr : Measurable r) (hr0 : ∀ y, 0 ≤ r y) {C : ℝ}
    (hC : ∀ y, r y ≤ C) {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (m : ℕ)
    (h : MarkovBanditHistory k S m) (i : Fin k) :
    |gittinsRetirementValue P r β
        (currentHistoryPrevailingCharge (gittinsIndex P r β) m h i) (h.2 i)| ≤
      (|C| + |C|) / (1 - β) := by
  have h1a : 0 < 1 - β := by linarith
  have hgi := DF742747B_gi_bounds P hr hr0 hC hβ0 hβ1
  have hq := DF742747B_chpc_bounds (k := k) (gittinsIndex P r β) hgi m h i
  obtain ⟨h0, h1⟩ := DF742747B_ret_bounds P hr0 hC hβ0 hβ1
    (currentHistoryPrevailingCharge (gittinsIndex P r β) m h i) (h.2 i)
  rw [abs_of_nonneg h0]
  refine h1.trans (div_le_div_of_nonneg_right ?_ h1a.le)
  rw [abs_of_nonneg hq.1]; linarith [le_abs_self C]

open MeasureTheory ProbabilityTheory BanditAlgorithm in
theorem DF742747B_pot_meas {k : ℕ} {S : Type*} [MeasurableSpace S] (P : Kernel S S)
    [IsMarkovKernel P] {r : S → ℝ} (hr : Measurable r)
    (hrb : WeberGittins.Suboptimality.RewardsNonnegBounded r)
    {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hγ : Measurable (gittinsIndex P r β)) (m : ℕ) :
    Measurable (fun h : MarkovBanditHistory k S m ↦ currentGittinsRetirementPotential P r β h) := by
  unfold currentGittinsRetirementPotential
  exact Finset.measurable_sum _ fun i _ ↦ DF742747B_T_meas P hr hrb hβ0 hβ1 hγ m i

open MeasureTheory ProbabilityTheory BanditAlgorithm in
theorem DF742747B_pot_bound {k : ℕ} {S : Type*} [MeasurableSpace S] (P : Kernel S S)
    [IsMarkovKernel P] {r : S → ℝ} (hr : Measurable r) (hr0 : ∀ y, 0 ≤ r y) {C : ℝ}
    (hC : ∀ y, r y ≤ C) {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (m : ℕ)
    (h : MarkovBanditHistory k S m) :
    |currentGittinsRetirementPotential P r β h| ≤ k * ((|C| + |C|) / (1 - β)) := by
  unfold currentGittinsRetirementPotential
  exact DF742747B_sum_bound _ (fun i ↦ DF742747B_T_bound P hr hr0 hC hβ0 hβ1 m h i) Finset.univ

open MeasureTheory ProbabilityTheory BanditAlgorithm in
theorem DF742747B_L_meas {k : ℕ} {S : Type*} [MeasurableSpace S] (P : Kernel S S)
    [IsMarkovKernel P] {r : S → ℝ} (hr : Measurable r)
    (hrb : WeberGittins.Suboptimality.RewardsNonnegBounded r)
    {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hγ : Measurable (gittinsIndex P r β)) (n : ℕ) :
    Measurable (fun q : MarkovBanditHistory k S n × Fin k ↦
      ∑ i ∈ Finset.univ.erase q.2, gittinsRetirementValue P r β
        (currentHistoryPrevailingCharge (gittinsIndex P r β) n q.1 i) (q.1.2 i)) := by
  refine measurable_from_prod_countable_left fun j ↦ ?_
  exact (Finset.measurable_sum (Finset.univ.erase j) fun i _ ↦
    DF742747B_T_meas P hr hrb hβ0 hβ1 hγ n i :)

open MeasureTheory ProbabilityTheory BanditAlgorithm in
/-- Integral against the step measure as an iterated integral. -/
theorem DF742747B_nu_iter {k n : ℕ} {S : Type*} [MeasurableSpace S] (P : Kernel S S)
    [IsMarkovKernel P] (π : MarkovBanditPolicy k S) (μ : Measure (MarkovBanditHistory k S n))
    [IsFiniteMeasure μ] (H : MarkovBanditHistory k S n × (Fin k × S) → ℝ) (hH : Measurable H)
    (b : ℝ) (hb : ∀ p, |H p| ≤ b) :
    ∫ p, H p ∂(μ ⊗ₘ markovBanditStepKernel P π n) =
      ∫ h, ∫ a, ∫ y, H (h, (a, y)) ∂P (h.2 a) ∂π.select n h ∂μ := by
  rw [Measure.integral_compProd (p2mbf_int_of_bound _ H hH b hb)]
  refine integral_congr_ae (Filter.Eventually.of_forall fun h ↦ ?_)
  dsimp only
  have hG : Measurable (fun z : Fin k × S ↦ H (h, z)) := hH.comp measurable_prodMk_left
  have hint : Integrable (fun z : Fin k × S ↦ H (h, z)) (markovBanditStepKernel P π n h) :=
    p2mbf_int_of_bound _ _ hG b (fun z ↦ hb (h, z))
  rw [markovBanditStepKernel] at hint ⊢
  rw [ProbabilityTheory.integral_compProd hint]
  simp only [Kernel.comap_apply]

open MeasureTheory ProbabilityTheory in
theorem DF742747B_int_fst {α γ : Type*} [MeasurableSpace α] [MeasurableSpace γ] (μ : Measure α)
    [IsFiniteMeasure μ] (κ : Kernel α γ) [IsMarkovKernel κ] (g : α → ℝ) (hg : Measurable g)
    (b : ℝ) (hb : ∀ x, |g x| ≤ b) : ∫ p, g p.1 ∂(μ ⊗ₘ κ) = ∫ x, g x ∂μ := by
  rw [Measure.integral_compProd (p2mbf_int_of_bound _ (fun p : α × γ ↦ g p.1)
    (hg.comp measurable_fst) b (fun p ↦ hb p.1))]
  simp only [integral_const, probReal_univ, one_smul]

open MeasureTheory ProbabilityTheory BanditAlgorithm in
/-- Generic zero-integral combination on the step measure. -/
theorem DF742747B_gen_zero {k n : ℕ} {S : Type*} [MeasurableSpace S] (P : Kernel S S)
    [IsMarkovKernel P] (π : MarkovBanditPolicy k S) (μ : Measure (MarkovBanditHistory k S n))
    [IsFiniteMeasure μ] (β : ℝ) (F1 F2 F3 F4 F5 : MarkovBanditHistory k S n × (Fin k × S) → ℝ)
    (m1 : Measurable F1) (m2 : Measurable F2) (m3 : Measurable F3) (m4 : Measurable F4)
    (m5 : Measurable F5) (b1 b2 b3 b4 b5 : ℝ) (hb1 : ∀ p, |F1 p| ≤ b1) (hb2 : ∀ p, |F2 p| ≤ b2)
    (hb3 : ∀ p, |F3 p| ≤ b3) (hb4 : ∀ p, |F4 p| ≤ b4) (hb5 : ∀ p, |F5 p| ≤ b5)
    (hin : ∀ h a, ∫ y, (β * F1 (h, (a, y)) + (F2 (h, (a, y)) + (1 - β) * F3 (h, (a, y)) -
      F4 (h, (a, y)) - F5 (h, (a, y)))) ∂P (h.2 a) = 0) :
    β * ∫ p, F1 p ∂(μ ⊗ₘ markovBanditStepKernel P π n) +
      (∫ p, F2 p ∂(μ ⊗ₘ markovBanditStepKernel P π n) +
        (1 - β) * ∫ p, F3 p ∂(μ ⊗ₘ markovBanditStepKernel P π n) -
        ∫ p, F4 p ∂(μ ⊗ₘ markovBanditStepKernel P π n) -
        ∫ p, F5 p ∂(μ ⊗ₘ markovBanditStepKernel P π n)) = 0 := by
  have i1 := p2mbf_int_of_bound (μ ⊗ₘ markovBanditStepKernel P π n) F1 m1 b1 hb1
  have i2 := p2mbf_int_of_bound (μ ⊗ₘ markovBanditStepKernel P π n) F2 m2 b2 hb2
  have i3 := p2mbf_int_of_bound (μ ⊗ₘ markovBanditStepKernel P π n) F3 m3 b3 hb3
  have i4 := p2mbf_int_of_bound (μ ⊗ₘ markovBanditStepKernel P π n) F4 m4 b4 hb4
  have i5 := p2mbf_int_of_bound (μ ⊗ₘ markovBanditStepKernel P π n) F5 m5 b5 hb5
  have j23 : Integrable (fun p ↦ F2 p + (1 - β) * F3 p) (μ ⊗ₘ markovBanditStepKernel P π n) :=
    i2.add (i3.const_mul _)
  have j234 : Integrable (fun p ↦ F2 p + (1 - β) * F3 p - F4 p)
      (μ ⊗ₘ markovBanditStepKernel P π n) := j23.sub i4
  have j2345 : Integrable (fun p ↦ F2 p + (1 - β) * F3 p - F4 p - F5 p)
      (μ ⊗ₘ markovBanditStepKernel P π n) := j234.sub i5
  have hDm : Measurable (fun p ↦ β * F1 p + (F2 p + (1 - β) * F3 p - F4 p - F5 p)) :=
    (measurable_const.mul m1).add (((m2.add (measurable_const.mul m3)).sub m4).sub m5)
  have hDb : ∀ p, |β * F1 p + (F2 p + (1 - β) * F3 p - F4 p - F5 p)| ≤
      |β| * b1 + b2 + |1 - β| * b3 + b4 + b5 :=
    fun p ↦ DF742747B_comb_bound _ _ _ _ _ _ _ _ _ _ _ (hb1 p) (hb2 p) (hb3 p) (hb4 p) (hb5 p)
  have hD := DF742747B_nu_iter P π μ _ hDm _ hDb
  rw [integral_add (i1.const_mul β) j2345, integral_sub j234 i5, integral_sub j23 i4,
    integral_add i2 (i3.const_mul _), integral_const_mul, integral_const_mul] at hD
  rw [hD]
  simp only [hin, integral_zero]

open MeasureTheory ProbabilityTheory BanditAlgorithm in
/-- Inner per-(history, arm) fair-game identity. -/
theorem DF742747B_inner {k n : ℕ} {S : Type*} [MeasurableSpace S] (P : Kernel S S)
    [IsMarkovKernel P] {r : S → ℝ} (hr : Measurable r)
    (hrb : WeberGittins.Suboptimality.RewardsNonnegBounded r)
    {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hγ : Measurable (gittinsIndex P r β))
    (h : MarkovBanditHistory k S n) (a : Fin k) :
    β * ∫ y, currentGittinsRetirementPotential P r β
        ((Fin.snoc (α := fun _ ↦ (Fin k → S) × Fin k) h.1 (h.2, a),
          Function.update h.2 a y) : MarkovBanditHistory k S (n + 1)) ∂P (h.2 a) =
      currentGittinsRetirementPotential P r β h - r (h.2 a) +
        currentHistoryPrevailingCharge (gittinsIndex P r β) n h a -
        (1 - β) * ∑ i ∈ Finset.univ.erase a, gittinsRetirementValue P r β
          (currentHistoryPrevailingCharge (gittinsIndex P r β) n h i) (h.2 i) := by
  obtain ⟨hr0, C, hC⟩ := id hrb
  have h1a : 0 < 1 - β := by linarith
  have hgi := DF742747B_gi_bounds P hr hr0 hC hβ0 hβ1
  have hcb := DF742747B_chpc_bounds (k := k) (gittinsIndex P r β) hgi
  have hpt : ∀ y : S, currentGittinsRetirementPotential P r β
        ((Fin.snoc (α := fun _ ↦ (Fin k → S) × Fin k) h.1 (h.2, a),
          Function.update h.2 a y) : MarkovBanditHistory k S (n + 1)) =
        gittinsRetirementValue P r β
          (min (currentHistoryPrevailingCharge (gittinsIndex P r β) n h a)
            (gittinsIndex P r β y)) y + ∑ i ∈ Finset.univ.erase a, gittinsRetirementValue P r β
          (currentHistoryPrevailingCharge (gittinsIndex P r β) n h i) (h.2 i) := by
    intro y
    unfold currentGittinsRetirementPotential
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ a)]
    congr 1
    · rw [DF742747B_chpc_snoc, if_pos rfl]
      simp only [Function.update_self]
    · refine Finset.sum_congr rfl fun i hi ↦ ?_
      have hne := Finset.ne_of_mem_erase hi
      rw [DF742747B_chpc_snoc, if_neg hne]
      simp only [Function.update_of_ne hne]
  have hmp : Measurable (fun y : S ↦
      (min (currentHistoryPrevailingCharge (gittinsIndex P r β) n h a) (gittinsIndex P r β y), y)) :=
    (measurable_const.min hγ).prodMk measurable_id
  have hmm := (DF742747B_ret_meas2 P hr hrb hβ0 hβ1).comp hmp
  have hmin_int : Integrable (fun y ↦ gittinsRetirementValue P r β
      (min (currentHistoryPrevailingCharge (gittinsIndex P r β) n h a)
        (gittinsIndex P r β y)) y) (P (h.2 a)) :=
    p2mbf_int_of_bound _ _ hmm ((|C| + |C|) / (1 - β))
      (fun y ↦ by
        have hq := le_min (hcb n h a).1 (hgi y).1
        obtain ⟨h0, h1⟩ := DF742747B_ret_bounds P hr0 hC hβ0 hβ1
          (min (currentHistoryPrevailingCharge (gittinsIndex P r β) n h a)
            (gittinsIndex P r β y)) y
        rw [abs_of_nonneg h0]
        refine h1.trans (div_le_div_of_nonneg_right ?_ h1a.le)
        rw [abs_of_nonneg hq]
        linarith [le_abs_self C, (min_le_right (currentHistoryPrevailingCharge
          (gittinsIndex P r β) n h a) (gittinsIndex P r β y)).trans (hgi y).2])
  have hstep := DF742747B_step P hr hrb hβ0 hβ1
    (currentHistoryPrevailingCharge (gittinsIndex P r β) n h a) (h.2 a)
    (DF742747B_chpc_le _ n h a)
  simp_rw [hpt]
  rw [integral_add hmin_int (integrable_const _)]
  simp only [integral_const, probReal_univ, one_smul]
  have hsplit : currentGittinsRetirementPotential P r β h = gittinsRetirementValue P r β
        (currentHistoryPrevailingCharge (gittinsIndex P r β) n h a) (h.2 a) +
      ∑ i ∈ Finset.univ.erase a, gittinsRetirementValue P r β
        (currentHistoryPrevailingCharge (gittinsIndex P r β) n h i) (h.2 i) := by
    unfold currentGittinsRetirementPotential
    exact (Finset.add_sum_erase _ _ (Finset.mem_univ a)).symm
  rw [hsplit]
  linear_combination -hstep

open MeasureTheory ProbabilityTheory BanditAlgorithm in
/-- Next-round integral as an integral on the step measure. -/
theorem DF742747B_next_int {k : ℕ} {S : Type*} [MeasurableSpace S] (P : Kernel S S)
    [IsMarkovKernel P] (π : MarkovBanditPolicy k S) (x : Fin k → S) (n : ℕ)
    (G : MarkovBanditHistory k S (n + 1) → ℝ) (hG : Measurable G) :
    ∫ h, G h ∂markovBanditMeasure P π x (n + 1) =
      ∫ p, G ((Fin.snoc (α := fun _ ↦ (Fin k → S) × Fin k) p.1.1 (p.1.2, p.2.1),
        Function.update p.1.2 p.2.1 p.2.2) : MarkovBanditHistory k S (n + 1))
        ∂(markovBanditMeasure P π x n ⊗ₘ markovBanditStepKernel P π n) := by
  rw [markovBanditMeasure, integral_map measurable_markovBanditSnoc.aemeasurable
    hG.aestronglyMeasurable]

open MeasureTheory ProbabilityTheory BanditAlgorithm in
/-- One-step identity for a general prior law of the history. -/
theorem DF742747B_onestep_gen {k n : ℕ} {S : Type*} [MeasurableSpace S] (P : Kernel S S)
    [IsMarkovKernel P] {r : S → ℝ} (hr : Measurable r)
    (hrb : WeberGittins.Suboptimality.RewardsNonnegBounded r)
    {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hγ : Measurable (gittinsIndex P r β))
    (π : MarkovBanditPolicy k S) (μ : Measure (MarkovBanditHistory k S n)) [IsFiniteMeasure μ] :
    ∫ p, r (p.1.2 p.2.1) ∂(μ ⊗ₘ markovBanditStepKernel P π n) +
        β * ∫ p, currentGittinsRetirementPotential P r β
          ((Fin.snoc (α := fun _ ↦ (Fin k → S) × Fin k) p.1.1 (p.1.2, p.2.1),
            Function.update p.1.2 p.2.1 p.2.2) : MarkovBanditHistory k S (n + 1))
          ∂(μ ⊗ₘ markovBanditStepKernel P π n) +
        (1 - β) * ∫ p, ∑ i ∈ Finset.univ.erase p.2.1, gittinsRetirementValue P r β
            (currentHistoryPrevailingCharge (gittinsIndex P r β) n p.1 i) (p.1.2 i)
          ∂(μ ⊗ₘ markovBanditStepKernel P π n) =
      ∫ p, currentHistoryPrevailingCharge (gittinsIndex P r β) n p.1 p.2.1
          ∂(μ ⊗ₘ markovBanditStepKernel P π n) +
        ∫ h, currentGittinsRetirementPotential P r β h ∂μ := by
  obtain ⟨hr0, C, hC⟩ := id hrb
  have hgi := DF742747B_gi_bounds P hr hr0 hC hβ0 hβ1
  have hcb := DF742747B_chpc_bounds (k := k) (gittinsIndex P r β) hgi
  have hcm := DF742747B_chpc_meas (k := k) hγ
  have hPm := DF742747B_pot_meas (k := k) P hr hrb hβ0 hβ1 hγ
  have hPb := DF742747B_pot_bound (k := k) P hr hr0 hC hβ0 hβ1
  have hTb := DF742747B_T_bound (k := k) P hr hr0 hC hβ0 hβ1
  have hLm := DF742747B_L_meas (k := k) P hr hrb hβ0 hβ1 hγ n
  have hsn := measurable_markovBanditSnoc (k := k) (n := n) (S := S)
  have hπ1 : Measurable (fun p : MarkovBanditHistory k S n × (Fin k × S) ↦ (p.1, p.2.1)) :=
    measurable_fst.prodMk (measurable_fst.comp measurable_snd)
  have hCm : Measurable (fun q : MarkovBanditHistory k S n × Fin k ↦
      currentHistoryPrevailingCharge (gittinsIndex P r β) n q.1 q.2) :=
    measurable_from_prod_countable_left fun j ↦ hcm n j
  have m1 := (hPm (n + 1)).comp hsn
  have m2a := measurable_currentArmState.comp hπ1
  have m2 := hr.comp m2a
  have m3 := hLm.comp hπ1
  have m4 := hCm.comp hπ1
  have hfst : Measurable (Prod.fst : MarkovBanditHistory k S n × (Fin k × S) →
      MarkovBanditHistory k S n) := measurable_fst
  have m5 := (hPm n).comp hfst
  have hz := DF742747B_gen_zero P π μ β
    (fun p ↦ currentGittinsRetirementPotential P r β
      ((Fin.snoc (α := fun _ ↦ (Fin k → S) × Fin k) p.1.1 (p.1.2, p.2.1),
        Function.update p.1.2 p.2.1 p.2.2) : MarkovBanditHistory k S (n + 1)))
    (fun p ↦ r (p.1.2 p.2.1))
    (fun p ↦ ∑ i ∈ Finset.univ.erase p.2.1, gittinsRetirementValue P r β
      (currentHistoryPrevailingCharge (gittinsIndex P r β) n p.1 i) (p.1.2 i))
    (fun p ↦ currentHistoryPrevailingCharge (gittinsIndex P r β) n p.1 p.2.1)
    (fun p ↦ currentGittinsRetirementPotential P r β p.1)
    m1 m2 m3 m4 m5
    _ |C| _ |C| _ (fun p ↦ hPb (n + 1) _)
    (fun p ↦ abs_le.2 ⟨by linarith [hr0 (p.1.2 p.2.1), abs_nonneg C],
      (hC _).trans (le_abs_self C)⟩)
    (fun p ↦ DF742747B_sum_bound _ (fun i ↦ hTb n p.1 i) _)
    (fun p ↦ abs_le.2 ⟨by linarith [(hcb n p.1 p.2.1).1, abs_nonneg C],
      (hcb n p.1 p.2.1).2.trans (le_abs_self C)⟩)
    (fun p ↦ hPb n p.1)
    (fun h a ↦ by
      dsimp only
      have hint : Integrable (fun y ↦ currentGittinsRetirementPotential P r β
          ((Fin.snoc (α := fun _ ↦ (Fin k → S) × Fin k) h.1 (h.2, a),
            Function.update h.2 a y) : MarkovBanditHistory k S (n + 1))) (P (h.2 a)) :=
        have hy : Measurable (fun y : S ↦ (h, (a, y))) := by fun_prop
        have mY := (hPm (n + 1)).comp (hsn.comp hy)
        p2mbf_int_of_bound _ _ mY _ (fun y ↦ hPb (n + 1) _)
      rw [integral_add (hint.const_mul β) (integrable_const _), integral_const_mul]
      simp only [integral_const, probReal_univ, one_smul]
      rw [DF742747B_inner P hr hrb hβ0 hβ1 hγ h a]
      ring)
  have hf := DF742747B_int_fst μ (markovBanditStepKernel P π n)
    (fun h ↦ currentGittinsRetirementPotential P r β h) (hPm n) _ (hPb n)
  linear_combination hz + hf

open MeasureTheory ProbabilityTheory BanditAlgorithm in
/-- Per-round fair-game identity (K1 step). -/
theorem DF742747B_onestep {k : ℕ} {S : Type*} [MeasurableSpace S] (P : Kernel S S)
    [IsMarkovKernel P] {r : S → ℝ} (hr : Measurable r)
    (hrb : WeberGittins.Suboptimality.RewardsNonnegBounded r)
    {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hγ : Measurable (gittinsIndex P r β))
    (π : MarkovBanditPolicy k S) (x : Fin k → S) (n : ℕ) :
    markovBanditRoundReward P r π x n +
        β * markovBanditExpectedRetirementPotential P r β π x (n + 1) +
        (1 - β) * WeberGittins.Suboptimality.roundExpectation P π x n (fun h j ↦
          ∑ i ∈ Finset.univ.erase j, gittinsRetirementValue P r β
            (currentHistoryPrevailingCharge (gittinsIndex P r β) n h i) (h.2 i)) =
      markovBanditRoundPrevailingCharge P r β π x n +
        markovBanditExpectedRetirementPotential P r β π x n := by
  have hPm := DF742747B_pot_meas (k := k) P hr hrb hβ0 hβ1 hγ
  have hLm := DF742747B_L_meas (k := k) P hr hrb hβ0 hβ1 hγ n
  have e1 : markovBanditRoundReward P r π x n = ∫ p, r (p.1.2 p.2.1)
      ∂(markovBanditMeasure P π x n ⊗ₘ markovBanditStepKernel P π n) := by
    unfold markovBanditRoundReward
    have hq : Measurable (fun q : (Fin k → S) × Fin k ↦ r (q.1 q.2)) :=
      measurable_from_prod_countable_left fun j ↦ hr.comp (measurable_pi_apply j)
    have hl : Measurable (fun h : MarkovBanditHistory k S (n + 1) ↦ h.1 (Fin.last n)) :=
      (measurable_pi_apply (Fin.last n)).comp measurable_fst
    have hG := hq.comp hl
    rw [DF742747B_next_int P π x n (fun h ↦ r ((h.1 (Fin.last n)).1 ((h.1 (Fin.last n)).2))) hG]
    refine integral_congr_ae (Filter.Eventually.of_forall fun p ↦ ?_)
    simp only [Fin.snoc_last]
  have e2 : WeberGittins.Suboptimality.roundExpectation P π x n (fun h j ↦
          ∑ i ∈ Finset.univ.erase j, gittinsRetirementValue P r β
            (currentHistoryPrevailingCharge (gittinsIndex P r β) n h i) (h.2 i)) =
      ∫ p, ∑ i ∈ Finset.univ.erase p.2.1, gittinsRetirementValue P r β
            (currentHistoryPrevailingCharge (gittinsIndex P r β) n p.1 i) (p.1.2 i)
        ∂(markovBanditMeasure P π x n ⊗ₘ markovBanditStepKernel P π n) := by
    unfold WeberGittins.Suboptimality.roundExpectation
    have hl : Measurable (fun h : MarkovBanditHistory k S (n + 1) ↦
        (truncateMarkovBanditHistory h, (h.1 (Fin.last n)).2)) :=
      DF742747B_trunc_meas.prodMk (measurable_snd.comp
        ((measurable_pi_apply (Fin.last n)).comp measurable_fst))
    have hG := hLm.comp hl
    rw [DF742747B_next_int P π x n (fun h ↦ ∑ i ∈ Finset.univ.erase (h.1 (Fin.last n)).2,
        gittinsRetirementValue P r β (currentHistoryPrevailingCharge (gittinsIndex P r β) n
          (truncateMarkovBanditHistory h) i) ((truncateMarkovBanditHistory h).2 i))
      hG]
    refine integral_congr_ae (Filter.Eventually.of_forall fun p ↦ ?_)
    simp only [DF742747B_trunc_snoc, Fin.snoc_last]
  have e5 : markovBanditExpectedRetirementPotential P r β π x (n + 1) =
      ∫ p, currentGittinsRetirementPotential P r β
          ((Fin.snoc (α := fun _ ↦ (Fin k → S) × Fin k) p.1.1 (p.1.2, p.2.1),
            Function.update p.1.2 p.2.1 p.2.2) : MarkovBanditHistory k S (n + 1))
        ∂(markovBanditMeasure P π x n ⊗ₘ markovBanditStepKernel P π n) :=
    DF742747B_next_int P π x n (fun h ↦ currentGittinsRetirementPotential P r β h) (hPm (n + 1))
  rw [e1, e2, e5]
  exact DF742747B_onestep_gen P hr hrb hβ0 hβ1 hγ π (markovBanditMeasure P π x n)

open MeasureTheory ProbabilityTheory BanditAlgorithm in
/-- The initial retirement potential vanishes (charges start at the index). -/
theorem DF742747B_pot_zero {k : ℕ} {S : Type*} [MeasurableSpace S] (P : Kernel S S)
    [IsMarkovKernel P] {r : S → ℝ} (hr : Measurable r)
    (hrb : WeberGittins.Suboptimality.RewardsNonnegBounded r)
    {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (π : MarkovBanditPolicy k S) (x : Fin k → S) :
    markovBanditExpectedRetirementPotential P r β π x 0 = 0 := by
  unfold markovBanditExpectedRetirementPotential currentGittinsRetirementPotential
  have hz : ∀ h : MarkovBanditHistory k S 0, ∑ i, gittinsRetirementValue P r β
      (currentHistoryPrevailingCharge (gittinsIndex P r β) 0 h i) (h.2 i) = 0 := fun h ↦
    Finset.sum_eq_zero fun i _ ↦ DF742747B_ret_zero P hr hrb hβ0 hβ1 _ _ le_rfl
  simp only [hz, integral_zero]

open MeasureTheory ProbabilityTheory BanditAlgorithm in
/-- K1: prevailing-charge accounting with the abandonment loss, for every policy. -/
theorem DF742747B_K1 {k : ℕ} {S : Type*} [MeasurableSpace S] (P : Kernel S S)
    [IsMarkovKernel P] {r : S → ℝ} (hr : Measurable r)
    (hrb : WeberGittins.Suboptimality.RewardsNonnegBounded r)
    {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hγ : Measurable (gittinsIndex P r β))
    (π : MarkovBanditPolicy k S) (x : Fin k → S) (N : ℕ) :
    (∑ n ∈ Finset.range N, β ^ n * markovBanditRoundReward P r π x n) +
        β ^ N * markovBanditExpectedRetirementPotential P r β π x N +
        (1 - β) * ∑ n ∈ Finset.range N, β ^ n *
          WeberGittins.Suboptimality.roundExpectation P π x n (fun h j =>
            ∑ i ∈ Finset.univ.erase j, gittinsRetirementValue P r β
              (currentHistoryPrevailingCharge (gittinsIndex P r β) n h i) (h.2 i)) =
      markovBanditFinitePrevailingChargeValue P r β π x N := by
  induction N with
  | zero =>
    simp only [Finset.sum_range_zero, pow_zero, one_mul, mul_zero, add_zero,
      DF742747B_pot_zero P hr hrb hβ0 hβ1 π x, markovBanditFinitePrevailingChargeValue]
  | succ N ih =>
    have hs := DF742747B_onestep P hr hrb hβ0 hβ1 hγ π x N
    unfold markovBanditFinitePrevailingChargeValue at ih ⊢
    simp only [Finset.sum_range_succ]
    linear_combination ih + β ^ N * hs

/-! INV for df742747: path invariant of a run-then-Gittins policy started at round 0. -/

open MeasureTheory ProbabilityTheory BanditAlgorithm

/-- Pure Gittins-phase invariant step: at most one arm `b` has a prevailing charge below its
index, and then that charge dominates every other index. -/
def DFI_G {k : ℕ} (G C : Fin k → ℝ) : Prop :=
  ∃ b, (∀ i, i ≠ b → G i ≤ C i) ∧ (C b < G b → ∀ i, i ≠ b → G i ≤ C b)

theorem DFI_G_key {k : ℕ} {G C : Fin k → ℝ} (hG : DFI_G G C) {a : Fin k}
    (ha : ∀ i, G i ≤ G a) :
    (∀ i, i ≠ a → G i ≤ C i) ∧ (∀ i, i ≠ a → G i ≤ C a) := by
  obtain ⟨b, hb1, hb2⟩ := hG
  have K : ∀ i, i ≠ a → G i ≤ C i := by
    intro i hia
    by_cases hib : i = b
    · subst hib
      by_contra hlt
      have := hb2 (lt_of_not_ge hlt) a (Ne.symm hia)
      exact hlt ((ha i).trans this)
    · exact hb1 i hib
  refine ⟨K, fun i hia => ?_⟩
  by_cases hlt : C a < G a
  · by_cases hab : a = b
    · subst hab; exact hb2 hlt i hia
    · exact absurd (hb1 a hab) (not_le.2 hlt)
  · exact (ha i).trans (le_of_not_gt hlt)

theorem DFI_G_step {k : ℕ} {G C : Fin k → ℝ} (hG : DFI_G G C) {a : Fin k}
    (ha : ∀ i, G i ≤ G a) (z : ℝ) :
    DFI_G (fun i => if i = a then z else G i)
      (fun i => if i = a then min (C a) z else C i) := by
  obtain ⟨K1, K2⟩ := DFI_G_key hG ha
  refine ⟨a, fun i hia => ?_, fun hlt i hia => ?_⟩
  · simp only [if_neg hia]; exact K1 i hia
  · simp only [if_neg hia, if_pos rfl] at hlt ⊢
    have hm : min (C a) z = C a := by
      rcases le_total (C a) z with h | h
      · exact min_eq_left h
      · rw [min_eq_right h] at hlt; exact absurd hlt (lt_irrefl _)
    rw [hm]; exact K2 i hia

/-- Run continuation from round 0 for a history of `n + 1` rounds. -/
def DFI_RC {k : ℕ} {S : Type*} [MeasurableSpace S] (P : Kernel S S) [IsMarkovKernel P]
    (r : S → ℝ) (β : ℝ) {n : ℕ} (h : MarkovBanditHistory k S (n + 1)) : Prop :=
  WeberGittins.IndexGap.RunContinues P r β 0 (n + 1) (Nat.succ_pos n) h

theorem DFI_RC_snoc {k : ℕ} {S : Type*} [MeasurableSpace S] (P : Kernel S S) [IsMarkovKernel P]
    (r : S → ℝ) (β : ℝ) {n : ℕ} (h : MarkovBanditHistory k S (n + 1)) (a : Fin k) (y : S) :
    DFI_RC P r β ((Fin.snoc (α := fun _ ↦ (Fin k → S) × Fin k) h.1 (h.2, a),
        Function.update h.2 a y) : MarkovBanditHistory k S (n + 2)) ↔
      DFI_RC P r β h ∧ a = (h.1 ⟨0, Nat.succ_pos n⟩).2 ∧
        gittinsIndex P r β ((h.1 ⟨0, Nat.succ_pos n⟩).1 (h.1 ⟨0, Nat.succ_pos n⟩).2) ≤
          gittinsIndex P r β y := by
  have hz : (Fin.snoc (α := fun _ ↦ (Fin k → S) × Fin k) h.1 (h.2, a)
      (⟨0, Nat.succ_pos (n + 1)⟩ : Fin (n + 2))) = h.1 ⟨0, Nat.succ_pos n⟩ :=
    Fin.snoc_castSucc (α := fun _ ↦ (Fin k → S) × Fin k) (x := (h.2, a)) (p := h.1)
      ⟨0, Nat.succ_pos n⟩
  have hc : ∀ m : Fin (n + 1), (Fin.snoc (α := fun _ ↦ (Fin k → S) × Fin k) h.1 (h.2, a)
      (Fin.castSucc m)) = h.1 m := fun m =>
    Fin.snoc_castSucc (α := fun _ ↦ (Fin k → S) × Fin k) (x := (h.2, a)) (p := h.1) m
  have hl : (Fin.snoc (α := fun _ ↦ (Fin k → S) × Fin k) h.1 (h.2, a) (Fin.last (n + 1))) =
      (h.2, a) := Fin.snoc_last (α := fun _ ↦ (Fin k → S) × Fin k) (x := (h.2, a)) (p := h.1)
  unfold DFI_RC WeberGittins.IndexGap.RunContinues
  simp only [hz]
  constructor
  · rintro ⟨h1, h2, h3⟩
    have ha : a = (h.1 ⟨0, Nat.succ_pos n⟩).2 := by
      have := h1 (Fin.last _) (Nat.zero_le _); rwa [hl] at this
    refine ⟨⟨fun m hm => ?_, fun m hm => ?_, ?_⟩, ha, ?_⟩
    · have := h1 (Fin.castSucc m) hm; rwa [hc] at this
    · have := h2 (Fin.castSucc m) hm; rwa [hc] at this
    · have := h2 (Fin.last _) (Nat.succ_pos n); rw [hl] at this; exact this
    · have e : Function.update h.2 a y (h.1 ⟨0, Nat.succ_pos n⟩).2 = y := by
        rw [← ha]; simp
      rw [e] at h3; exact h3
  · rintro ⟨⟨h1, h2, h3⟩, ha, hy⟩
    refine ⟨fun m hm => ?_, fun m hm => ?_, ?_⟩
    · induction m using Fin.lastCases with
      | last => rw [hl]; exact ha
      | cast m => rw [hc]; exact h1 m hm
    · induction m using Fin.lastCases with
      | last => rw [hl]; exact h3
      | cast m => rw [hc]; exact h2 m hm
    · have e : Function.update h.2 a y (h.1 ⟨0, Nat.succ_pos n⟩).2 = y := by
        rw [← ha]; simp
      rw [e]; exact hy

theorem DFI_RC_one {k : ℕ} {S : Type*} [MeasurableSpace S] (P : Kernel S S) [IsMarkovKernel P]
    (r : S → ℝ) (β : ℝ) (h : MarkovBanditHistory k S 0) (a : Fin k) (y : S) :
    DFI_RC P r β ((Fin.snoc (α := fun _ ↦ (Fin k → S) × Fin k) h.1 (h.2, a),
        Function.update h.2 a y) : MarkovBanditHistory k S 1) ↔
      gittinsIndex P r β (h.2 a) ≤ gittinsIndex P r β y := by
  have hl : (Fin.snoc (α := fun _ ↦ (Fin k → S) × Fin k) h.1 (h.2, a)
      (⟨0, Nat.succ_pos 0⟩ : Fin 1)) = (h.2, a) :=
    Fin.snoc_last (α := fun _ ↦ (Fin k → S) × Fin k) (x := (h.2, a)) (p := h.1)
  unfold DFI_RC WeberGittins.IndexGap.RunContinues
  simp only [hl]
  constructor
  · rintro ⟨-, -, h3⟩
    simpa using h3
  · intro hy
    refine ⟨fun m _ => ?_, fun m hm => ?_, by simpa using hy⟩
    · have : m = ⟨0, Nat.succ_pos 0⟩ := Fin.ext (by have := m.isLt; omega)
      subst this; rw [hl]
    · exact absurd hm (by have := m.isLt; omega)

/-- The invariant at a history of `n + 1` rounds. -/
def DFI_Inv {k : ℕ} {S : Type*} [MeasurableSpace S] (P : Kernel S S) [IsMarkovKernel P]
    (r : S → ℝ) (β : ℝ) {n : ℕ} (h : MarkovBanditHistory k S (n + 1)) : Prop :=
  (DFI_RC P r β h →
    currentHistoryPrevailingCharge (gittinsIndex P r β) (n + 1) h (h.1 ⟨0, Nat.succ_pos n⟩).2 =
        gittinsIndex P r β ((h.1 ⟨0, Nat.succ_pos n⟩).1 (h.1 ⟨0, Nat.succ_pos n⟩).2) ∧
      ∀ i, i ≠ (h.1 ⟨0, Nat.succ_pos n⟩).2 →
        gittinsIndex P r β (h.2 i) ≤
            currentHistoryPrevailingCharge (gittinsIndex P r β) (n + 1) h i ∧
          gittinsIndex P r β (h.2 i) ≤
            ⨆ l, gittinsIndex P r β ((h.1 ⟨0, Nat.succ_pos n⟩).1 l)) ∧
  (¬ DFI_RC P r β h →
    DFI_G (fun i => gittinsIndex P r β (h.2 i))
      (fun i => currentHistoryPrevailingCharge (gittinsIndex P r β) (n + 1) h i))

/-- The arms the policy may select after a history of `n + 1` rounds. -/
def DFI_Allowed {k : ℕ} {S : Type*} [MeasurableSpace S] (P : Kernel S S) [IsMarkovKernel P]
    (r : S → ℝ) (β : ℝ) {n : ℕ} (h : MarkovBanditHistory k S (n + 1)) (a : Fin k) : Prop :=
  (DFI_RC P r β h → a = (h.1 ⟨0, Nat.succ_pos n⟩).2) ∧
  (¬ DFI_RC P r β h → ∀ i, gittinsIndex P r β (h.2 i) ≤ gittinsIndex P r β (h.2 a))

theorem DFI_le_sup {k : ℕ} (f : Fin k → ℝ) (i : Fin k) : f i ≤ ⨆ l, f l :=
  le_ciSup (Set.finite_range f).bddAbove i

theorem DFI_inv_base {k : ℕ} {S : Type*} [MeasurableSpace S] (P : Kernel S S) [IsMarkovKernel P]
    (r : S → ℝ) (β : ℝ) (h : MarkovBanditHistory k S 0) (a : Fin k) (y : S) :
    DFI_Inv P r β ((Fin.snoc (α := fun _ ↦ (Fin k → S) × Fin k) h.1 (h.2, a),
        Function.update h.2 a y) : MarkovBanditHistory k S 1) := by
  have hl : (Fin.snoc (α := fun _ ↦ (Fin k → S) × Fin k) h.1 (h.2, a)
      (⟨0, Nat.succ_pos 0⟩ : Fin 1)) = (h.2, a) :=
    Fin.snoc_last (α := fun _ ↦ (Fin k → S) × Fin k) (x := (h.2, a)) (p := h.1)
  have hch := DF742747B_chpc_snoc (gittinsIndex P r β) h a y
  have h0 : ∀ i, currentHistoryPrevailingCharge (gittinsIndex P r β) 0 h i =
      gittinsIndex P r β (h.2 i) := fun i => rfl
  unfold DFI_Inv
  rw [DFI_RC_one]
  simp only [hl, hch, h0]
  refine ⟨fun hy => ⟨?_, fun i hi => ?_⟩, fun hy => ⟨a, fun i hi => ?_, fun hlt => ?_⟩⟩
  · (try simp only [if_pos rfl]); exact min_eq_left hy
  · simp only [if_neg hi, Function.update_apply]
    exact ⟨le_rfl, DFI_le_sup (fun l => gittinsIndex P r β (h.2 l)) i⟩
  · simp only [if_neg hi, Function.update_apply]; exact le_rfl
  · exfalso
    simp only [if_pos rfl, Function.update_apply] at hlt
    rw [min_eq_right (le_of_lt (lt_of_not_ge hy))] at hlt
    exact lt_irrefl _ hlt

theorem DFI_inv_step {k : ℕ} {S : Type*} [MeasurableSpace S] (P : Kernel S S) [IsMarkovKernel P]
    (r : S → ℝ) (β : ℝ) {n : ℕ} (h : MarkovBanditHistory k S (n + 1)) (a : Fin k) (y : S)
    (hI : DFI_Inv P r β h) (hA : DFI_Allowed P r β h a) :
    DFI_Inv P r β ((Fin.snoc (α := fun _ ↦ (Fin k → S) × Fin k) h.1 (h.2, a),
        Function.update h.2 a y) : MarkovBanditHistory k S (n + 2)) := by
  have hz : (Fin.snoc (α := fun _ ↦ (Fin k → S) × Fin k) h.1 (h.2, a)
      (⟨0, Nat.succ_pos (n + 1)⟩ : Fin (n + 2))) = h.1 ⟨0, Nat.succ_pos n⟩ :=
    Fin.snoc_castSucc (α := fun _ ↦ (Fin k → S) × Fin k) (x := (h.2, a)) (p := h.1)
      ⟨0, Nat.succ_pos n⟩
  have hch := DF742747B_chpc_snoc (gittinsIndex P r β) h a y
  have hu : ∀ i, Function.update h.2 a y i = if i = a then y else h.2 i := fun i => by
    rw [Function.update_apply]
  obtain ⟨hIr, hIg⟩ := hI
  obtain ⟨hAr, hAg⟩ := hA
  unfold DFI_Inv
  rw [DFI_RC_snoc]
  simp only [hz, hch, hu]
  by_cases hrc : DFI_RC P r β h
  · obtain ⟨hj, hoth⟩ := hIr hrc
    have ha := hAr hrc
    subst ha
    refine ⟨fun ⟨_, _, hy⟩ => ⟨?_, fun i hi => ?_⟩, fun hn => ⟨h.1 ⟨0, Nat.succ_pos n⟩ |>.2,
      fun i hi => ?_, fun hlt => ?_⟩⟩
    · (try simp only [if_pos rfl]); rw [hj]; exact min_eq_left hy
    · simp only [if_neg hi]; exact hoth i hi
    · simp only [if_neg hi]; exact (hoth i hi).1
    · exfalso
      have hy : gittinsIndex P r β y <
          gittinsIndex P r β ((h.1 ⟨0, Nat.succ_pos n⟩).1 (h.1 ⟨0, Nat.succ_pos n⟩).2) := by
        by_contra hc; exact hn ⟨hrc, rfl, le_of_not_gt hc⟩
      (try simp only [if_pos rfl] at hlt)
      rw [hj, min_eq_right hy.le] at hlt
      exact lt_irrefl _ hlt
  · have hGa := hAg hrc
    refine ⟨fun hh => absurd hh.1 hrc, fun _ => ?_⟩
    have e1 : (fun i => gittinsIndex P r β (if i = a then y else h.2 i)) =
        (fun i => if i = a then gittinsIndex P r β y else gittinsIndex P r β (h.2 i)) := by
      funext i; split_ifs <;> rfl
    rw [e1]; exact DFI_G_step (hIg hrc) hGa _

theorem DFI_eq_meas {k : ℕ} {α : Type*} [MeasurableSpace α] {f g : α → Fin k}
    (hf : Measurable f) (hg : Measurable g) : MeasurableSet {a | f a = g a} := by
  have e : {a | f a = g a} = ⋃ j, f ⁻¹' {j} ∩ g ⁻¹' {j} := by
    ext a
    simp only [Set.mem_setOf_eq, Set.mem_iUnion, Set.mem_inter_iff, Set.mem_preimage,
      Set.mem_singleton_iff]
    exact ⟨fun h => ⟨_, rfl, h.symm⟩, fun ⟨j, h1, h2⟩ => h1.trans h2.symm⟩
  rw [e]
  exact MeasurableSet.iUnion fun j =>
    (hf (measurableSet_singleton j)).inter (hg (measurableSet_singleton j))

theorem DFI_ev {k : ℕ} {B : Type*} [MeasurableSpace B] :
    Measurable (fun p : (Fin k → B) × Fin k => p.1 p.2) :=
  measurable_from_prod_countable_left fun a => measurable_pi_apply a

theorem DFI_meas_dep {k : ℕ} {α B : Type*} [MeasurableSpace α] [MeasurableSpace B]
    {f : α → Fin k → B} (hf : Measurable f) {g : α → Fin k} (hg : Measurable g) :
    Measurable (fun a => f a (g a)) := DFI_ev.comp (hf.prodMk hg)

theorem DFI_RC_meas {k : ℕ} {S : Type*} [MeasurableSpace S] (P : Kernel S S) [IsMarkovKernel P]
    (r : S → ℝ) (β : ℝ) (hγ : Measurable (gittinsIndex P r β)) (n : ℕ) :
    Measurable (fun h : MarkovBanditHistory k S (n + 1) => DFI_RC P r β h) := by
  have hE : ∀ m : Fin (n + 1), Measurable (fun h : MarkovBanditHistory k S (n + 1) => h.1 m) :=
    fun m => (measurable_pi_apply m).comp measurable_fst
  have hc := hγ.comp (DFI_meas_dep (hE ⟨0, Nat.succ_pos n⟩).fst (hE ⟨0, Nat.succ_pos n⟩).snd)
  unfold DFI_RC WeberGittins.IndexGap.RunContinues
  refine Measurable.and ?_ (Measurable.and ?_ ?_)
  · refine Measurable.forall fun m => Measurable.imp measurable_const ?_
    exact measurableSet_setOf.1
      (DFI_eq_meas (hE m).snd (hE ⟨0, Nat.succ_pos n⟩).snd)
  · refine Measurable.forall fun m => Measurable.imp measurable_const ?_
    exact measurableSet_setOf.1 (measurableSet_le hc
      (hγ.comp (DFI_meas_dep (hE m).fst (hE ⟨0, Nat.succ_pos n⟩).snd)))
  · exact measurableSet_setOf.1 (measurableSet_le hc
      (hγ.comp (DFI_meas_dep measurable_snd (hE ⟨0, Nat.succ_pos n⟩).snd)))

theorem DFI_inv_meas {k : ℕ} {S : Type*} [MeasurableSpace S] (P : Kernel S S) [IsMarkovKernel P]
    (r : S → ℝ) (β : ℝ) (hγ : Measurable (gittinsIndex P r β)) (n : ℕ) :
    MeasurableSet {h : MarkovBanditHistory k S (n + 1) | DFI_Inv P r β h} := by
  have hE : ∀ m : Fin (n + 1), Measurable (fun h : MarkovBanditHistory k S (n + 1) => h.1 m) :=
    fun m => (measurable_pi_apply m).comp measurable_fst
  have hC : ∀ i, Measurable (fun h : MarkovBanditHistory k S (n + 1) =>
      currentHistoryPrevailingCharge (gittinsIndex P r β) (n + 1) h i) :=
    fun i => DF742747B_chpc_meas hγ (n + 1) i
  have hG : ∀ i, Measurable (fun h : MarkovBanditHistory k S (n + 1) =>
      gittinsIndex P r β (h.2 i)) := fun i => hγ.comp ((measurable_pi_apply i).comp measurable_snd)
  have hG0 : ∀ i, Measurable (fun h : MarkovBanditHistory k S (n + 1) =>
      gittinsIndex P r β ((h.1 ⟨0, Nat.succ_pos n⟩).1 i)) :=
    fun i => hγ.comp ((measurable_pi_apply i).comp (hE _).fst)
  have hM : Measurable (fun h : MarkovBanditHistory k S (n + 1) =>
      ⨆ l, gittinsIndex P r β ((h.1 ⟨0, Nat.succ_pos n⟩).1 l)) := Measurable.iSup hG0
  have e : {h : MarkovBanditHistory k S (n + 1) | DFI_Inv P r β h} =
      {h | (DFI_RC P r β h → ∀ j, (h.1 ⟨0, Nat.succ_pos n⟩).2 = j →
          (currentHistoryPrevailingCharge (gittinsIndex P r β) (n + 1) h j =
              gittinsIndex P r β ((h.1 ⟨0, Nat.succ_pos n⟩).1 j) ∧
            ∀ i, i ≠ j → gittinsIndex P r β (h.2 i) ≤
                currentHistoryPrevailingCharge (gittinsIndex P r β) (n + 1) h i ∧
              gittinsIndex P r β (h.2 i) ≤
                ⨆ l, gittinsIndex P r β ((h.1 ⟨0, Nat.succ_pos n⟩).1 l))) ∧
        (¬ DFI_RC P r β h → ∃ b, (∀ i, i ≠ b → gittinsIndex P r β (h.2 i) ≤
            currentHistoryPrevailingCharge (gittinsIndex P r β) (n + 1) h i) ∧
          (currentHistoryPrevailingCharge (gittinsIndex P r β) (n + 1) h b <
              gittinsIndex P r β (h.2 b) → ∀ i, i ≠ b → gittinsIndex P r β (h.2 i) ≤
                currentHistoryPrevailingCharge (gittinsIndex P r β) (n + 1) h b))} := by
    ext h
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨fun hr j hj => by subst hj; exact h1 hr, h2⟩
    · rintro ⟨h1, h2⟩
      exact ⟨fun hr => h1 hr _ rfl, h2⟩
  rw [e]
  have hR := DFI_RC_meas (k := k) P r β hγ n
  refine measurableSet_setOf.2 (Measurable.and (Measurable.imp hR ?_) (Measurable.imp hR.not ?_))
  · refine Measurable.forall fun j => Measurable.imp
      (measurableSet_setOf.1 ((hE _).snd (measurableSet_singleton j))) (Measurable.and ?_ ?_)
    · exact measurableSet_setOf.1 (measurableSet_eq_fun (hC j) (hG0 j))
    · refine Measurable.forall fun i => Measurable.imp measurable_const (Measurable.and ?_ ?_)
      · exact measurableSet_setOf.1 (measurableSet_le (hG i) (hC i))
      · exact measurableSet_setOf.1 (measurableSet_le (hG i) hM)
  · refine Measurable.exists fun b => Measurable.and ?_ ?_
    · refine Measurable.forall fun i => Measurable.imp measurable_const ?_
      exact measurableSet_setOf.1 (measurableSet_le (hG i) (hC i))
    · refine Measurable.imp (measurableSet_setOf.1 (measurableSet_lt (hC b) (hG b))) ?_
      refine Measurable.forall fun i => Measurable.imp measurable_const ?_
      exact measurableSet_setOf.1 (measurableSet_le (hG i) (hC b))

theorem DFI_allowed_meas {k : ℕ} {S : Type*} [MeasurableSpace S] (P : Kernel S S)
    [IsMarkovKernel P] (r : S → ℝ) (β : ℝ) (hγ : Measurable (gittinsIndex P r β)) (n : ℕ) :
    MeasurableSet {p : MarkovBanditHistory k S (n + 1) × (Fin k × S) |
      DFI_Allowed P r β p.1 p.2.1} := by
  have hR := (DFI_RC_meas P r β hγ n).comp
    (measurable_fst : Measurable (fun p : MarkovBanditHistory k S (n + 1) × (Fin k × S) => p.1))
  have hj : Measurable (fun p : MarkovBanditHistory k S (n + 1) × (Fin k × S) =>
      (p.1.1 ⟨0, Nat.succ_pos n⟩).2) :=
    ((measurable_pi_apply _).comp (measurable_fst.comp measurable_fst)).snd
  have ha : Measurable (fun p : MarkovBanditHistory k S (n + 1) × (Fin k × S) => p.2.1) :=
    measurable_fst.comp measurable_snd
  have hs : Measurable (fun p : MarkovBanditHistory k S (n + 1) × (Fin k × S) => p.1.2) :=
    measurable_snd.comp measurable_fst
  unfold DFI_Allowed
  refine measurableSet_setOf.2 (Measurable.and (Measurable.imp hR ?_) (Measurable.imp hR.not ?_))
  · exact measurableSet_setOf.1 (DFI_eq_meas ha hj)
  · refine Measurable.forall fun i => ?_
    exact measurableSet_setOf.1 (measurableSet_le
      (hγ.comp ((measurable_pi_apply i).comp hs)) (hγ.comp (DFI_meas_dep hs ha)))

theorem DFI_ae_fst {α B : Type*} [MeasurableSpace α] [MeasurableSpace B] {μ : Measure α}
    [IsFiniteMeasure μ] {κ : Kernel α B} [IsMarkovKernel κ] {q : α → Prop}
    (hq : ∀ᵐ a ∂μ, q a) : ∀ᵐ p ∂(μ ⊗ₘ κ), q p.1 := by
  apply ae_of_ae_map measurable_fst.aemeasurable
  show ∀ᵐ y ∂(μ ⊗ₘ κ).fst, q y
  rw [Measure.fst_compProd]; exact hq

theorem DFI_allowed_ae {k : ℕ} {S : Type*} [MeasurableSpace S] (P : Kernel S S)
    [IsMarkovKernel P] (r : S → ℝ) (β : ℝ) (hγ : Measurable (gittinsIndex P r β))
    (ρ : MarkovBanditPolicy k S)
    (hρ : WeberGittins.IndexGap.IsRunThenGittinsAt P r β ρ 0 ρ) (x : Fin k → S) (n : ℕ) :
    ∀ᵐ p ∂(markovBanditMeasure P ρ x (n + 1) ⊗ₘ markovBanditStepKernel P ρ (n + 1)),
      DFI_Allowed P r β p.1 p.2.1 := by
  refine Measure.ae_compProd_of_ae_ae (DFI_allowed_meas P r β hγ n) (ae_of_all _ fun h => ?_)
  have e : (markovBanditStepKernel P ρ (n + 1) h).map Prod.fst = ρ.select (n + 1) h := by
    rw [← Kernel.fst_apply, markovBanditStepKernel, Kernel.fst_compProd]
  have hρn := hρ.2 (n + 1) (Nat.succ_pos n) h
  have key : ∀ᵐ a ∂ρ.select (n + 1) h, DFI_Allowed P r β h a := by
    by_cases hrc : DFI_RC P r β h
    · have hm := hρn.1 hrc
      have hae : ∀ᵐ a ∂ρ.select (n + 1) h,
          a ∈ ({(h.1 ⟨0, Nat.succ_pos n⟩).2} : Set (Fin k)) :=
        ae_iff.2 ((prob_compl_eq_zero_iff (Set.toFinite _).measurableSet).2 hm)
      filter_upwards [hae] with a ha
      exact ⟨fun _ => Set.mem_singleton_iff.1 ha, fun hn => absurd hrc hn⟩
    · have hm := hρn.2 hrc
      have hae : ∀ᵐ a ∂ρ.select (n + 1) h, a ∈ {a | ∀ i, gittinsIndex P r β (h.2 i) ≤
          gittinsIndex P r β (h.2 a)} :=
        ae_iff.2 ((prob_compl_eq_zero_iff (Set.toFinite _).measurableSet).2 hm)
      filter_upwards [hae] with a ha
      exact ⟨fun hh => absurd hh hrc, fun _ => ha⟩
  rw [← e] at key
  exact ae_of_ae_map measurable_fst.aemeasurable key

theorem DFI_inv_ae {k : ℕ} {S : Type*} [MeasurableSpace S] (P : Kernel S S) [IsMarkovKernel P]
    (r : S → ℝ) (β : ℝ) (hγ : Measurable (gittinsIndex P r β)) (ρ : MarkovBanditPolicy k S)
    (hρ : WeberGittins.IndexGap.IsRunThenGittinsAt P r β ρ 0 ρ) (x : Fin k → S) :
    ∀ n, ∀ᵐ h ∂markovBanditMeasure P ρ x (n + 1), DFI_Inv P r β h := by
  intro n
  induction n with
  | zero =>
    rw [markovBanditMeasure,
      ae_map_iff measurable_markovBanditSnoc.aemeasurable (DFI_inv_meas P r β hγ 0)]
    exact ae_of_all _ fun p => DFI_inv_base P r β p.1 p.2.1 p.2.2
  | succ n ih =>
    rw [markovBanditMeasure,
      ae_map_iff measurable_markovBanditSnoc.aemeasurable (DFI_inv_meas P r β hγ (n + 1))]
    filter_upwards [DFI_ae_fst ih, DFI_allowed_ae P r β hγ ρ hρ x n] with p hp1 hp2
    exact DFI_inv_step P r β p.1 p.2.1 p.2.2 hp1 hp2

/-! C1 assembly for df742747 (session 8): theorem2 + K1 + round invariant => eq. (8) at t = 0. -/

open MeasureTheory ProbabilityTheory BanditAlgorithm

theorem DFC_chpc_div {k : ℕ} {S : Type*} (g : S → ℝ) {c : ℝ} (hc : 0 < c) :
    ∀ (n : ℕ) (h : MarkovBanditHistory k S n) (i : Fin k),
      currentHistoryPrevailingCharge (fun y => g y / c) n h i =
        currentHistoryPrevailingCharge g n h i / c
  | 0, h, i => rfl
  | n + 1, h, i => by
      simp only [currentHistoryPrevailingCharge]
      rw [DFC_chpc_div g hc n]
      exact min_div_div_right hc.le _ _

theorem DFC_arm_meas {k n : ℕ} {S : Type*} [MeasurableSpace S] :
    Measurable (fun h : MarkovBanditHistory k S (n + 1) => (h.1 (Fin.last n)).2) :=
  measurable_snd.comp ((measurable_pi_apply _).comp measurable_fst)

theorem DFC_jm {α : Type*} [MeasurableSpace α] {k : ℕ} {F : α → Fin k → ℝ}
    (hF : ∀ j, Measurable (fun a => F a j)) :
    Measurable (fun q : α × Fin k => F q.1 q.2) :=
  measurable_from_prod_countable_left (fun j => hF j)

/-- Round expectation as an integral over the step measure. -/
theorem DFC_re_nu {k : ℕ} {S : Type*} [MeasurableSpace S] (P : Kernel S S) [IsMarkovKernel P]
    (π : MarkovBanditPolicy k S) (x : Fin k → S) (n : ℕ)
    (G : MarkovBanditHistory k S n → Fin k → ℝ)
    (hG : Measurable (fun q : MarkovBanditHistory k S n × Fin k => G q.1 q.2)) :
    WeberGittins.Suboptimality.roundExpectation P π x n G =
      ∫ p, G p.1 p.2.1 ∂(markovBanditMeasure P π x n ⊗ₘ markovBanditStepKernel P π n) := by
  unfold WeberGittins.Suboptimality.roundExpectation
  rw [DF742747B_next_int P π x n
    (fun h => G (truncateMarkovBanditHistory h) (h.1 (Fin.last n)).2)
    (hG.comp (DF742747B_trunc_meas.prodMk DFC_arm_meas))]
  congr 1
  funext p
  simp only [DF742747B_trunc_snoc, Fin.snoc_last]

/-- Round-0 index gap, read off a history of at least one round. -/
noncomputable def DFC_B {k : ℕ} {S : Type*} [MeasurableSpace S] (P : Kernel S S)
    [IsMarkovKernel P] (r : S → ℝ) (β : ℝ) {n : ℕ} (h : MarkovBanditHistory k S (n + 1)) : ℝ :=
  (⨆ l, gittinsIndex P r β ((h.1 ⟨0, Nat.succ_pos n⟩).1 l)) -
    gittinsIndex P r β ((h.1 ⟨0, Nat.succ_pos n⟩).1 (h.1 ⟨0, Nat.succ_pos n⟩).2)

theorem DFC_B_meas {k : ℕ} {S : Type*} [MeasurableSpace S] (P : Kernel S S) [IsMarkovKernel P]
    (r : S → ℝ) (β : ℝ) (hγ : Measurable (gittinsIndex P r β)) (n : ℕ) :
    Measurable (fun h : MarkovBanditHistory k S (n + 1) => DFC_B P r β h) := by
  have h0 : Measurable (fun h : MarkovBanditHistory k S (n + 1) =>
      (h.1 ⟨0, Nat.succ_pos n⟩).1) :=
    measurable_fst.comp ((measurable_pi_apply _).comp measurable_fst)
  have h1 : Measurable (fun h : MarkovBanditHistory k S (n + 1) =>
      (h.1 ⟨0, Nat.succ_pos n⟩).2) :=
    measurable_snd.comp ((measurable_pi_apply _).comp measurable_fst)
  exact (Measurable.iSup fun l => hγ.comp ((measurable_pi_apply l).comp h0)).sub
    (hγ.comp (DFI_meas_dep h0 h1))

theorem DFC_sup_bounds {k : ℕ} (f : Fin k → ℝ) {C : ℝ} (hf : ∀ i, 0 ≤ f i ∧ f i ≤ C) :
    0 ≤ ⨆ i, f i ∧ ⨆ i, f i ≤ |C| :=
  ⟨Real.iSup_nonneg fun i => (hf i).1,
    Real.iSup_le (fun i => (hf i).2.trans (le_abs_self C)) (abs_nonneg C)⟩

theorem DFC_B_bound {k : ℕ} {S : Type*} [MeasurableSpace S] (P : Kernel S S) [IsMarkovKernel P]
    (r : S → ℝ) (β : ℝ) {C : ℝ}
    (hγb : ∀ z, 0 ≤ gittinsIndex P r β z ∧ gittinsIndex P r β z ≤ C) {n : ℕ}
    (h : MarkovBanditHistory k S (n + 1)) : |DFC_B P r β h| ≤ |C| + |C| := by
  have hs := DFC_sup_bounds (fun l => gittinsIndex P r β ((h.1 ⟨0, Nat.succ_pos n⟩).1 l))
    (fun l => hγb _)
  have hg := hγb ((h.1 ⟨0, Nat.succ_pos n⟩).1 (h.1 ⟨0, Nat.succ_pos n⟩).2)
  have hC := le_abs_self C
  unfold DFC_B
  rw [abs_le]; constructor <;> linarith [hs.1, hs.2, hg.1, hg.2, abs_nonneg C]

theorem DFC_B_nonneg {k : ℕ} {S : Type*} [MeasurableSpace S] (P : Kernel S S) [IsMarkovKernel P]
    (r : S → ℝ) (β : ℝ) {n : ℕ} (h : MarkovBanditHistory k S (n + 1)) :
    0 ≤ DFC_B P r β h := by
  unfold DFC_B
  exact sub_nonneg.2 (DFI_le_sup (fun l => gittinsIndex P r β ((h.1 ⟨0, Nat.succ_pos n⟩).1 l)) _)

theorem DFC_snoc_zero {k t : ℕ} {S : Type*} (f : Fin (t + 1) → (Fin k → S) × Fin k)
    (a : (Fin k → S) × Fin k) :
    (Fin.snoc (α := fun _ ↦ (Fin k → S) × Fin k) f a : Fin (t + 2) → _)
      ⟨0, Nat.succ_pos (t + 1)⟩ = f ⟨0, Nat.succ_pos t⟩ :=
  Fin.snoc_castSucc (α := fun _ ↦ (Fin k → S) × Fin k) (p := f) (x := a)
    (i := ⟨0, Nat.succ_pos t⟩)

/-- The round-0 gap has the same law at every round. -/
theorem DFC_marg {k : ℕ} {S : Type*} [MeasurableSpace S] (P : Kernel S S) [IsMarkovKernel P]
    (r : S → ℝ) (β : ℝ) (hγ : Measurable (gittinsIndex P r β)) {C : ℝ}
    (hγb : ∀ z, 0 ≤ gittinsIndex P r β z ∧ gittinsIndex P r β z ≤ C)
    (π : MarkovBanditPolicy k S) (x : Fin k → S) :
    ∀ t : ℕ, ∫ h, DFC_B P r β h ∂markovBanditMeasure P π x (t + 1) =
      ∫ h, DFC_B P r β h ∂markovBanditMeasure P π x 1
  | 0 => rfl
  | t + 1 => by
      rw [DF742747B_next_int P π x (t + 1) _ (DFC_B_meas P r β hγ (t + 1)), ← DFC_marg P r β hγ hγb π x t]
      have e : ∀ p : MarkovBanditHistory k S (t + 1) × (Fin k × S),
          DFC_B P r β ((Fin.snoc (α := fun _ ↦ (Fin k → S) × Fin k) p.1.1 (p.1.2, p.2.1),
            Function.update p.1.2 p.2.1 p.2.2) : MarkovBanditHistory k S (t + 1 + 1)) =
          DFC_B P r β p.1 := by
        intro p
        unfold DFC_B
        dsimp only
        rw [DFC_snoc_zero]
      simp only [e]
      exact DF742747B_int_fst _ _ (fun h => DFC_B P r β h) (DFC_B_meas P r β hγ t) _
        (fun h => DFC_B_bound P r β hγb h)

/-- C1 assembly: theorem2 + K1 + the round invariant. -/
theorem DFC_C1 {k : ℕ} {S : Type*} [MeasurableSpace S] (P : Kernel S S) [IsMarkovKernel P]
    {r : S → ℝ} (hr : Measurable r) (hr0 : ∀ y, 0 ≤ r y) {C : ℝ} (hC : ∀ y, r y ≤ C)
    {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hγ : Measurable (gittinsIndex P r β))
    (hγb : ∀ z, 0 ≤ gittinsIndex P r β z ∧ gittinsIndex P r β z ≤ C)
    (hRm : Measurable (fun z : ℝ × S ↦ gittinsRetirementValue P r β z.1 z.2))
    (hret0 : ∀ (c : ℝ) (z : S), gittinsIndex P r β z ≤ c →
      gittinsRetirementValue P r β c z = 0)
    (K : ℝ) (hPot : ∀ (m : ℕ) (h : MarkovBanditHistory k S m),
      |currentGittinsRetirementPotential P r β h| ≤ K)
    (σstar ρ : MarkovBanditPolicy k S) (x : Fin k → S)
    (h2 : markovBanditDiscountedValue P r β σstar x - markovBanditDiscountedValue P r β ρ x ≤
      (1 - β) * ∑' t : ℕ, β ^ t * WeberGittins.Suboptimality.roundExpectation P ρ x t
        (fun h j => (⨆ i : Fin k, currentHistoryPrevailingCharge
          (WeberGittins.Suboptimality.weberIndex P r β) t h i) - r (h.2 j) / (1 - β)))
    (hK1 : ∀ N : ℕ, (∑ n ∈ Finset.range N, β ^ n * markovBanditRoundReward P r ρ x n) +
        β ^ N * markovBanditExpectedRetirementPotential P r β ρ x N +
        (1 - β) * ∑ n ∈ Finset.range N, β ^ n *
          WeberGittins.Suboptimality.roundExpectation P ρ x n (fun h j =>
            ∑ i ∈ Finset.univ.erase j, gittinsRetirementValue P r β
              (currentHistoryPrevailingCharge (gittinsIndex P r β) n h i) (h.2 i)) =
      markovBanditFinitePrevailingChargeValue P r β ρ x N)
    (hround : ∀ n : ℕ, ∀ᵐ p ∂(markovBanditMeasure P ρ x n ⊗ₘ markovBanditStepKernel P ρ n),
      (∀ i, i ≠ p.2.1 → gittinsIndex P r β (p.1.2 i) ≤
          currentHistoryPrevailingCharge (gittinsIndex P r β) n p.1 i) ∧
      (⨆ i, currentHistoryPrevailingCharge (gittinsIndex P r β) n p.1 i) -
          currentHistoryPrevailingCharge (gittinsIndex P r β) n p.1 p.2.1 ≤
        DFC_B P r β ((Fin.snoc (α := fun _ ↦ (Fin k → S) × Fin k) p.1.1 (p.1.2, p.2.1),
          Function.update p.1.2 p.2.1 p.2.2) : MarkovBanditHistory k S (n + 1))) :
    markovBanditDiscountedValue P r β σstar x - markovBanditDiscountedValue P r β ρ x ≤
      WeberGittins.Suboptimality.roundExpectation P ρ x 0 (fun h j =>
        ((⨆ i : Fin k, gittinsIndex P r β (h.2 i)) - gittinsIndex P r β (h.2 j)) / (1 - β)) := by
  set γ := gittinsIndex P r β with hγdef
  have h1β : 0 < 1 - β := by linarith
  have hrb : ∀ y, |r y| ≤ |C| := fun y => abs_le.2
    ⟨by linarith [hr0 y, abs_nonneg C], (hC y).trans (le_abs_self C)⟩
  have chm : ∀ (t : ℕ) (i : Fin k), Measurable
      (fun h : MarkovBanditHistory k S t => currentHistoryPrevailingCharge γ t h i) :=
    DF742747B_chpc_meas hγ
  have chb : ∀ (t : ℕ) (h : MarkovBanditHistory k S t) (i : Fin k),
      0 ≤ currentHistoryPrevailingCharge γ t h i ∧ currentHistoryPrevailingCharge γ t h i ≤ C :=
    DF742747B_chpc_bounds γ hγb
  -- A t q = largest prevailing charge
  have Am : ∀ t : ℕ, Measurable (fun h : MarkovBanditHistory k S t =>
      ⨆ i, currentHistoryPrevailingCharge γ t h i) :=
    fun t => Measurable.iSup fun i => chm t i
  have Ab : ∀ (t : ℕ) (h : MarkovBanditHistory k S t),
      |⨆ i, currentHistoryPrevailingCharge γ t h i| ≤ |C| := by
    intro t h
    have := DFC_sup_bounds (fun i => currentHistoryPrevailingCharge γ t h i) (chb t h)
    rw [abs_le]; constructor <;> linarith [this.1, this.2, abs_nonneg C]
  have rpm : ∀ t : ℕ, Measurable (fun p : MarkovBanditHistory k S t × (Fin k × S) =>
      r (p.1.2 p.2.1)) := fun t =>
    hr.comp (DFI_meas_dep (measurable_snd.comp measurable_fst) (measurable_fst.comp measurable_snd))
  have cpm : ∀ t : ℕ, Measurable (fun p : MarkovBanditHistory k S t × (Fin k × S) =>
      currentHistoryPrevailingCharge γ t p.1 p.2.1) := fun t =>
    DFI_meas_dep (f := fun p : MarkovBanditHistory k S t × (Fin k × S) =>
        fun i => currentHistoryPrevailingCharge γ t p.1 i)
      (measurable_pi_lambda _ fun i => (chm t i).comp measurable_fst)
      (measurable_fst.comp measurable_snd)
  -- integrals on the step measure
  have IA : ∀ t, Integrable (fun p : MarkovBanditHistory k S t × (Fin k × S) =>
      ⨆ i, currentHistoryPrevailingCharge γ t p.1 i)
      (markovBanditMeasure P ρ x t ⊗ₘ markovBanditStepKernel P ρ t) := fun t =>
    p2mbf_int_of_bound _ _ ((Am t).comp measurable_fst) |C| (fun p => Ab t p.1)
  have IR : ∀ t, Integrable (fun p : MarkovBanditHistory k S t × (Fin k × S) => r (p.1.2 p.2.1))
      (markovBanditMeasure P ρ x t ⊗ₘ markovBanditStepKernel P ρ t) := fun t =>
    p2mbf_int_of_bound _ _ (rpm t) |C| (fun p => hrb _)
  have IC : ∀ t, Integrable (fun p : MarkovBanditHistory k S t × (Fin k × S) =>
      currentHistoryPrevailingCharge γ t p.1 p.2.1)
      (markovBanditMeasure P ρ x t ⊗ₘ markovBanditStepKernel P ρ t) := fun t =>
    p2mbf_int_of_bound _ _ (cpm t) |C| (fun p => abs_le.2
      ⟨by linarith [(chb t p.1 p.2.1).1, abs_nonneg C], (chb t p.1 p.2.1).2.trans (le_abs_self C)⟩)
  -- round reward on the step measure
  have hR : ∀ t, markovBanditRoundReward P r ρ x t =
      ∫ p, r (p.1.2 p.2.1) ∂(markovBanditMeasure P ρ x t ⊗ₘ markovBanditStepKernel P ρ t) := by
    intro t
    have := DFC_re_nu P ρ x t (fun h j => r (h.2 j))
      (DFC_jm fun j => hr.comp ((measurable_pi_apply j).comp measurable_snd))
    exact this
  -- theorem2 term
  set I_A : ℕ → ℝ := fun t => ∫ p, ⨆ i, currentHistoryPrevailingCharge γ t p.1 i
    ∂(markovBanditMeasure P ρ x t ⊗ₘ markovBanditStepKernel P ρ t) with hIA
  have hT : ∀ t, (1 - β) * WeberGittins.Suboptimality.roundExpectation P ρ x t
      (fun h j => (⨆ i : Fin k, currentHistoryPrevailingCharge
        (WeberGittins.Suboptimality.weberIndex P r β) t h i) - r (h.2 j) / (1 - β)) =
      I_A t - markovBanditRoundReward P r ρ x t := by
    intro t
    have hw : (fun h : MarkovBanditHistory k S t => fun j : Fin k =>
        (⨆ i : Fin k, currentHistoryPrevailingCharge
          (WeberGittins.Suboptimality.weberIndex P r β) t h i) - r (h.2 j) / (1 - β)) =
        fun h j => ((⨆ i, currentHistoryPrevailingCharge γ t h i) - r (h.2 j)) / (1 - β) := by
      funext h j
      have e1 : ∀ i, currentHistoryPrevailingCharge
          (WeberGittins.Suboptimality.weberIndex P r β) t h i =
          currentHistoryPrevailingCharge γ t h i * (1 - β)⁻¹ := by
        intro i
        rw [← div_eq_mul_inv]
        exact DFC_chpc_div γ h1β t h i
      simp only [e1]
      rw [← Real.iSup_mul_of_nonneg (inv_nonneg.2 h1β.le), sub_div, div_eq_mul_inv,
        div_eq_mul_inv]
    rw [hw, DFC_re_nu P ρ x t (fun h j => ((⨆ i, currentHistoryPrevailingCharge γ t h i) - r (h.2 j)) / (1 - β)) (DFC_jm fun j => (((Am t).sub
      (hr.comp ((measurable_pi_apply j).comp measurable_snd))).div_const _)),
      integral_div, integral_sub (IA t) (IR t), hR t, mul_div_cancel₀ _ h1β.ne']
  -- loss terms vanish
  have hL : ∀ n, WeberGittins.Suboptimality.roundExpectation P ρ x n (fun h j =>
      ∑ i ∈ Finset.univ.erase j, gittinsRetirementValue P r β
        (currentHistoryPrevailingCharge γ n h i) (h.2 i)) = 0 := by
    intro n
    rw [DFC_re_nu P ρ x n (fun h j => ∑ i ∈ Finset.univ.erase j, gittinsRetirementValue P r β
        (currentHistoryPrevailingCharge γ n h i) (h.2 i)) (DFC_jm fun j => Finset.measurable_sum _ fun i _ =>
      hRm.comp ((chm n i).prodMk ((measurable_pi_apply i).comp measurable_snd)))]
    apply integral_eq_zero_of_ae
    filter_upwards [hround n] with p hp
    exact Finset.sum_eq_zero fun i hi => hret0 _ _ (hp.1 i (Finset.ne_of_mem_erase hi))
  -- accounting identity without loss
  have hK : ∀ N, (∑ n ∈ Finset.range N, β ^ n * markovBanditRoundReward P r ρ x n) +
      β ^ N * markovBanditExpectedRetirementPotential P r β ρ x N =
      ∑ n ∈ Finset.range N, β ^ n * ∫ p, currentHistoryPrevailingCharge γ n p.1 p.2.1
        ∂(markovBanditMeasure P ρ x n ⊗ₘ markovBanditStepKernel P ρ n) := by
    intro N
    have := hK1 N
    simp only [hL, mul_zero, Finset.sum_const_zero, add_zero] at this
    rw [this]
    rfl
  -- per-round gap
  set G0 : ℝ := ∫ h, DFC_B P r β h ∂markovBanditMeasure P ρ x 1 with hG0
  have hgap : ∀ t, I_A t - ∫ p, currentHistoryPrevailingCharge γ t p.1 p.2.1
      ∂(markovBanditMeasure P ρ x t ⊗ₘ markovBanditStepKernel P ρ t) ≤ G0 := by
    intro t
    have hsm : Measurable (fun p : MarkovBanditHistory k S t × (Fin k × S) =>
        ((Fin.snoc (α := fun _ ↦ (Fin k → S) × Fin k) p.1.1 (p.1.2, p.2.1),
          Function.update p.1.2 p.2.1 p.2.2) : MarkovBanditHistory k S (t + 1))) :=
      measurable_markovBanditSnoc
    rw [hIA, ← integral_sub (IA t) (IC t), hG0, ← DFC_marg P r β hγ hγb ρ x t,
      DF742747B_next_int P ρ x t _ (DFC_B_meas P r β hγ t)]
    apply integral_mono_ae ((IA t).sub (IC t))
      (p2mbf_int_of_bound _ _ ((DFC_B_meas P r β hγ t).comp hsm) _
        (fun p => DFC_B_bound P r β hγb _))
    filter_upwards [hround t] with p hp
    exact hp.2
  -- potential bound
  have hPb : ∀ N, |markovBanditExpectedRetirementPotential P r β ρ x N| ≤ K := fun N =>
    p2mbf_abs_int_le _ _ K (fun h => hPot N h)
  -- partial sums
  set U : ℝ := G0 / (1 - β) with hU
  have hpart : ∀ N, ∑ t ∈ Finset.range N, β ^ t * (I_A t - markovBanditRoundReward P r ρ x t) ≤
      U + β ^ N * (K - U) := by
    intro N
    have e := hK N
    have hs : ∑ t ∈ Finset.range N, β ^ t * (I_A t - markovBanditRoundReward P r ρ x t) =
        ∑ t ∈ Finset.range N, β ^ t * (I_A t - ∫ p, currentHistoryPrevailingCharge γ t p.1 p.2.1
          ∂(markovBanditMeasure P ρ x t ⊗ₘ markovBanditStepKernel P ρ t)) +
        β ^ N * markovBanditExpectedRetirementPotential P r β ρ x N := by
      simp only [mul_sub, Finset.sum_sub_distrib]
      linarith
    have hle : ∑ t ∈ Finset.range N, β ^ t * (I_A t - ∫ p, currentHistoryPrevailingCharge γ t
        p.1 p.2.1 ∂(markovBanditMeasure P ρ x t ⊗ₘ markovBanditStepKernel P ρ t)) ≤
        ∑ t ∈ Finset.range N, β ^ t * G0 :=
      Finset.sum_le_sum fun t _ => mul_le_mul_of_nonneg_left (hgap t) (pow_nonneg hβ0.le t)
    have hgeo : ∑ t ∈ Finset.range N, β ^ t * G0 = U - β ^ N * U := by
      have hb1 : β - 1 ≠ 0 := (sub_neg.2 hβ1).ne
      have hb2 : 1 - β ≠ 0 := h1β.ne'
      rw [← Finset.sum_mul, geom_sum_eq hβ1.ne, hU]
      field_simp
      ring
    have hp := hPb N
    have hpot : β ^ N * markovBanditExpectedRetirementPotential P r β ρ x N ≤ β ^ N * K :=
      mul_le_mul_of_nonneg_left (le_of_abs_le hp) (pow_nonneg hβ0.le N)
    rw [hs]
    linarith
  have hG0nn : 0 ≤ G0 := integral_nonneg fun h => DFC_B_nonneg P r β h
  have hUnn : 0 ≤ U := div_nonneg hG0nn h1β.le
  -- tsum bound
  have htsum : ∑' t : ℕ, β ^ t * (I_A t - markovBanditRoundReward P r ρ x t) ≤ U := by
    by_cases hs : Summable (fun t : ℕ => β ^ t * (I_A t - markovBanditRoundReward P r ρ x t))
    · have h1 := hs.hasSum.tendsto_sum_nat
      have h2' : Filter.Tendsto (fun N : ℕ => U + β ^ N * (K - U)) Filter.atTop
          (nhds (U + 0 * (K - U))) :=
        tendsto_const_nhds.add
          ((tendsto_pow_atTop_nhds_zero_of_lt_one hβ0.le hβ1).mul tendsto_const_nhds)
      rw [zero_mul, add_zero] at h2'
      exact le_of_tendsto_of_tendsto' h1 h2' hpart
    · rw [tsum_eq_zero_of_not_summable hs]
      exact hUnn
  have hRHS : WeberGittins.Suboptimality.roundExpectation P ρ x 0 (fun h j =>
      ((⨆ i : Fin k, γ (h.2 i)) - γ (h.2 j)) / (1 - β)) = U := by
    unfold WeberGittins.Suboptimality.roundExpectation
    rw [hU, hG0, ← integral_div]
    rfl
  rw [hRHS]
  refine h2.trans (Eq.trans_le ?_ htsum)
  rw [← tsum_mul_left]
  congr 1
  funext t
  rw [← hT t]
  ring

/-! Round consequences of the INV invariant for df742747 (session 8). -/

open MeasureTheory ProbabilityTheory BanditAlgorithm

theorem DFC_sup_le {k : ℕ} (f : Fin k → ℝ) (a : Fin k) {M : ℝ} (hf : ∀ i, f i ≤ M) :
    ⨆ i, f i ≤ M := by
  haveI : Nonempty (Fin k) := ⟨a⟩
  exact ciSup_le hf

/-- Round facts: unplayed arms have index at most their prevailing charge, and the
prevailing-charge gap is at most the round-0 index gap. -/
theorem DFC_round {k : ℕ} {S : Type*} [MeasurableSpace S] (P : Kernel S S) [IsMarkovKernel P]
    (r : S → ℝ) (β : ℝ) (hγ : Measurable (gittinsIndex P r β)) (ρ : MarkovBanditPolicy k S)
    (hρ : WeberGittins.IndexGap.IsRunThenGittinsAt P r β ρ 0 ρ) (x : Fin k → S) (n : ℕ) :
    ∀ᵐ p ∂(markovBanditMeasure P ρ x n ⊗ₘ markovBanditStepKernel P ρ n),
      (∀ i, i ≠ p.2.1 → gittinsIndex P r β (p.1.2 i) ≤
          currentHistoryPrevailingCharge (gittinsIndex P r β) n p.1 i) ∧
      (⨆ i, currentHistoryPrevailingCharge (gittinsIndex P r β) n p.1 i) -
          currentHistoryPrevailingCharge (gittinsIndex P r β) n p.1 p.2.1 ≤
        DFC_B P r β ((Fin.snoc (α := fun _ ↦ (Fin k → S) × Fin k) p.1.1 (p.1.2, p.2.1),
          Function.update p.1.2 p.2.1 p.2.2) : MarkovBanditHistory k S (n + 1)) := by
  cases n with
  | zero =>
    refine Filter.Eventually.of_forall fun p => ⟨fun i _ => le_rfl, le_of_eq ?_⟩
    have e : (Fin.snoc (α := fun _ ↦ (Fin k → S) × Fin k) p.1.1 (p.1.2, p.2.1) : Fin 1 → _)
        ⟨0, Nat.succ_pos 0⟩ = (p.1.2, p.2.1) :=
      Fin.snoc_last (α := fun _ ↦ (Fin k → S) × Fin k) (p := p.1.1) (x := (p.1.2, p.2.1))
    first
      | rfl
      | (unfold DFC_B; dsimp only; rw [e]; rfl)
  | succ m =>
    filter_upwards [DFI_ae_fst (κ := markovBanditStepKernel P ρ (m + 1))
      (DFI_inv_ae P r β hγ ρ hρ x m), DFI_allowed_ae P r β hγ ρ hρ x m] with p hI hA
    set h := p.1 with hh
    set a := p.2.1 with ha
    have hB : DFC_B P r β ((Fin.snoc (α := fun _ ↦ (Fin k → S) × Fin k) p.1.1 (p.1.2, p.2.1),
          Function.update p.1.2 p.2.1 p.2.2) : MarkovBanditHistory k S (m + 1 + 1)) =
        DFC_B P r β h := by
      unfold DFC_B
      dsimp only
      rw [DFC_snoc_zero]
    rw [hB]
    have hBnn := DFC_B_nonneg P r β h
    by_cases hrc : DFI_RC P r β h
    · obtain ⟨hc, hoth⟩ := hI.1 hrc
      have haj : a = (h.1 ⟨0, Nat.succ_pos m⟩).2 := hA.1 hrc
      refine ⟨fun i hi => (hoth i (haj ▸ hi)).1, ?_⟩
      have hsup : (⨆ i, currentHistoryPrevailingCharge (gittinsIndex P r β) (m + 1) h i) ≤
          ⨆ l, gittinsIndex P r β ((h.1 ⟨0, Nat.succ_pos m⟩).1 l) := by
        apply DFC_sup_le _ a
        intro i
        by_cases hi : i = (h.1 ⟨0, Nat.succ_pos m⟩).2
        · rw [hi, hc]
          exact DFI_le_sup (fun l => gittinsIndex P r β ((h.1 ⟨0, Nat.succ_pos m⟩).1 l)) _
        · exact (DF742747B_chpc_le _ (m + 1) h i).trans (hoth i hi).2
      rw [haj, hc]
      unfold DFC_B
      linarith
    · have hG := hI.2 hrc
      have hmax := hA.2 hrc
      obtain ⟨k1, k2⟩ := DFI_G_key hG hmax
      refine ⟨k1, ?_⟩
      have hsup : (⨆ i, currentHistoryPrevailingCharge (gittinsIndex P r β) (m + 1) h i) ≤
          currentHistoryPrevailingCharge (gittinsIndex P r β) (m + 1) h a := by
        apply DFC_sup_le _ a
        intro i
        by_cases hi : i = a
        · rw [hi]
        · exact (DF742747B_chpc_le _ (m + 1) h i).trans (k2 i hi)
      linarith

/-! C1 instantiation for df742747 (session 8, NOT YET COMPILED): DFC_C1 with the K1B/INV lemmas. -/

open MeasureTheory ProbabilityTheory BanditAlgorithm in
theorem DFC_C1_main {k : ℕ} {S : Type*} [MeasurableSpace S] (P : Kernel S S) [IsMarkovKernel P]
    {r : S → ℝ} (hr : Measurable r) (hrb : WeberGittins.Suboptimality.RewardsNonnegBounded r)
    {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hγ : Measurable (gittinsIndex P r β))
    (σstar ρ : MarkovBanditPolicy k S) (x : Fin k → S)
    (h2 : markovBanditDiscountedValue P r β σstar x - markovBanditDiscountedValue P r β ρ x ≤
      (1 - β) * ∑' t : ℕ, β ^ t * WeberGittins.Suboptimality.roundExpectation P ρ x t
        (fun h j => (⨆ i : Fin k, currentHistoryPrevailingCharge
          (WeberGittins.Suboptimality.weberIndex P r β) t h i) - r (h.2 j) / (1 - β)))
    (hρ : WeberGittins.IndexGap.IsRunThenGittinsAt P r β ρ 0 ρ) :
    markovBanditDiscountedValue P r β σstar x - markovBanditDiscountedValue P r β ρ x ≤
      WeberGittins.Suboptimality.roundExpectation P ρ x 0 (fun h j =>
        ((⨆ i : Fin k, gittinsIndex P r β (h.2 i)) - gittinsIndex P r β (h.2 j)) / (1 - β)) := by
  obtain ⟨hr0, C, hC⟩ := id hrb
  exact DFC_C1 P hr hr0 hC hβ0 hβ1 hγ
    (fun z => DF742747B_gi_bounds P hr hr0 hC hβ0 hβ1 z)
    (DF742747B_ret_meas2 P hr hrb hβ0 hβ1)
    (fun c z hz => DF742747B_ret_zero P hr hrb hβ0 hβ1 c z hz)
    _ (fun m h => DF742747B_pot_bound P hr hr0 hC hβ0 hβ1 m h)
    σstar ρ x h2 (fun N => DF742747B_K1 P hr hrb hβ0 hβ1 hγ ρ x N)
    (fun n => DFC_round P r β hγ ρ hρ x n)


open MeasureTheory ProbabilityTheory BanditAlgorithm

/-! Restart lemma R for df742747: the history law at time `t + n` is the law at time `t`
followed by the continuation policy run for `n` rounds from the current states. -/

namespace DF742747R

variable {S : Type*} [MeasurableSpace S] {k : ℕ}

/-- Concatenation of a `t`-round history with an `n`-round history. -/
def happ {t n : ℕ} (h : MarkovBanditHistory k S t) (h' : MarkovBanditHistory k S n) :
    MarkovBanditHistory k S (t + n) :=
  (Fin.append h.1 h'.1, h'.2)

lemma measurable_happ {t n : ℕ} :
    Measurable (fun p : MarkovBanditHistory k S t × MarkovBanditHistory k S n =>
      happ p.1 p.2) := by
  refine Measurable.prodMk ?_ (measurable_snd.comp measurable_snd)
  rw [measurable_pi_iff]
  intro i
  refine Fin.addCases (fun i => ?_) (fun i => ?_) i
  · simp only [happ, Fin.append_left]
    exact (measurable_pi_apply i).comp (measurable_fst.comp measurable_fst)
  · simp only [happ, Fin.append_right]
    exact (measurable_pi_apply i).comp (measurable_fst.comp measurable_snd)

lemma measurable_happ_left {t n : ℕ} (h : MarkovBanditHistory k S t) :
    Measurable (happ (n := n) h) :=
  measurable_happ.comp measurable_prodMk_left

/-- The continuation of `s` after the `t`-round history `h`. -/
noncomputable def cont (s : MarkovBanditPolicy k S) {t : ℕ} (h : MarkovBanditHistory k S t) :
    MarkovBanditPolicy k S where
  select n := (s.select (t + n)).comap (happ h) (measurable_happ_left h)
  markov n := by infer_instance

/-- One bandit round applied to a history (the map used in `markovBanditMeasure`). -/
def snocF {n : ℕ} (p : MarkovBanditHistory k S n × (Fin k × S)) :
    MarkovBanditHistory k S (n + 1) :=
  (Fin.snoc (α := fun _ ↦ (Fin k → S) × Fin k) p.1.1 (p.1.2, p.2.1),
    Function.update p.1.2 p.2.1 p.2.2)

lemma measurable_snocF {n : ℕ} : Measurable (snocF (k := k) (S := S) (n := n)) :=
  measurable_markovBanditSnoc

lemma snocF_happ {t n : ℕ} (h : MarkovBanditHistory k S t) (h' : MarkovBanditHistory k S n)
    (q : Fin k × S) : snocF (happ h h', q) = happ h (snocF (h', q)) := by
  simp only [snocF, happ]
  refine Prod.ext ?_ rfl
  exact (Fin.append_snoc h.1 h'.1 (h'.2, q.1)).symm

lemma step_cont (P : Kernel S S) [IsMarkovKernel P] (s : MarkovBanditPolicy k S) {t : ℕ}
    (h : MarkovBanditHistory k S t) (n : ℕ) (h' : MarkovBanditHistory k S n) :
    markovBanditStepKernel P (cont s h) n h' = markovBanditStepKernel P s (t + n) (happ h h') := by
  ext B hB
  simp only [markovBanditStepKernel, Kernel.compProd_apply hB, Kernel.comap_apply, cont]
  rfl

variable (P : Kernel S S) [IsMarkovKernel P]

/-- The continuation law as a kernel in the round-`t` history. -/
noncomputable def kap (s : MarkovBanditPolicy k S) (t : ℕ) :
    (n : ℕ) → Kernel (MarkovBanditHistory k S t) (MarkovBanditHistory k S n)
  | 0 => Kernel.deterministic
      (fun h => ((Fin.elim0 : Fin 0 → (Fin k → S) × Fin k), h.2))
      (measurable_const.prodMk measurable_snd)
  | n + 1 => Kernel.map ((kap s t n) ⊗ₖ
      ((markovBanditStepKernel P s (t + n)).comap (fun p => happ p.1 p.2) measurable_happ))
      snocF

lemma kap_markov (s : MarkovBanditPolicy k S) (t : ℕ) : ∀ n, IsMarkovKernel (kap P s t n)
  | 0 => by rw [kap]; infer_instance
  | n + 1 => by
      haveI := kap_markov s t n
      rw [kap]
      exact Kernel.IsMarkovKernel.map _ measurable_snocF

lemma kap_apply (s : MarkovBanditPolicy k S) (t : ℕ) (h : MarkovBanditHistory k S t) :
    ∀ n, kap P s t n h = markovBanditMeasure P (cont s h) h.2 n
  | 0 => by
      rw [kap, Kernel.deterministic_apply, markovBanditMeasure]
  | n + 1 => by
      haveI := kap_markov P s t n
      rw [kap, Kernel.map_apply _ measurable_snocF, markovBanditMeasure]
      have hc : ((kap P s t n) ⊗ₖ ((markovBanditStepKernel P s (t + n)).comap
          (fun p => happ p.1 p.2) measurable_happ)) h =
          (markovBanditMeasure P (cont s h) h.2 n).compProd
            (markovBanditStepKernel P (cont s h) n) := by
        ext A hA
        rw [Kernel.compProd_apply hA, Measure.compProd_apply hA, kap_apply s t h n]
        congr 1
        funext b
        rw [Kernel.comap_apply, step_cont]
      rw [hc]
      rfl

lemma happ_zero {t : ℕ} (h : MarkovBanditHistory k S t) :
    happ h ((Fin.elim0 : Fin 0 → (Fin k → S) × Fin k), h.2) = h := by
  refine Prod.ext ?_ rfl
  funext i
  simp [happ, Fin.append_elim0]

/-- Restart lemma R (measure form). -/
lemma restart (s : MarkovBanditPolicy k S) (x : Fin k → S) (t : ℕ) :
    ∀ n, markovBanditMeasure P s x (t + n) =
      ((markovBanditMeasure P s x t).compProd (kap P s t n)).map (fun p => happ p.1 p.2)
  | 0 => by
      haveI := kap_markov P s t 0
      ext A hA
      rw [Measure.map_apply measurable_happ hA, Measure.compProd_apply (measurable_happ hA)]
      simp only [kap, Kernel.deterministic_apply]
      have : ∀ h : MarkovBanditHistory k S t,
          (Measure.dirac ((Fin.elim0 : Fin 0 → (Fin k → S) × Fin k), h.2))
            (Prod.mk h ⁻¹' ((fun p : MarkovBanditHistory k S t × MarkovBanditHistory k S 0 =>
              happ p.1 p.2) ⁻¹' A)) = A.indicator 1 h := by
        intro h
        rw [Measure.dirac_apply' _ (measurable_prodMk_left (measurable_happ hA))]
        have e : ((Fin.elim0 : Fin 0 → (Fin k → S) × Fin k), h.2) ∈ Prod.mk h ⁻¹'
            ((fun p : MarkovBanditHistory k S t × MarkovBanditHistory k S 0 =>
              happ p.1 p.2) ⁻¹' A) ↔ h ∈ A := by
          simp only [Set.mem_preimage]
          rw [happ_zero]
        simp only [Set.indicator, Pi.one_apply]
        by_cases hh : h ∈ A
        · rw [if_pos (e.mpr hh), if_pos hh]
        · rw [if_neg (fun c => hh (e.mp c)), if_neg hh]
      simp_rw [this]
      exact (lintegral_indicator_one (μ := markovBanditMeasure P s x t) hA).symm
  | n + 1 => by
      haveI := kap_markov P s t n
      haveI := kap_markov P s t (n + 1)
      ext A hA
      have hA' : MeasurableSet (snocF (k := k) (S := S) (n := t + n) ⁻¹' A) := measurable_snocF hA
      show (markovBanditMeasure P s x (t + n + 1)) A = _
      rw [markovBanditMeasure, restart s x t n]
      change (Measure.map snocF _) A = _
      rw [Measure.map_apply measurable_snocF hA, Measure.compProd_apply hA',
        Measure.map_apply measurable_happ hA, Measure.compProd_apply (measurable_happ hA)]
      try rw [lintegral_map (Kernel.measurable_kernel_prodMk_left hA') measurable_happ]
      rw [Measure.lintegral_compProd (f := fun a => markovBanditStepKernel P s (t + n)
          (happ a.1 a.2) (Prod.mk (happ a.1 a.2) ⁻¹' (snocF ⁻¹' A)))
          ((Kernel.measurable_kernel_prodMk_left hA').comp measurable_happ)]
      refine lintegral_congr fun h => ?_
      rw [kap, Kernel.map_apply' _ measurable_snocF _ (measurable_prodMk_left (measurable_happ hA)),
        Kernel.compProd_apply (measurable_snocF (measurable_prodMk_left (measurable_happ hA)))]
      refine lintegral_congr fun h' => ?_
      rw [Kernel.comap_apply]
      congr 1
      ext q
      simp only [Set.mem_preimage]
      rw [snocF_happ]

lemma measurable_lastReward {r : S → ℝ} (hr : Measurable r) (m : ℕ) :
    Measurable (fun q : MarkovBanditHistory k S (m + 1) =>
      r ((q.1 (Fin.last m)).1 ((q.1 (Fin.last m)).2))) := by
  have h1 : Measurable (fun q : MarkovBanditHistory k S (m + 1) => q.1 (Fin.last m)) :=
    (measurable_pi_apply _).comp measurable_fst
  have h2 : Measurable (fun p : (Fin k → S) × Fin k => p.1 p.2) :=
    measurable_from_prod_countable_left fun a => measurable_pi_apply a
  exact hr.comp (h2.comp h1)

/-- Restart lemma R (round-reward form). -/
lemma roundReward_restart {r : S → ℝ} (hr : Measurable r) (C : ℝ) (hC : ∀ y, |r y| ≤ C)
    (s : MarkovBanditPolicy k S) (x : Fin k → S) (t n : ℕ) :
    markovBanditRoundReward P r s x (t + n) =
      ∫ h, markovBanditRoundReward P r (cont s h) h.2 n ∂markovBanditMeasure P s x t := by
  haveI := kap_markov P s t (n + 1)
  have hF := measurable_lastReward (k := k) hr (t + n)
  have hR : markovBanditMeasure P s x (t + n + 1) =
      ((markovBanditMeasure P s x t).compProd (kap P s t (n + 1))).map
        (fun p => happ p.1 p.2) := restart P s x t (n + 1)
  unfold markovBanditRoundReward
  rw [hR]
  refine (integral_map (φ := fun p : MarkovBanditHistory k S t × MarkovBanditHistory k S (n + 1) =>
    happ p.1 p.2) measurable_happ.aemeasurable hF.aestronglyMeasurable).trans ?_
  rw [Measure.integral_compProd]
  · refine integral_congr_ae (ae_of_all _ fun h => ?_)
    simp only
    rw [kap_apply]
    refine integral_congr_ae (ae_of_all _ fun h' => ?_)
    simp only [happ]
    rw [show (Fin.last (t + n) : Fin (t + (n + 1))) = Fin.natAdd t (Fin.last n) from rfl,
      Fin.append_right]
  · exact Integrable.of_bound
      (hF.comp (measurable_happ (k := k) (S := S) (t := t) (n := n + 1))).aestronglyMeasurable C
      (ae_of_all _ fun p => by simpa [Real.norm_eq_abs] using hC _)

lemma abs_roundReward_le {r : S → ℝ} (C : ℝ) (hC : ∀ y, |r y| ≤ C)
    (s : MarkovBanditPolicy k S) (x : Fin k → S) (n : ℕ) :
    |markovBanditRoundReward P r s x n| ≤ C := by
  unfold markovBanditRoundReward
  have := norm_integral_le_of_norm_le_const (μ := markovBanditMeasure P s x (n + 1))
    (f := fun h : MarkovBanditHistory k S (n + 1) => r ((h.1 (Fin.last n)).1 ((h.1 (Fin.last n)).2)))
    (C := C) (ae_of_all _ fun h => by simpa [Real.norm_eq_abs] using hC _)
  simpa [Real.norm_eq_abs, probReal_univ] using this

lemma measurable_contReward {r : S → ℝ} (hr : Measurable r) (s : MarkovBanditPolicy k S)
    (t n : ℕ) :
    StronglyMeasurable (fun h : MarkovBanditHistory k S t =>
      markovBanditRoundReward P r (cont s h) h.2 n) := by
  haveI := kap_markov P s t (n + 1)
  have e : (fun h : MarkovBanditHistory k S t => markovBanditRoundReward P r (cont s h) h.2 n) =
      fun h => ∫ q, r ((q.1 (Fin.last n)).1 ((q.1 (Fin.last n)).2)) ∂(kap P s t (n + 1) h) := by
    funext h
    rw [kap_apply]
    rfl
  rw [e]
  exact (measurable_lastReward (k := k) hr n).stronglyMeasurable.integral_kernel

lemma summable_value {r : S → ℝ} (C : ℝ) (hC : ∀ y, |r y| ≤ C) {β : ℝ} (hβ0 : 0 < β)
    (hβ1 : β < 1) (s : MarkovBanditPolicy k S) (x : Fin k → S) :
    Summable (fun n => β ^ n * markovBanditRoundReward P r s x n) := by
  refine Summable.of_norm_bounded (g := fun n => C * β ^ n)
    ((summable_geometric_of_lt_one hβ0.le hβ1).mul_left C) (fun n => ?_)
  rw [Real.norm_eq_abs, abs_mul, abs_of_pos (pow_pos hβ0 n), mul_comm]
  exact mul_le_mul_of_nonneg_right (abs_roundReward_le P C hC s x n) (pow_pos hβ0 n).le

lemma abs_value_le {r : S → ℝ} (C : ℝ) (hC : ∀ y, |r y| ≤ C) {β : ℝ} (hβ0 : 0 < β)
    (hβ1 : β < 1) (s : MarkovBanditPolicy k S) (x : Fin k → S) :
    |markovBanditDiscountedValue P r β s x| ≤ C / (1 - β) := by
  unfold markovBanditDiscountedValue
  have hs := summable_value P C hC hβ0 hβ1 s x
  have hg : Summable (fun n => C * β ^ n) := (summable_geometric_of_lt_one hβ0.le hβ1).mul_left C
  have h1 : ‖∑' n, β ^ n * markovBanditRoundReward P r s x n‖ ≤ ∑' n, C * β ^ n :=
    tsum_of_norm_bounded hg.hasSum (fun n => by
      rw [Real.norm_eq_abs, abs_mul, abs_of_pos (pow_pos hβ0 n), mul_comm]
      exact mul_le_mul_of_nonneg_right (abs_roundReward_le P C hC s x n) (pow_pos hβ0 n).le)
  rw [tsum_mul_left, tsum_geometric_of_lt_one hβ0.le hβ1] at h1
  simpa [Real.norm_eq_abs, div_eq_mul_inv] using h1

lemma aesm_contValue {r : S → ℝ} (hr : Measurable r) (C : ℝ) (hC : ∀ y, |r y| ≤ C) {β : ℝ}
    (hβ0 : 0 < β) (hβ1 : β < 1) (s : MarkovBanditPolicy k S) (t : ℕ)
    (μ : Measure (MarkovBanditHistory k S t)) :
    AEStronglyMeasurable (fun h : MarkovBanditHistory k S t =>
      markovBanditDiscountedValue P r β (cont s h) h.2) μ := by
  refine aestronglyMeasurable_of_tendsto_ae (u := Filter.atTop)
    (f := fun N (h : MarkovBanditHistory k S t) =>
      ∑ n ∈ Finset.range N, β ^ n * markovBanditRoundReward P r (cont s h) h.2 n) ?_ ?_
  · intro N
    refine (Finset.measurable_sum _ fun n _ => ?_).aestronglyMeasurable
    exact (measurable_contReward P hr s t n).measurable.const_mul _
  · exact ae_of_all _ fun h => (summable_value P C hC hβ0 hβ1 (cont s h) h.2).hasSum.tendsto_sum_nat

lemma integrable_contValue {r : S → ℝ} (hr : Measurable r) (C : ℝ) (hC : ∀ y, |r y| ≤ C)
    {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (s : MarkovBanditPolicy k S) (t : ℕ)
    (μ : Measure (MarkovBanditHistory k S t)) [IsFiniteMeasure μ] :
    Integrable (fun h : MarkovBanditHistory k S t =>
      markovBanditDiscountedValue P r β (cont s h) h.2) μ :=
  Integrable.of_bound (aesm_contValue P hr C hC hβ0 hβ1 s t μ) (C / (1 - β))
    (ae_of_all _ fun h => by
      rw [Real.norm_eq_abs]; exact abs_value_le P C hC hβ0 hβ1 (cont s h) h.2)

/-- Restart lemma R (value form). -/
lemma value_restart {r : S → ℝ} (hr : Measurable r) (C : ℝ) (hC : ∀ y, |r y| ≤ C) {β : ℝ}
    (hβ0 : 0 < β) (hβ1 : β < 1) (s : MarkovBanditPolicy k S) (x : Fin k → S) (t : ℕ) :
    markovBanditDiscountedValue P r β s x =
      (∑ n ∈ Finset.range t, β ^ n * markovBanditRoundReward P r s x n) +
        β ^ t * ∫ h, markovBanditDiscountedValue P r β (cont s h) h.2
          ∂markovBanditMeasure P s x t := by
  have hs := summable_value P C hC hβ0 hβ1 s x
  unfold markovBanditDiscountedValue
  rw [← Summable.sum_add_tsum_nat_add t hs]
  congr 1
  have e1 : ∀ i, β ^ (i + t) * markovBanditRoundReward P r s x (i + t) =
      β ^ t * ∫ h, β ^ i * markovBanditRoundReward P r (cont s h) h.2 i
        ∂markovBanditMeasure P s x t := by
    intro i
    rw [add_comm i t, roundReward_restart P hr C hC, integral_const_mul, pow_add]
    ring
  simp_rw [e1]
  rw [tsum_mul_left]
  congr 1
  refine integral_tsum_of_summable_integral_norm (fun i => ?_) ?_
  · refine Integrable.of_bound ((measurable_contReward P hr s t i).const_mul _).aestronglyMeasurable
      (β ^ i * C) (ae_of_all _ fun h => ?_)
    rw [Real.norm_eq_abs, abs_mul, abs_of_pos (pow_pos hβ0 i)]
    exact mul_le_mul_of_nonneg_left (abs_roundReward_le P C hC _ _ i) (pow_pos hβ0 i).le
  · refine Summable.of_nonneg_of_le (fun i => integral_nonneg fun _ => norm_nonneg _)
      (fun i => ?_) ((summable_geometric_of_lt_one hβ0.le hβ1).mul_right C)
    refine (le_abs_self _).trans ?_
    rw [← Real.norm_eq_abs]
    refine (norm_integral_le_of_norm_le_const (μ := markovBanditMeasure P s x t)
      (f := fun h => ‖β ^ i * markovBanditRoundReward P r (cont s h) h.2 i‖) (C := β ^ i * C)
      (ae_of_all _ fun h => ?_)).trans ?_
    · rw [norm_norm, Real.norm_eq_abs, abs_mul, abs_of_pos (pow_pos hβ0 i)]
      exact mul_le_mul_of_nonneg_left (abs_roundReward_le P C hC _ _ i) (pow_pos hβ0 i).le
    · simp [probReal_univ]

lemma stepKernel_congr {s1 s2 : MarkovBanditPolicy k S} {n : ℕ}
    (h : s1.select n = s2.select n) :
    markovBanditStepKernel P s1 n = markovBanditStepKernel P s2 n := by
  unfold markovBanditStepKernel; rw [h]

/-- Policies agreeing before `t` have the same history law up to time `t`. -/
lemma measure_congr {s1 s2 : MarkovBanditPolicy k S} (x : Fin k → S) {t : ℕ}
    (hag : ∀ n, n < t → s1.select n = s2.select n) :
    ∀ m, m ≤ t → markovBanditMeasure P s1 x m = markovBanditMeasure P s2 x m
  | 0, _ => rfl
  | m + 1, hm => by
      rw [markovBanditMeasure, markovBanditMeasure, measure_congr x hag m (by omega),
        stepKernel_congr P (hag m (by omega))]

lemma roundReward_congr {r : S → ℝ} {s1 s2 : MarkovBanditPolicy k S} (x : Fin k → S) {t : ℕ}
    (hag : ∀ n, n < t → s1.select n = s2.select n) (n : ℕ) (hn : n < t) :
    markovBanditRoundReward P r s1 x n = markovBanditRoundReward P r s2 x n := by
  unfold markovBanditRoundReward; rw [measure_congr P x hag (n + 1) hn]

/-- The value gap of two policies agreeing before `t` is the discounted mean continuation gap. -/
lemma value_gap {r : S → ℝ} (hr : Measurable r) (C : ℝ) (hC : ∀ y, |r y| ≤ C) {β : ℝ}
    (hβ0 : 0 < β) (hβ1 : β < 1) {s1 s2 : MarkovBanditPolicy k S} (x : Fin k → S) {t : ℕ}
    (hag : ∀ n, n < t → s1.select n = s2.select n) :
    markovBanditDiscountedValue P r β s1 x - markovBanditDiscountedValue P r β s2 x =
      β ^ t * ∫ h, (markovBanditDiscountedValue P r β (cont s1 h) h.2 -
        markovBanditDiscountedValue P r β (cont s2 h) h.2) ∂markovBanditMeasure P s2 x t := by
  rw [value_restart P hr C hC hβ0 hβ1 s1 x t, value_restart P hr C hC hβ0 hβ1 s2 x t,
    measure_congr P x hag t le_rfl,
    Finset.sum_congr rfl fun n hn => by
      rw [roundReward_congr P x hag n (Finset.mem_range.mp hn)],
    integral_sub (integrable_contValue P hr C hC hβ0 hβ1 s1 t (markovBanditMeasure P s2 x t))
      (integrable_contValue P hr C hC hβ0 hβ1 s2 t (markovBanditMeasure P s2 x t))]
  ring

lemma happ_last {t : ℕ} (h : MarkovBanditHistory k S t) (h' : MarkovBanditHistory k S 1) :
    (happ h h').1 (Fin.last t) = h'.1 (Fin.last 0) := by
  simp only [happ]
  rw [show (Fin.last t : Fin (t + 1)) = Fin.natAdd t (Fin.last 0) from rfl, Fin.append_right]

/-- Restart for a round-`t` expectation of a function of the current states and the played arm. -/
lemma roundExp_restart (F : (Fin k → S) → Fin k → ℝ)
    (hF : Measurable (fun p : (Fin k → S) × Fin k => F p.1 p.2)) (B : ℝ)
    (hB : ∀ y j, |F y j| ≤ B) (s : MarkovBanditPolicy k S) (x : Fin k → S) (t : ℕ) :
    WeberGittins.Suboptimality.roundExpectation P s x t (fun h j => F h.2 j) =
      ∫ h, WeberGittins.Suboptimality.roundExpectation P (cont s h) h.2 0 (fun h0 j => F h0.2 j)
        ∂markovBanditMeasure P s x t := by
  haveI := kap_markov P s t 1
  have hG : ∀ m : ℕ, Measurable (fun q : MarkovBanditHistory k S (m + 1) =>
      F (q.1 (Fin.last m)).1 (q.1 (Fin.last m)).2) :=
    fun m => hF.comp ((measurable_pi_apply _).comp measurable_fst)
  unfold WeberGittins.Suboptimality.roundExpectation
  simp only [truncateMarkovBanditHistory]
  rw [restart P s x t 1]
  refine (integral_map (φ := fun p : MarkovBanditHistory k S t × MarkovBanditHistory k S 1 =>
    happ p.1 p.2) measurable_happ.aemeasurable (hG t).aestronglyMeasurable).trans ?_
  rw [Measure.integral_compProd]
  · refine integral_congr_ae (ae_of_all _ fun h => ?_)
    simp only
    rw [kap_apply]
    refine integral_congr_ae (ae_of_all _ fun h' => ?_)
    simp only [happ_last]
  · exact Integrable.of_bound
      ((hG t).comp (measurable_happ (k := k) (S := S) (t := t) (n := 1))).aestronglyMeasurable B
      (ae_of_all _ fun p => by simpa [Real.norm_eq_abs] using hB _ _)

/-- The continuation of a switch-to-Gittins policy is a Gittins index policy. -/
lemma cont_gittins {r : S → ℝ} {β : ℝ} {π σ : MarkovBanditPolicy k S} {t : ℕ}
    (hσ : WeberGittins.IndexGap.IsSwitchToGittinsAt P r β π t σ)
    (h : MarkovBanditHistory k S t) : IsGittinsIndexPolicy P r β (cont σ h) := by
  intro n h'
  show (σ.select (t + n)).comap (happ h) (measurable_happ_left h) h' _ = 1
  rw [Kernel.comap_apply]
  exact hσ.2 (t + n) (Nat.le_add_right t n) (happ h h')

lemma happ_natAdd {t n : ℕ} (h : MarkovBanditHistory k S t) (h' : MarkovBanditHistory k S n)
    (m : Fin n) : (happ h h').1 (Fin.natAdd t m) = h'.1 m := by
  simp only [happ, Fin.append_right]

lemma runContinues_shift {r : S → ℝ} {β : ℝ} {t n : ℕ} (hn : 0 < n)
    (h : MarkovBanditHistory k S t) (h' : MarkovBanditHistory k S n) :
    WeberGittins.IndexGap.RunContinues P r β t (t + n) (by omega) (happ h h') ↔
      WeberGittins.IndexGap.RunContinues P r β 0 n hn h' := by
  have e0 : (happ h h').1 ⟨t, by omega⟩ = h'.1 ⟨0, hn⟩ := happ_natAdd h h' ⟨0, hn⟩
  unfold WeberGittins.IndexGap.RunContinues
  rw [e0]
  have e2 : (happ h h').2 = h'.2 := rfl
  rw [e2]
  refine and_congr ?_ (and_congr ?_ Iff.rfl)
  · constructor
    · intro H m _
      have := H (Fin.natAdd t m) (by simp)
      rwa [happ_natAdd] at this
    · intro H m hm
      obtain ⟨m', rfl⟩ : ∃ m' : Fin n, m = Fin.natAdd t m' :=
        ⟨⟨m - t, by omega⟩, Fin.ext (by simp; omega)⟩
      rw [happ_natAdd]
      exact H m' (Nat.zero_le _)
  · constructor
    · intro H m hm
      have := H (Fin.natAdd t m) (by simp; omega)
      rwa [happ_natAdd] at this
    · intro H m hm
      obtain ⟨m', rfl⟩ : ∃ m' : Fin n, m = Fin.natAdd t m' :=
        ⟨⟨m - t, by omega⟩, Fin.ext (by simp; omega)⟩
      rw [happ_natAdd]
      exact H m' (by simp at hm; omega)

/-- The continuation of a run-then-Gittins policy is run-then-Gittins from time `0`. -/
lemma cont_runThen {r : S → ℝ} {β : ℝ} {π σ : MarkovBanditPolicy k S} {t : ℕ}
    (hσ : WeberGittins.IndexGap.IsRunThenGittinsAt P r β π t σ)
    (h : MarkovBanditHistory k S t) :
    WeberGittins.IndexGap.IsRunThenGittinsAt P r β (cont σ h) 0 (cont σ h) := by
  refine ⟨fun n _ => rfl, fun n hn h' => ?_⟩
  have key := hσ.2 (t + n) (by omega) (happ h h')
  have e0 : (happ h h').1 ⟨t, by omega⟩ = h'.1 ⟨0, hn⟩ := happ_natAdd h h' ⟨0, hn⟩
  rw [runContinues_shift P hn h h', e0] at key
  have ec : ∀ A, (cont σ h).select n h' A = σ.select (t + n) (happ h h') A := by
    intro A
    show (σ.select (t + n)).comap (happ h) (measurable_happ_left h) h' A = _
    rw [Kernel.comap_apply]
  refine ⟨fun hc => ?_, fun hc => ?_⟩
  · rw [ec]; exact key.1 hc
  · rw [ec]; exact key.2 hc

lemma dss_bounds {r : S → ℝ} (hr0 : ∀ y, 0 ≤ r y) {C : ℝ} (hC : ∀ y, r y ≤ C) {α : ℝ}
    (hα0 : 0 < α) (hα1 : α < 1) (τ : (ℕ → S) → ℕ∞) (ω : ℕ → S) :
    0 ≤ discountedStoppedSum α r τ ω ∧
      discountedStoppedSum α r τ ω ≤ C * discountedStoppedSum α (fun _ => (1 : ℝ)) τ ω := by
  have hC0 : ∀ t : ℕ, (if (t : ℕ∞) < τ ω then α ^ t * r (ω t) else 0) ≤ C * α ^ t := by
    intro t; split_ifs
    · rw [mul_comm C]; exact mul_le_mul_of_nonneg_left (hC _) (pow_pos hα0 t).le
    · exact mul_nonneg ((hr0 (ω 0)).trans (hC _)) (pow_pos hα0 t).le
  have hn : ∀ t : ℕ, 0 ≤ (if (t : ℕ∞) < τ ω then α ^ t * r (ω t) else 0) := by
    intro t; split_ifs
    · exact mul_nonneg (pow_pos hα0 t).le (hr0 _)
    · exact le_rfl
  have hn1 : ∀ t : ℕ, 0 ≤ (if (t : ℕ∞) < τ ω then α ^ t * (fun _ => (1 : ℝ)) (ω t) else 0) := by
    intro t; split_ifs
    · simp only [mul_one]; exact (pow_pos hα0 t).le
    · exact le_rfl
  have hg := summable_geometric_of_lt_one hα0.le hα1
  have hs : Summable (fun t : ℕ => if (t : ℕ∞) < τ ω then α ^ t * r (ω t) else 0) :=
    Summable.of_nonneg_of_le hn hC0 (hg.mul_left C)
  have hs1 : Summable (fun t : ℕ =>
      if (t : ℕ∞) < τ ω then α ^ t * (fun _ => (1 : ℝ)) (ω t) else 0) :=
    Summable.of_nonneg_of_le hn1 (fun t => by
      split_ifs <;> simp [(pow_pos hα0 t).le]) hg
  refine ⟨tsum_nonneg hn, ?_⟩
  unfold discountedStoppedSum
  rw [← tsum_mul_left]
  refine Summable.tsum_le_tsum (fun t => ?_) hs (hs1.mul_left C)
  split_ifs
  · simp only [mul_one]; rw [mul_comm C]; exact mul_le_mul_of_nonneg_left (hC _) (pow_pos hα0 t).le
  · simp

lemma gi_bounds (P : Kernel S S) [IsMarkovKernel P] {r : S → ℝ} (hr0 : ∀ y, 0 ≤ r y) {C : ℝ}
    (hC : ∀ y, r y ≤ C) (hC0 : 0 ≤ C) {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1) (y : S) :
    0 ≤ gittinsIndex P r α y ∧ gittinsIndex P r α y ≤ C := by
  have mem : ∀ g ∈ {g : ℝ | ∃ τ : (ℕ → S) → ℕ∞, IsTrajStoppingTime τ ∧ (∀ ω, 1 ≤ τ ω) ∧
      g = (∫ ω, discountedStoppedSum α r τ ω ∂markovChainMeasure P y) /
        (∫ ω, discountedStoppedSum α (fun _ ↦ 1) τ ω ∂markovChainMeasure P y)}, 0 ≤ g ∧ g ≤ C := by
    rintro _ ⟨τ, -, -, rfl⟩
    have hb := dss_bounds hr0 hC hα0 hα1 τ
    have hnum : 0 ≤ ∫ ω, discountedStoppedSum α r τ ω ∂markovChainMeasure P y :=
      integral_nonneg fun ω => (hb ω).1
    have hden : 0 ≤ ∫ ω, discountedStoppedSum α (fun _ ↦ 1) τ ω ∂markovChainMeasure P y :=
      integral_nonneg fun ω => (dss_bounds (r := fun _ => (1 : ℝ)) (fun _ => zero_le_one)
        (fun _ => le_rfl) hα0 hα1 τ ω).1
    refine ⟨div_nonneg hnum hden, ?_⟩
    by_cases hi : Integrable (fun ω => discountedStoppedSum α (fun _ ↦ 1) τ ω)
        (markovChainMeasure P y)
    · rcases hden.lt_or_eq with hpos | hzero
      · rw [div_le_iff₀ hpos, ← integral_const_mul]
        exact integral_mono_of_nonneg (ae_of_all _ fun ω => (hb ω).1) (hi.const_mul C)
          (ae_of_all _ fun ω => (hb ω).2)
      · rw [← hzero, div_zero]; exact hC0
    · rw [integral_undef hi, div_zero]; exact hC0
  unfold gittinsIndex
  exact ⟨Real.sSup_nonneg fun g hg => (mem g hg).1, Real.sSup_le (fun g hg => (mem g hg).2) hC0⟩

lemma integrable_contRE (F : (Fin k → S) → Fin k → ℝ)
    (hF : Measurable (fun p : (Fin k → S) × Fin k => F p.1 p.2)) (B : ℝ)
    (hB : ∀ y j, |F y j| ≤ B) (s : MarkovBanditPolicy k S) (t : ℕ)
    (μ : Measure (MarkovBanditHistory k S t)) [IsFiniteMeasure μ] :
    Integrable (fun h : MarkovBanditHistory k S t =>
      WeberGittins.Suboptimality.roundExpectation P (cont s h) h.2 0 (fun h0 j => F h0.2 j)) μ := by
  haveI := kap_markov P s t 1
  have hG : Measurable (fun q : MarkovBanditHistory k S (0 + 1) =>
      F (q.1 (Fin.last 0)).1 (q.1 (Fin.last 0)).2) :=
    hF.comp ((measurable_pi_apply _).comp measurable_fst)
  have e : (fun h : MarkovBanditHistory k S t =>
      WeberGittins.Suboptimality.roundExpectation P (cont s h) h.2 0 (fun h0 j => F h0.2 j)) =
      fun h => ∫ q, F (q.1 (Fin.last 0)).1 (q.1 (Fin.last 0)).2 ∂(kap P s t (0 + 1) h) := by
    funext h
    rw [kap_apply]
    rfl
  rw [e]
  refine Integrable.of_bound hG.stronglyMeasurable.integral_kernel.aestronglyMeasurable B
    (ae_of_all _ fun h => ?_)
  refine (norm_integral_le_of_norm_le_const (C := B) (ae_of_all _ fun q => ?_)).trans ?_
  · rw [Real.norm_eq_abs]; exact hB _ _
  · simp

/-- The parent (eq. (8)) from its `t = 0` case C1 by restarting at `t`. -/
theorem parent_of_C1 {S : Type*} [MeasurableSpace S] [StandardBorelSpace S] (P : Kernel S S)
    [IsMarkovKernel P] {r : S → ℝ} (hr : Measurable r)
    (hrb : WeberGittins.Suboptimality.RewardsNonnegBounded r)
    {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hγ : Measurable (gittinsIndex P r β))
    (hC1 : ∀ (σs ρ : MarkovBanditPolicy k S), IsGittinsIndexPolicy P r β σs →
      WeberGittins.IndexGap.IsRunThenGittinsAt P r β ρ 0 ρ → ∀ y : Fin k → S,
      markovBanditDiscountedValue P r β σs y - markovBanditDiscountedValue P r β ρ y ≤
        WeberGittins.Suboptimality.roundExpectation P ρ y 0 (fun h j =>
          ((⨆ i : Fin k, gittinsIndex P r β (h.2 i)) - gittinsIndex P r β (h.2 j)) / (1 - β)))
    (π : MarkovBanditPolicy k S) (t : ℕ) (σstar σ : MarkovBanditPolicy k S)
    (hσstar : WeberGittins.IndexGap.IsSwitchToGittinsAt P r β π t σstar)
    (hσ : WeberGittins.IndexGap.IsRunThenGittinsAt P r β π t σ)
    (x : Fin k → S) :
    markovBanditDiscountedValue P r β σstar x - markovBanditDiscountedValue P r β σ x ≤
      β ^ t * WeberGittins.Suboptimality.roundExpectation P π x t (fun h j =>
        ((⨆ i : Fin k, gittinsIndex P r β (h.2 i)) - gittinsIndex P r β (h.2 j)) / (1 - β)) := by
  obtain ⟨hr0, C, hC⟩ := hrb
  have hCabs : ∀ y, |r y| ≤ max C 0 := fun y => by
    rw [abs_of_nonneg (hr0 y)]; exact (hC y).trans (le_max_left _ _)
  have hgi := fun y => gi_bounds P hr0 (fun y => (hC y).trans (le_max_left C 0))
    (le_max_right C 0) hβ0 hβ1 y
  set F : (Fin k → S) → Fin k → ℝ := fun y j =>
    ((⨆ i : Fin k, gittinsIndex P r β (y i)) - gittinsIndex P r β (y j)) / (1 - β) with hFdef
  have hF : Measurable (fun p : (Fin k → S) × Fin k => F p.1 p.2) := by
    refine measurable_from_prod_countable_left fun j => ?_
    exact ((Measurable.iSup fun i => hγ.comp (measurable_pi_apply i)).sub
      (hγ.comp (measurable_pi_apply j))).div_const _
  have h1β : 0 < 1 - β := by linarith
  have hB : ∀ y j, |F y j| ≤ max C 0 / (1 - β) := by
    intro y j
    have hs0 : 0 ≤ ⨆ i : Fin k, gittinsIndex P r β (y i) := Real.iSup_nonneg fun i => (hgi _).1
    have hs1 : (⨆ i : Fin k, gittinsIndex P r β (y i)) ≤ max C 0 :=
      Real.iSup_le (fun i => (hgi _).2) (le_max_right _ _)
    simp only [hFdef]
    rw [abs_div, abs_of_pos h1β]
    refine div_le_div_of_nonneg_right ?_ h1β.le
    rw [abs_le]
    constructor <;> linarith [(hgi (y j)).1, (hgi (y j)).2]
  have hag1 : ∀ n, n < t → σstar.select n = σ.select n :=
    fun n hn => (hσstar.1 n hn).trans (hσ.1 n hn.le).symm
  rw [value_gap P hr (max C 0) hCabs hβ0 hβ1 x hag1]
  have hRE : WeberGittins.Suboptimality.roundExpectation P π x t (fun h j =>
        ((⨆ i : Fin k, gittinsIndex P r β (h.2 i)) - gittinsIndex P r β (h.2 j)) / (1 - β)) =
      WeberGittins.Suboptimality.roundExpectation P σ x t (fun h j => F h.2 j) := by
    unfold WeberGittins.Suboptimality.roundExpectation
    rw [measure_congr P x (s1 := π) (s2 := σ) (t := t + 1)
      (fun n hn => (hσ.1 n (by omega)).symm) (t + 1) le_rfl]
  rw [hRE, roundExp_restart P F hF _ hB σ x t]
  refine mul_le_mul_of_nonneg_left ?_ (pow_pos hβ0 t).le
  refine integral_mono ((integrable_contValue P hr _ hCabs hβ0 hβ1 σstar t _).sub
    (integrable_contValue P hr _ hCabs hβ0 hβ1 σ t _))
    (integrable_contRE P F hF _ hB σ t _) (fun h => ?_)
  exact hC1 (cont σstar h) (cont σ h) (cont_gittins P hσstar h) (cont_runThen P hσ h) h.2

end DF742747R

open MeasureTheory ProbabilityTheory BanditAlgorithm WeberGittins.IndexGap in
theorem solution {k : ℕ} {S : Type*} [MeasurableSpace S]
    [StandardBorelSpace S] (P : Kernel S S) [IsMarkovKernel P]
    {r : S → ℝ} (hr : Measurable r) (hrb : WeberGittins.Suboptimality.RewardsNonnegBounded r)
    {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hγ : Measurable (gittinsIndex P r β))
    (π : MarkovBanditPolicy k S) (t : ℕ) (σstar σ : MarkovBanditPolicy k S)
    (hσstar : IsSwitchToGittinsAt P r β π t σstar) (hσ : IsRunThenGittinsAt P r β π t σ)
    (x : Fin k → S) :
    markovBanditDiscountedValue P r β σstar x - markovBanditDiscountedValue P r β σ x ≤
      β ^ t * WeberGittins.Suboptimality.roundExpectation P π x t (fun h j =>
        ((⨆ i : Fin k, gittinsIndex P r β (h.2 i)) - gittinsIndex P r β (h.2 j)) / (1 - β)) := by
  exact DF742747R.parent_of_C1 P hr hrb hβ0 hβ1 hγ
    (fun σs ρ hσs hρ y => DFC_C1_main P hr hrb hβ0 hβ1 hγ σs ρ y
      (WeberGittins.Suboptimality.theorem2_suboptimality_bound P hr hrb hβ0 hβ1 σs hσs ρ y) hρ)
    π t σstar σ hσstar hσ x
