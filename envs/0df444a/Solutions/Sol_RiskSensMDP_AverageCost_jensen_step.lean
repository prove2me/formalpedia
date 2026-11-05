-- Prove2me | solution 1 for RiskSensMDP.AverageCost.jensen_step
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-05T02:08:34.203662+00:00
-- url     : https://prove2.me/submissions/d4e169b8-6cb3-418d-a3b7-5679cd3b92a8

import Mathlib
import Definitions.Def_RiskSensMDP_AverageCost_Model
import Definitions.Def_RiskSensMDP_AverageCost_HarrisRecurrence
import Definitions.Def_RiskSensMDP_AverageCost_Criterion

open MeasureTheory ProbabilityTheory Filter Finset

namespace Aux_RSMDP5

open RiskSensMDP.AverageCost

variable {E A : Type*} [MeasurableSpace E] [MeasurableSpace A]

lemma stepKernel_compl_D (M : Model E A) (σ : Policy M) (t : ℕ) (h : Π _ : Iic t, E × A) :
    stepKernel M σ t h M.Dᶜ = 0 := by
  have : IsMarkovKernel (M.Q.comap (lastPair (E := E) (A := A) t) (measurable_pi_apply _)) :=
    Kernel.IsMarkovKernel.comap _ _
  unfold stepKernel
  rw [Kernel.compProd_apply M.D_meas.compl]
  refine (lintegral_eq_zero_iff ?_).2 ?_
  · exact Kernel.measurable_kernel_prodMk_left' (M.D_meas.compl) h |>.comp measurable_id
  · refine Filter.Eventually.of_forall (fun b => ?_)
    simp only [Pi.zero_apply]
    rw [Kernel.deterministic_apply' _ _ (measurable_prodMk_left M.D_meas.compl)]
    rw [Set.indicator_apply_eq_zero]
    intro hc
    exact absurd (σ.g_adm (t + 1) (histFin t h, b)) hc

lemma ae_mem_D (M : Model E A) (σ : Policy M) (x : E) (k : ℕ) :
    ∀ᵐ ω ∂(pathMeasure M σ x), ω k ∈ M.D := by
  rw [ae_iff]
  cases k with
  | zero =>
    have hm : Measurable (Preorder.frestrictLe (π := fun _ : ℕ => E × A) 0) := by fun_prop
    have hS : MeasurableSet {y : Π _ : Iic 0, E × A | y ⟨0, by simp⟩ ∉ M.D} :=
      (M.D_meas.preimage (measurable_pi_apply _)).compl
    have : {ω : ℕ → E × A | ¬ ω 0 ∈ M.D} =
        Preorder.frestrictLe 0 ⁻¹' {y : Π _ : Iic 0, E × A | y ⟨0, by simp⟩ ∉ M.D} := rfl
    rw [this, ← Measure.map_apply hm hS]
    unfold pathMeasure Kernel.trajMeasure
    rw [Measure.map_comp _ _ hm, Kernel.traj_map_frestrictLe, Kernel.partialTraj_self,
      Measure.id_comp, Measure.map_dirac' (by fun_prop)]
    rw [Measure.dirac_apply' _ hS]
    simp only [Set.indicator_apply_eq_zero, Pi.one_apply, one_ne_zero, imp_false]
    intro hc
    exact hc (σ.g_adm 0 (fun j => j.elim0, x))
  | succ a =>
    have hm : Measurable (fun ω : ℕ → E × A => (Preorder.frestrictLe a ω, ω (a + 1))) := by
      fun_prop
    have hS : MeasurableSet ((Set.univ : Set (Π _ : Iic a, E × A)) ×ˢ M.Dᶜ) :=
      MeasurableSet.univ.prod M.D_meas.compl
    have : {ω : ℕ → E × A | ¬ ω (a + 1) ∈ M.D} =
        (fun ω : ℕ → E × A => (Preorder.frestrictLe a ω, ω (a + 1))) ⁻¹'
          ((Set.univ : Set (Π _ : Iic a, E × A)) ×ˢ M.Dᶜ) := by
      ext ω; simp
    rw [this, ← Measure.map_apply hm hS]
    unfold pathMeasure
    rw [← Kernel.map_frestrictLe_trajMeasure_compProd_eq_map_trajMeasure,
      Measure.compProd_apply_prod MeasurableSet.univ M.D_meas.compl]
    simp [stepKernel_compl_D]


lemma measurable_cost (M : Model E A) (n : ℕ) : Measurable (cost M n) := by
  unfold cost
  exact Finset.measurable_sum _ (fun k _ => M.c_meas.comp (measurable_pi_apply k))

lemma ae_cost_bounds (M : Model E A) (σ : Policy M) (x : E) (n : ℕ) :
    ∀ᵐ ω ∂(pathMeasure M σ x), (n : ℝ) * M.cl ≤ cost M n ω ∧ cost M n ω ≤ n * M.cu := by
  have h : ∀ᵐ ω ∂(pathMeasure M σ x), ∀ k, ω k ∈ M.D := ae_all_iff.2 (ae_mem_D M σ x)
  filter_upwards [h] with ω hω
  unfold cost
  constructor
  · have := Finset.sum_le_sum (s := Finset.range n) (fun k _ => (M.c_mem _ (hω k)).1)
    simpa [mul_comm] using this
  · have := Finset.sum_le_sum (s := Finset.range n) (fun k _ => (M.c_mem _ (hω k)).2)
    simpa [mul_comm] using this

lemma jensen_n (M : Model E A) (γ : ℝ) (hγ : 1 ≤ γ) (σ : Policy M) (x : E) (n : ℕ) :
    ∫ ω, cost M n ω ∂(pathMeasure M σ x) ≤
      (∫ ω, (cost M n ω) ^ γ ∂(pathMeasure M σ x)) ^ (1 / γ) ∧
    0 ≤ ∫ ω, cost M n ω ∂(pathMeasure M σ x) ∧
    (∫ ω, (cost M n ω) ^ γ ∂(pathMeasure M σ x)) ^ (1 / γ) ≤ n * M.cu := by
  set μ := pathMeasure M σ x
  have : IsProbabilityMeasure μ := by unfold μ pathMeasure; infer_instance
  have hb := ae_cost_bounds M σ x n
  have hcl := M.cl_pos
  have hcu : 0 < M.cu := hcl.trans M.cl_lt_cu
  have hγ0 : 0 < γ := lt_of_lt_of_le one_pos hγ
  have hnn : ∀ᵐ ω ∂μ, 0 ≤ cost M n ω := by
    filter_upwards [hb] with ω hω
    exact le_trans (by positivity) hω.1
  have hm := measurable_cost M n
  have hint : Integrable (cost M n) μ := by
    refine Integrable.of_bound hm.aestronglyMeasurable (n * M.cu) ?_
    filter_upwards [hb] with ω hω
    rw [Real.norm_eq_abs, abs_le]
    constructor
    · nlinarith [hω.1]
    · exact hω.2
  have hintγ : Integrable (fun ω => (cost M n ω) ^ γ) μ := by
    refine Integrable.of_bound (hm.pow_const γ).aestronglyMeasurable ((n * M.cu) ^ γ) ?_
    filter_upwards [hb, hnn] with ω hω h0
    rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg h0 _)]
    exact Real.rpow_le_rpow h0 hω.2 hγ0.le
  have hI0 : 0 ≤ ∫ ω, cost M n ω ∂μ := integral_nonneg_of_ae hnn
  have hIγ0 : 0 ≤ ∫ ω, (cost M n ω) ^ γ ∂μ :=
    integral_nonneg_of_ae (by filter_upwards [hnn] with ω h0; exact Real.rpow_nonneg h0 _)
  refine ⟨?_, hI0, ?_⟩
  · have hJ : (∫ ω, cost M n ω ∂μ) ^ γ ≤ ∫ ω, (cost M n ω) ^ γ ∂μ :=
      (convexOn_rpow hγ).map_integral_le (g := fun y : ℝ => y ^ γ)
        (Real.continuous_rpow_const hγ0.le).continuousOn isClosed_Ici hnn hint hintγ
    calc ∫ ω, cost M n ω ∂μ = ((∫ ω, cost M n ω ∂μ) ^ γ) ^ (1 / γ) := by
          rw [one_div, Real.rpow_rpow_inv hI0 hγ0.ne']
      _ ≤ _ := Real.rpow_le_rpow (Real.rpow_nonneg hI0 _) hJ (by positivity)
  · have hle : ∫ ω, (cost M n ω) ^ γ ∂μ ≤ (n * M.cu) ^ γ := by
      calc ∫ ω, (cost M n ω) ^ γ ∂μ ≤ ∫ _ω, (n * M.cu) ^ γ ∂μ := by
            refine integral_mono_ae hintγ (integrable_const _) ?_
            filter_upwards [hb, hnn] with ω hω h0
            exact Real.rpow_le_rpow h0 hω.2 hγ0.le
        _ = (n * M.cu) ^ γ := by simp
    calc (∫ ω, (cost M n ω) ^ γ ∂μ) ^ (1 / γ) ≤ ((n * M.cu) ^ γ) ^ (1 / γ) :=
          Real.rpow_le_rpow hIγ0 hle (by positivity)
      _ = n * M.cu := by rw [one_div, Real.rpow_rpow_inv (by positivity) hγ0.ne']

end Aux_RSMDP5

open RiskSensMDP.AverageCost in
theorem solution {E A : Type*} [MeasurableSpace E] [StandardBorelSpace E]
    [MeasurableSpace A] [StandardBorelSpace A]
    (M : Model E A) (γ : ℝ) (hγ : 1 ≤ γ) (σ : Policy M) (x : E) :
    riskNeutralAvgCost M σ x ≤ powerAvgCost M γ σ x := by
  unfold riskNeutralAvgCost powerAvgCost
  have hj := Aux_RSMDP5.jensen_n M γ hγ σ x
  apply Filter.limsup_le_limsup
  · exact Filter.Eventually.of_forall (fun n =>
      mul_le_mul_of_nonneg_left (hj n).1 (by positivity))
  · exact Filter.isCoboundedUnder_le_of_le atTop (x := 0) (fun n =>
      mul_nonneg (by positivity) (hj n).2.1)
  · refine Filter.isBoundedUnder_of_eventually_le (a := M.cu) ?_
    filter_upwards [Filter.eventually_ge_atTop 1] with n hn
    have hn' : (0 : ℝ) < n := by exact_mod_cast hn
    calc 1 / (n : ℝ) * (∫ ω, (cost M n ω) ^ γ ∂(pathMeasure M σ x)) ^ (1 / γ)
        ≤ 1 / (n : ℝ) * (n * M.cu) := mul_le_mul_of_nonneg_left (hj n).2.2 (by positivity)
      _ = M.cu := by field_simp
