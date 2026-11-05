-- Prove2me | solution 1 for RiskSensMDP.AverageCost.theorem_5_1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-05T02:15:59.586731+00:00
-- url     : https://prove2.me/submissions/1bbba250-258d-4fbb-8d73-437ccdb114ba
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_RiskSensMDP_AverageCost_Model
import Definitions.Def_RiskSensMDP_AverageCost_HarrisRecurrence
import Definitions.Def_RiskSensMDP_AverageCost_Criterion
import Theorems.Thm_RiskSensMDP_AverageCost_harris_slln
import Theorems.Thm_RiskSensMDP_AverageCost_stationary_state_process
import Theorems.Thm_RiskSensMDP_AverageCost_power_rewriting

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


end Aux_RSMDP5

open RiskSensMDP.AverageCost in
theorem solution {E A : Type*} [MeasurableSpace E] [StandardBorelSpace E]
    [MeasurableSpace A] [StandardBorelSpace A]
    (M : Model E A) (f : StationaryRule M)
    (hf : IsPositiveHarrisRecurrent (stateKernel M f)) :
    ∃ ρ : ℝ,
      (∀ γ : ℝ, 0 < γ → ∀ x : E,
        Tendsto (fun n : ℕ => (1 / (n : ℝ)) *
            (∫ ω, (cost M n ω) ^ γ ∂(pathMeasure M f.toPolicy x)) ^ (1 / γ)) atTop (nhds ρ)) ∧
      (∀ x : E,
        Tendsto (fun n : ℕ => (1 / (n : ℝ)) * ∫ ω, cost M n ω ∂(pathMeasure M f.toPolicy x))
          atTop (nhds ρ)) := by
  obtain ⟨μ, hμP, hμ⟩ := hf.2
  set h : E → ℝ := fun y => M.c (y, f.f y) with hh
  have hcl := M.cl_pos
  have hcu : 0 < M.cu := hcl.trans M.cl_lt_cu
  have hhm : Measurable h := M.c_meas.comp (measurable_id.prodMk f.f_meas)
  have hhb : ∀ y, M.cl ≤ h y ∧ h y ≤ M.cu := fun y => M.c_mem _ (f.f_adm y)
  have hhi : Integrable h μ := by
    refine Integrable.of_bound hhm.aestronglyMeasurable M.cu (Eventually.of_forall fun y => ?_)
    rw [Real.norm_eq_abs, abs_of_pos (hcl.trans_le (hhb y).1)]
    exact (hhb y).2
  set ρ := ∫ y, h y ∂μ with hρ
  have hρ0 : 0 ≤ ρ := integral_nonneg (fun y => (hcl.trans_le (hhb y).1).le)
  -- the key a.s. convergence `C^n / n → ρ`
  have key : ∀ x : E, ∀ᵐ ω ∂(pathMeasure M f.toPolicy x),
      Tendsto (fun n : ℕ => cost M n ω / n) atTop (nhds ρ) := by
    intro x
    obtain ⟨hB1, hB2⟩ := stationary_state_process M f x
    have hA := harris_slln (stateKernel M f) hf μ hμ h hhm hhi x
    rw [← hB2] at hA
    have hmeas : Measurable (fun ω : ℕ → E × A => fun n => (ω n).1) :=
      measurable_pi_lambda _ (fun n => measurable_fst.comp (measurable_pi_apply n))
    have hA' := ae_of_ae_map hmeas.aemeasurable hA
    filter_upwards [hA', hB1] with ω h1 h2
    have heq : ∀ n : ℕ, cost M n ω / n = (1 / (n : ℝ)) * ∑ k ∈ Finset.range n, h (ω k).1 := by
      intro n
      unfold cost
      rw [div_eq_inv_mul, one_div]
      congr 1
      refine Finset.sum_congr rfl (fun k _ => ?_)
      simp only [hh]
      rw [← h2 k]
    simp_rw [heq]
    exact h1
  -- uniform bounds on `C^n / n`
  have bnd : ∀ x : E, ∀ n : ℕ, ∀ᵐ ω ∂(pathMeasure M f.toPolicy x),
      0 ≤ cost M n ω / n ∧ cost M n ω / n ≤ M.cu := by
    intro x n
    filter_upwards [Aux_RSMDP5.ae_cost_bounds M f.toPolicy x n] with ω hω
    rcases Nat.eq_zero_or_pos n with hn | hn
    · subst hn; simp [hcu.le]
    · have hn' : (0 : ℝ) < n := by exact_mod_cast hn
      constructor
      · exact div_nonneg (le_trans (by positivity) hω.1) hn'.le
      · rw [div_le_iff₀ hn']; linarith [hω.2]
  refine ⟨ρ, ?_, ?_⟩
  · intro γ hγ x
    have : IsProbabilityMeasure (pathMeasure M f.toPolicy x) := by
      unfold pathMeasure; infer_instance
    have hDCT : Tendsto (fun n : ℕ => ∫ ω, (cost M n ω / n) ^ γ ∂(pathMeasure M f.toPolicy x))
        atTop (nhds (∫ _ω, ρ ^ γ ∂(pathMeasure M f.toPolicy x))) := by
      refine tendsto_integral_of_dominated_convergence (fun _ => M.cu ^ γ) (fun n => ?_)
        (integrable_const _) (fun n => ?_) ?_
      · exact (((Aux_RSMDP5.measurable_cost M n).div_const _).pow_const γ).aestronglyMeasurable
      · filter_upwards [bnd x n] with ω hω
        rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg hω.1 _)]
        exact Real.rpow_le_rpow hω.1 hω.2 hγ.le
      · filter_upwards [key x] with ω hω
        exact ((Real.continuousAt_rpow_const ρ γ (Or.inr hγ.le)).tendsto).comp hω
    rw [integral_const] at hDCT
    simp only [probReal_univ, one_smul] at hDCT
    have hfin := ((Real.continuousAt_rpow_const (ρ ^ γ) (1 / γ)
      (Or.inr (by positivity))).tendsto).comp hDCT
    simp only [Function.comp_def] at hfin
    rw [one_div, Real.rpow_rpow_inv hρ0 hγ.ne'] at hfin
    have hpr := (power_rewriting M γ hγ f.toPolicy x).1
    simp_rw [hpr]
    simpa [one_div] using hfin
  · intro x
    have : IsProbabilityMeasure (pathMeasure M f.toPolicy x) := by
      unfold pathMeasure; infer_instance
    have hDCT : Tendsto (fun n : ℕ => ∫ ω, cost M n ω / n ∂(pathMeasure M f.toPolicy x))
        atTop (nhds (∫ _ω, ρ ∂(pathMeasure M f.toPolicy x))) := by
      refine tendsto_integral_of_dominated_convergence (fun _ => M.cu) (fun n => ?_)
        (integrable_const _) (fun n => ?_) (key x)
      · exact ((Aux_RSMDP5.measurable_cost M n).div_const _).aestronglyMeasurable
      · filter_upwards [bnd x n] with ω hω
        rw [Real.norm_eq_abs, abs_of_nonneg hω.1]
        exact hω.2
    rw [integral_const] at hDCT
    simp only [probReal_univ, one_smul] at hDCT
    refine hDCT.congr (fun n => ?_)
    rw [integral_div]
    ring
