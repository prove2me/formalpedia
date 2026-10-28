-- Prove2me | solution 2 for OnlineNRM.TSFixed.full_demand_period_revenue_integrable
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T14:34:39.084979+00:00
-- url     : https://prove2.me/submissions/15b003ae-eb76-4aff-a219-b049e9d1a0b9

import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Definitions.Def_OnlineNRM_TSFixed_LP
import Definitions.Def_OnlineNRM_TSFixed_Run
import Mathlib

open MeasureTheory ProbabilityTheory OnlineNRM.TSFixed
open scoped BigOperators OnlineNRM.TSFixed
namespace S216NRM

theorem key
    {N M K T : ℕ}
    {p : Fin N → Fin K → ℝ} {a : Fin N → Fin M → ℝ}
    {I : Fin M → ℝ}
    {Θ : Type*} [MeasurableSpace Θ]
    {μ₀ : Measure Θ}
    {F : Kernel (Θ × Fin K) (Fin N → ℝ)} [IsMarkovKernel F]
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P]
    {θ : Ω → Θ} {θs : ℕ → Ω → Θ}
    {A : ℕ → Ω → Option (Fin K)}
    {D Dsat : ℕ → Ω → Fin N → ℝ} {xsel : Θ → Fin K → ℝ}
    (hrun : IsTSFixedRun p a I F μ₀ T P θ θs A D Dsat xsel)
    {t : ℕ} (ht : t < T) (k : Fin K) {B : Set (Fin N → ℝ)} (hB : MeasurableSet B) :
    P (A t ⁻¹' {some k} ∩ D t ⁻¹' B) = ∫⁻ ω in A t ⁻¹' {some k}, F (θ ω, k) B ∂P := by
  have hm : pastSigma θ θs A D t ⊔ MeasurableSpace.comap (θs t) inferInstance ⊔
        MeasurableSpace.comap (A t) inferInstance ≤ mΩ := by
    refine sup_le (sup_le ?_ (hrun.measurable_θs t).comap_le) (hrun.measurable_A t).comap_le
    refine sup_le hrun.measurable_θ.comap_le (iSup₂_le fun s _ => ?_)
    exact sup_le (sup_le (hrun.measurable_θs s).comap_le (hrun.measurable_A s).comap_le)
      (hrun.measurable_D s).comap_le
  have hEm : MeasurableSet[pastSigma θ θs A D t ⊔ MeasurableSpace.comap (θs t) inferInstance ⊔
        MeasurableSpace.comap (A t) inferInstance] (A t ⁻¹' {some k}) :=
    le_sup_right (a := pastSigma θ θs A D t ⊔ MeasurableSpace.comap (θs t) inferInstance)
      _ ⟨{some k}, trivial, rfl⟩
  have hE : MeasurableSet (A t ⁻¹' {some k}) := hm _ hEm
  have hS : MeasurableSet (D t ⁻¹' B) := hrun.measurable_D t hB
  have hf : Integrable ((D t ⁻¹' B).indicator (fun _ => (1 : ℝ))) P :=
    (integrable_const (1 : ℝ)).indicator hS
  have h1 := setIntegral_condExp hm hf hEm
  have h2 : ∫ ω in A t ⁻¹' {some k}, (P[(D t ⁻¹' B).indicator (fun _ => (1 : ℝ)) | pastSigma θ θs A D t ⊔
        MeasurableSpace.comap (θs t) inferInstance ⊔ MeasurableSpace.comap (A t) inferInstance]) ω ∂P
      = ∫ ω in A t ⁻¹' {some k}, (F (θ ω, k) B).toReal ∂P := by
    have hd := hrun.demand t ht B hB
    unfold condProb at hd
    rw [integral_congr_ae (ae_restrict_of_ae hd)]
    refine setIntegral_congr_fun hE (fun ω hω => ?_)
    simp only [Set.mem_preimage, Set.mem_singleton_iff] at hω
    simp [hω, demandLaw]
  rw [h2, setIntegral_indicator hS, setIntegral_const, smul_eq_mul, mul_one,
    Measure.real] at h1
  have hmeas : Measurable (fun ω => F (θ ω, k) B) :=
    (F.measurable_coe hB).comp (hrun.measurable_θ.prodMk measurable_const)
  rw [integral_toReal hmeas.aemeasurable (Filter.Eventually.of_forall fun _ => measure_lt_top _ _)]
    at h1
  rw [ENNReal.toReal_eq_toReal_iff'] at h1
  · exact h1.symm
  · exact (lintegral_mono fun ω => prob_le_one).trans_lt (by simp) |>.ne
  · exact measure_ne_top _ _

theorem demand_ae
    {N M K T : ℕ}
    {p : Fin N → Fin K → ℝ} {a : Fin N → Fin M → ℝ}
    {I : Fin M → ℝ} {dbar : Fin N → ℝ}
    {Θ : Type*} [MeasurableSpace Θ]
    {μ₀ : Measure Θ}
    {F : Kernel (Θ × Fin K) (Fin N → ℝ)} [IsMarkovKernel F]
    (hF : ∀ ρ k, ∀ᵐ x ∂(F (ρ, k)), ∀ i, x i ∈ Set.Icc 0 (dbar i))
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P]
    {θ : Ω → Θ} {θs : ℕ → Ω → Θ}
    {A : ℕ → Ω → Option (Fin K)}
    {D Dsat : ℕ → Ω → Fin N → ℝ} {xsel : Θ → Fin K → ℝ}
    (hrun : IsTSFixedRun p a I F μ₀ T P θ θs A D Dsat xsel)
    {t : ℕ} (ht : t < T) :
    ∀ᵐ ω ∂P, A t ω = none ∨ ∀ i, D t ω i ∈ Set.Icc 0 (dbar i) := by
  set G : Set (Fin N → ℝ) := {x | ¬ ∀ i, x i ∈ Set.Icc 0 (dbar i)} with hG
  have hGm : MeasurableSet G := by
    have : G = (⋂ i, (fun x : Fin N → ℝ => x i) ⁻¹' Set.Icc 0 (dbar i))ᶜ := by
      ext x; simp [hG]
    rw [this]
    exact (MeasurableSet.iInter fun i => measurable_pi_apply i measurableSet_Icc).compl
  have hk : ∀ k : Fin K, ∀ᵐ ω ∂P, A t ω = some k → ∀ i, D t ω i ∈ Set.Icc 0 (dbar i) := by
    intro k
    have h0 : P (A t ⁻¹' {some k} ∩ D t ⁻¹' G) = 0 := by
      rw [key hrun ht k hGm]
      have : ∀ ω, F (θ ω, k) G = 0 := fun ω => ae_iff.mp (hF (θ ω) k)
      simp [this]
    filter_upwards [measure_eq_zero_iff_ae_notMem.mp h0] with ω hω hA
    by_contra hc
    exact hω ⟨hA, hc⟩
  filter_upwards [ae_all_iff.mpr hk] with ω hω
  cases h : A t ω with
  | none => exact Or.inl rfl
  | some k => exact Or.inr (hω k h)

theorem revenue_integrable
    {N M K T : ℕ}
    {p : Fin N → Fin K → ℝ} {a : Fin N → Fin M → ℝ}
    {I : Fin M → ℝ} {dbar : Fin N → ℝ}
    {Θ : Type*} [MeasurableSpace Θ]
    {μ₀ : Measure Θ}
    {F : Kernel (Θ × Fin K) (Fin N → ℝ)} [IsMarkovKernel F]
    (hF : ∀ ρ k, ∀ᵐ x ∂(F (ρ, k)), ∀ i, x i ∈ Set.Icc 0 (dbar i))
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P]
    {θ : Ω → Θ} {θs : ℕ → Ω → Θ}
    {A : ℕ → Ω → Option (Fin K)}
    {D Dsat : ℕ → Ω → Fin N → ℝ} {xsel : Θ → Fin K → ℝ}
    (hrun : IsTSFixedRun p a I F μ₀ T P θ θs A D Dsat xsel)
    {t : ℕ} (ht : t < T) :
    Integrable (fun ω => ∑ i : Fin N, D t ω i * postedPrice p (A t ω) i) P := by
  have hpm : ∀ i, Measurable (fun ω => postedPrice p (A t ω) i) := fun i =>
    (measurable_from_top (f := fun o : Option (Fin K) => postedPrice p o i)).comp
      (hrun.measurable_A t)
  refine Integrable.of_bound (C := ∑ i, |dbar i| * ∑ k, |p i k|) ?_ ?_
  · exact (Finset.measurable_sum _ fun i _ =>
      ((measurable_pi_apply i).comp (hrun.measurable_D t)).mul (hpm i)).aestronglyMeasurable
  · filter_upwards [demand_ae hF hrun ht] with ω hω
    rcases hω with h | h
    · simp [h, postedPrice]
      exact Finset.sum_nonneg fun i _ => mul_nonneg (abs_nonneg _)
        (Finset.sum_nonneg fun k _ => abs_nonneg _)
    · cases hA : A t ω with
      | none => simp [postedPrice]
                exact Finset.sum_nonneg fun i _ => mul_nonneg (abs_nonneg _)
                  (Finset.sum_nonneg fun k _ => abs_nonneg _)
      | some k =>
        simp only [postedPrice, Real.norm_eq_abs]
        refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => ?_)
        rw [abs_mul]
        have h1 : |D t ω i| ≤ |dbar i| := by
          have := h i
          rw [abs_of_nonneg this.1, abs_of_nonneg (this.1.trans this.2)]; exact this.2
        have h2 : |p i k| ≤ ∑ k, |p i k| :=
          Finset.single_le_sum (f := fun k => |p i k|) (fun k _ => abs_nonneg _) (Finset.mem_univ k)
        exact mul_le_mul h1 h2 (abs_nonneg _) (abs_nonneg _)

end S216NRM

theorem solution
    {N M K T : ℕ}
    (p : Fin N → Fin K → ℝ) (a : Fin N → Fin M → ℝ)
    (I : Fin M → ℝ) (dbar : Fin N → ℝ)
    (hp : ∀ i k, 0 ≤ p i k)
    {Θ : Type*} [MeasurableSpace Θ] [StandardBorelSpace Θ]
    (μ₀ : Measure Θ) [IsProbabilityMeasure μ₀]
    (F : Kernel (Θ × Fin K) (Fin N → ℝ)) [IsMarkovKernel F]
    (hF : ∀ ρ k, ∀ᵐ x ∂(F (ρ, k)), ∀ i, x i ∈ Set.Icc 0 (dbar i))
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (θ : Ω → Θ) (θs : ℕ → Ω → Θ)
    (A : ℕ → Ω → Option (Fin K))
    (D Dsat : ℕ → Ω → Fin N → ℝ) (xsel : Θ → Fin K → ℝ)
    (hrun : IsTSFixedRun p a I F μ₀ T P θ θs A D Dsat xsel)
    (t : ℕ) (ht : t < T) :
    Integrable (fun ω => ∑ i : Fin N, D t ω i * postedPrice p (A t ω) i) P := by
  exact S216NRM.revenue_integrable hF hrun ht
