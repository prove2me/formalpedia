-- Prove2me | solution 1 for OnlineNRM.TSFixed.full_demand_period_mean_replacement_identity
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-17T18:29:18.193347+00:00
-- url     : https://prove2.me/submissions/ed540520-6dfb-44fe-a7f0-11b85c5e0c0e
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Function.ConditionalExpectation.PullOut
import Definitions.Def_OnlineNRM_TSFixed_LP
import Definitions.Def_OnlineNRM_TSFixed_Run
import Theorems.Thm_MeasureTheory_conditional_mean_of_eventwise_probability_law_ambient

open MeasureTheory ProbabilityTheory OnlineNRM.TSFixed
open scoped BigOperators OnlineNRM.TSFixed MeasureTheory

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
    (∫ ω, ∑ i : Fin N, D t ω i * postedPrice p (A t ω) i ∂P) =
      ∫ ω, (match A t ω with
        | none => 0
        | some k => ∑ i : Fin N, p i k * meanDemand F (θ ω) i k) ∂P := by
  classical
  let ambient : MeasurableSpace Ω := ‹MeasurableSpace Ω›
  let m : MeasurableSpace Ω :=
    pastSigma θ θs A D t ⊔ MeasurableSpace.comap (θs t) inferInstance ⊔
      MeasurableSpace.comap (A t) inferInstance
  -- Keep the ambient instance in force; `m` is only the conditioning sigma algebra.
  letI : MeasurableSpace Ω := ambient
  have hpast : pastSigma θ θs A D t ≤ ambient := by
    unfold pastSigma
    refine sup_le hrun.measurable_θ.comap_le ?_
    refine iSup_le fun s => iSup_le fun _ => ?_
    exact sup_le
      (sup_le (hrun.measurable_θs s).comap_le (hrun.measurable_A s).comap_le)
      (hrun.measurable_D s).comap_le
  have hm : m ≤ ambient :=
    sup_le (sup_le hpast (hrun.measurable_θs t).comap_le)
      (hrun.measurable_A t).comap_le
  have hAm : Measurable[m] (A t) := by
    apply measurable_iff_comap_le.mpr
    exact le_sup_right

  let ν : Ω → Measure (Fin N → ℝ) :=
    fun ω => demandLaw F (θ ω) (A t ω)
  have hν : ∀ ω, IsProbabilityMeasure (ν ω) := by
    intro ω
    dsimp [ν]
    cases A t ω <;> dsimp [demandLaw] <;> infer_instance
  have hLaw : ∀ B : Set (Fin N → ℝ), MeasurableSet B →
      P[(D t ⁻¹' B).indicator (fun _ => (1 : ℝ)) | m] =ᵐ[P]
        fun ω => (ν ω B).toReal := by
    intro B hB
    simpa only [condProb, m, ν] using hrun.demand t ht B hB
  have hbound (i : Fin N) :
      ∀ ω, ∀ᵐ x ∂(ν ω), ‖x i‖ ≤ |dbar i| := by
    intro ω
    dsimp [ν]
    cases A t ω with
    | none =>
        simpa only [demandLaw, ae_dirac_eq, Filter.eventually_pure,
          Pi.zero_apply, norm_zero, abs_zero] using (abs_nonneg (dbar i))
    | some k =>
        change ∀ᵐ x ∂(F (θ ω, k)), ‖x i‖ ≤ |dbar i|
        filter_upwards [hF (θ ω) k] with x hx
        rw [Real.norm_eq_abs, abs_of_nonneg (hx i).1]
        exact (hx i).2.trans (le_abs_self _)
  have hc (i : Fin N) :
      Integrable (fun ω => D t ω i) P ∧
        P[(fun ω => D t ω i) | m] =ᵐ[P]
          fun ω => ∫ x, x i ∂(ν ω) :=
    MeasureTheory.conditional_mean_of_eventwise_probability_law_ambient
      (mΩ := ambient) P m hm (D t) (hrun.measurable_D t) ν hν hLaw
      (fun x => x i) (measurable_pi_apply i) |dbar i| (abs_nonneg _) (hbound i)

  have hw (i : Fin N) :
      Measurable[m] (fun ω => postedPrice p (A t ω) i) :=
    (measurable_of_finite (fun q : Option (Fin K) => postedPrice p q i)).comp hAm
  have hwb (i : Fin N) :
      ∀ᵐ ω ∂P, ‖postedPrice p (A t ω) i‖ ≤ ∑ k : Fin K, |p i k| := by
    apply Filter.Eventually.of_forall
    intro ω
    cases A t ω with
    | none =>
        simp only [postedPrice, norm_zero]
        exact Finset.sum_nonneg fun k _ => abs_nonneg (p i k)
    | some k =>
        simp only [postedPrice, Real.norm_eq_abs]
        exact Finset.single_le_sum (fun k _ => abs_nonneg (p i k)) (Finset.mem_univ k)
  have hleft (i : Fin N) :
      Integrable (fun ω => D t ω i * postedPrice p (A t ω) i) P :=
    (hc i).1.mul_bdd ((hw i).mono hm le_rfl).aestronglyMeasurable (hwb i)
  have hmean (i : Fin N) :
      Integrable (fun ω => ∫ x, x i ∂(ν ω)) P :=
    (integrable_condExp (μ := P) (m := m) (f := fun ω => D t ω i)).congr (hc i).2
  have hright (i : Fin N) :
      Integrable (fun ω => (∫ x, x i ∂(ν ω)) * postedPrice p (A t ω) i) P :=
    (hmean i).mul_bdd ((hw i).mono hm le_rfl).aestronglyMeasurable (hwb i)
  have hcoord (i : Fin N) :
      (∫ ω, D t ω i * postedPrice p (A t ω) i ∂P) =
        ∫ ω, (∫ x, x i ∂(ν ω)) * postedPrice p (A t ω) i ∂P := by
    have hpo :
        P[(fun ω => D t ω i * postedPrice p (A t ω) i) | m] =ᵐ[P]
          fun ω => P[(fun ω => D t ω i) | m] ω * postedPrice p (A t ω) i :=
      condExp_mul_of_stronglyMeasurable_right
        (hw i).stronglyMeasurable (hleft i) (hc i).1
    calc
      (∫ ω, D t ω i * postedPrice p (A t ω) i ∂P) =
          ∫ ω, P[(fun ω => D t ω i * postedPrice p (A t ω) i) | m] ω ∂P :=
        (integral_condExp hm).symm
      _ = ∫ ω, (∫ x, x i ∂(ν ω)) * postedPrice p (A t ω) i ∂P := by
        apply integral_congr_ae
        filter_upwards [hpo, (hc i).2] with ω hω hμ
        rw [hω, hμ]

  calc
    (∫ ω, ∑ i : Fin N, D t ω i * postedPrice p (A t ω) i ∂P) =
        ∑ i : Fin N, ∫ ω, D t ω i * postedPrice p (A t ω) i ∂P :=
      integral_finsetSum Finset.univ (fun i _ => hleft i)
    _ = ∑ i : Fin N, ∫ ω, (∫ x, x i ∂(ν ω)) * postedPrice p (A t ω) i ∂P :=
      Finset.sum_congr rfl (fun i _ => hcoord i)
    _ = ∫ ω, ∑ i : Fin N, (∫ x, x i ∂(ν ω)) * postedPrice p (A t ω) i ∂P :=
      (integral_finsetSum Finset.univ (fun i _ => hright i)).symm
    _ = ∫ ω, (match A t ω with
        | none => 0
        | some k => ∑ i : Fin N, p i k * meanDemand F (θ ω) i k) ∂P := by
      apply integral_congr_ae
      apply Filter.Eventually.of_forall
      intro ω
      dsimp [ν]
      cases A t ω <;> simp [demandLaw, postedPrice, meanDemand, mul_comm]
