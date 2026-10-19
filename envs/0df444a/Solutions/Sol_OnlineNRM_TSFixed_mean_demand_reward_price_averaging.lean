-- Prove2me | solution 1 for OnlineNRM.TSFixed.mean_demand_reward_price_averaging
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-17T18:17:42.062042+00:00
-- url     : https://prove2.me/submissions/defeb516-c48b-476e-bd93-dabf620301de

import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Function.ConditionalExpectation.PullOut
import Mathlib.Probability.Kernel.MeasurableIntegral
import Definitions.Def_OnlineNRM_TSFixed_LP
import Definitions.Def_OnlineNRM_TSFixed_Run

open MeasureTheory ProbabilityTheory OnlineNRM.TSFixed
open scoped BigOperators OnlineNRM.TSFixed

theorem solution
    {N M K T : ℕ}
    (p : Fin N → Fin K → ℝ) (a : Fin N → Fin M → ℝ)
    (I : Fin M → ℝ) (dbar : Fin N → ℝ)
    (hp : ∀ i k, 0 ≤ p i k)
    {Θ : Type*} [MeasurableSpace Θ] [StandardBorelSpace Θ]
    (μ₀ : Measure Θ) [IsProbabilityMeasure μ₀]
    (F : Kernel (Θ × Fin K) (Fin N → ℝ)) [IsMarkovKernel F]
    (hF : ∀ ρ k, ∀ᵐ x ∂(F (ρ, k)), ∀ i, x i ∈ Set.Icc 0 (dbar i))
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (θ : Ω → Θ) (θs : ℕ → Ω → Θ)
    (A : ℕ → Ω → Option (Fin K))
    (D Dsat : ℕ → Ω → Fin N → ℝ) (xsel : Θ → Fin K → ℝ)
    (hrun : IsTSFixedRun p a I F μ₀ T P θ θs A D Dsat xsel)
    (t : ℕ) (ht : t < T) :
    (∫ ω, (match A t ω with
      | none => 0
      | some k => ∑ i : Fin N, p i k * meanDemand F (θ ω) i k) ∂P) =
      ∫ ω, lpObj p (meanDemand F (θ ω)) (xsel (θs t ω)) ∂P := by
  classical
  -- Kernel integration gives measurable, uniformly bounded coordinate means.
  have hmean_meas (i : Fin N) (k : Fin K) :
      Measurable (fun ρ : Θ => meanDemand F ρ i k) := by
    have hcoord : Measurable (fun x : Fin N → ℝ => x i) :=
      measurable_pi_apply i
    have hkernel :
        StronglyMeasurable (fun q : Θ × Fin K => ∫ x, x i ∂(F q)) :=
      hcoord.stronglyMeasurable.integral_kernel
    exact hkernel.measurable.comp (measurable_id.prodMk measurable_const)
  have hmean_bound (ρ : Θ) (i : Fin N) (k : Fin K) :
      ‖meanDemand F ρ i k‖ ≤ |dbar i| := by
    have hb : ∀ᵐ x ∂(F (ρ, k)), ‖x i‖ ≤ |dbar i| := by
      filter_upwards [hF ρ k] with x hx
      rw [Real.norm_eq_abs, abs_of_nonneg (hx i).1]
      exact (hx i).2.trans (le_abs_self (dbar i))
    simpa [meanDemand] using
      (norm_integral_le_of_norm_le_const (μ := F (ρ, k)) hb)

  let m : MeasurableSpace Ω :=
    pastSigma θ θs A D t ⊔ MeasurableSpace.comap (θs t) inferInstance
  -- Keep ambient measurability distinct from the conditioning sigma algebra.
  letI : MeasurableSpace Ω := mΩ
  have hm : m ≤ mΩ := by
    dsimp [m, pastSigma]
    refine sup_le (sup_le hrun.measurable_θ.comap_le ?_)
      (hrun.measurable_θs t).comap_le
    refine iSup_le fun s => iSup_le fun _ => ?_
    exact sup_le
      (sup_le (hrun.measurable_θs s).comap_le (hrun.measurable_A s).comap_le)
      (hrun.measurable_D s).comap_le
  have hθm : Measurable[m] θ := by
    apply Measurable.of_comap_le
    change MeasurableSpace.comap θ inferInstance ≤
      (MeasurableSpace.comap θ inferInstance ⊔ _) ⊔ _
    exact le_trans le_sup_left le_sup_left

  let R : Fin K → Ω → ℝ :=
    fun k ω => ∑ i : Fin N, p i k * meanDemand F (θ ω) i k
  let S : Fin K → Set Ω := fun k => A t ⁻¹' {some k}
  let B : Fin K → Ω → ℝ := fun k => (S k).indicator (fun _ => 1)
  have hRm (k : Fin K) : Measurable[m] (R k) := by
    exact Finset.measurable_fun_sum Finset.univ fun i _ =>
      measurable_const.mul ((hmean_meas i k).comp hθm)
  have hRi (k : Fin K) : Integrable (R k) P := by
    refine integrable_finsetSum Finset.univ fun i _ => ?_
    have hi : Integrable (fun ω => meanDemand F (θ ω) i k) P := by
      refine (integrable_const (|dbar i|)).mono'
        (((hmean_meas i k).comp hrun.measurable_θ).aestronglyMeasurable) ?_
      exact Filter.Eventually.of_forall fun ω => hmean_bound (θ ω) i k
    exact hi.const_mul (p i k)
  have hS (k : Fin K) : MeasurableSet (S k) :=
    hrun.measurable_A t (measurableSet_singleton (some k))
  have hBi (k : Fin K) : Integrable (B k) P :=
    (integrable_const (1 : ℝ)).indicator (hS k)
  have hRBi (k : Fin K) : Integrable (R k * B k) P := by
    have heq : R k * B k = (S k).indicator (R k) := by
      funext ω
      by_cases hω : ω ∈ S k <;> simp [B, hω]
    rw [heq]
    exact (hRi k).indicator (hS k)

  -- Pull the true-parameter coefficient through the conditional price law.
  have hCE (k : Fin K) :
      P[R k * B k | m] =ᵐ[P]
        (fun ω => R k ω * xsel (θs t ω) k) := by
    have hpull := condExp_mul_of_stronglyMeasurable_left (m := m)
      (hRm k).stronglyMeasurable (hRBi k) (hBi k)
    have hoff : P[B k | m] =ᵐ[P] (fun ω => xsel (θs t ω) k) :=
      hrun.offer_price t ht k
    filter_upwards [hpull, hoff] with ω hω hprice
    exact hω.trans (congrArg (fun z : ℝ => R k ω * z) hprice)
  have hRxi (k : Fin K) :
      Integrable (fun ω => R k ω * xsel (θs t ω) k) P :=
    (integrable_condExp (μ := P) (m := m) (f := R k * B k)).congr (hCE k)
  have hprice_integral (k : Fin K) :
      (∫ ω, R k ω * B k ω ∂P) =
        ∫ ω, R k ω * xsel (θs t ω) k ∂P := by
    calc
      _ = ∫ ω, (P[R k * B k | m]) ω ∂P :=
        (integral_condExp (μ := P) (m := m) (f := R k * B k) hm).symm
      _ = _ := integral_congr_ae (hCE k)

  -- The option-valued action is the finite sum of its price indicators.
  have hexpand (ω : Ω) :
      (match A t ω with
        | none => 0
        | some k => ∑ i : Fin N, p i k * meanDemand F (θ ω) i k) =
        ∑ k : Fin K, R k ω * B k ω := by
    cases hA : A t ω with
    | none => simp [B, S, hA]
    | some j =>
      change R j ω = ∑ k : Fin K, R k ω * B k ω
      symm
      calc
        _ = R j ω * B j ω := by
          apply Finset.sum_eq_single j
          · intro k _ hkj
            simp [B, S, hA, Ne.symm hkj]
          · intro hj
            exact (hj (Finset.mem_univ j)).elim
        _ = R j ω := by simp [B, S, hA]
  calc
    _ = ∫ ω, ∑ k : Fin K, R k ω * B k ω ∂P :=
      integral_congr_ae (Filter.Eventually.of_forall hexpand)
    _ = ∑ k : Fin K, ∫ ω, R k ω * B k ω ∂P :=
      integral_finsetSum Finset.univ (fun k _ => hRBi k)
    _ = ∑ k : Fin K, ∫ ω, R k ω * xsel (θs t ω) k ∂P :=
      Finset.sum_congr rfl (fun k _ => hprice_integral k)
    _ = ∫ ω, ∑ k : Fin K, R k ω * xsel (θs t ω) k ∂P :=
      (integral_finsetSum Finset.univ (fun k _ => hRxi k)).symm
    _ = _ := rfl
