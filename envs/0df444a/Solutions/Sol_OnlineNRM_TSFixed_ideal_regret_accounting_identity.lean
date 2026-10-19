-- Prove2me | solution 1 for OnlineNRM.TSFixed.ideal_regret_accounting_identity
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-17T14:41:20.629057+00:00
-- url     : https://prove2.me/submissions/26f9a322-81a7-4204-9c0b-ea61cbad74fd
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Tactic.Ring
import Definitions.Def_OnlineNRM_TSFixed_LP
import Definitions.Def_OnlineNRM_TSFixed_Run
import Theorems.Thm_OnlineNRM_TSFixed_integrable_meanDemand_lpObj
import Theorems.Thm_OnlineNRM_TSFixed_full_demand_period_mean_replacement
import Theorems.Thm_OnlineNRM_TSFixed_mean_demand_reward_price_averaging

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
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (θ : Ω → Θ) (θs : ℕ → Ω → Θ)
    (A : ℕ → Ω → Option (Fin K))
    (D Dsat : ℕ → Ω → Fin N → ℝ) (xsel : Θ → Fin K → ℝ)
    (hrun : IsTSFixedRun p a I F μ₀ T P θ θs A D Dsat xsel) :
    (∫ ω, lpOpt p a (meanDemand F (θ ω)) (fun j => I j / (T : ℝ)) ∂P) *
        (T : ℝ) - ∫ ω, revenue p A D T ω ∂P =
      ∑ t ∈ Finset.range T,
        ∫ ω, lpObj p (meanDemand F (θ ω)) (xsel (θ ω)) -
          lpObj p (meanDemand F (θ ω)) (xsel (θs t ω)) ∂P := by
  classical
  have hsimplex (ρ : Θ) :
      (∀ k, 0 ≤ xsel ρ k) ∧ ∑ k : Fin K, xsel ρ k ≤ 1 :=
    ⟨(hrun.lp_optimal ρ).1.2.2, (hrun.lp_optimal ρ).1.2.1⟩
  have htrue : Integrable
      (fun ω => lpObj p (meanDemand F (θ ω)) (xsel (θ ω))) P := by
    exact integrable_meanDemand_lpObj p dbar hp F hF P θ hrun.measurable_θ
      (fun ω => xsel (θ ω)) (hrun.measurable_xsel.comp hrun.measurable_θ)
      (Filter.Eventually.of_forall fun ω => hsimplex (θ ω))
  have hsample (t : ℕ) : Integrable
      (fun ω => lpObj p (meanDemand F (θ ω)) (xsel (θs t ω))) P := by
    exact integrable_meanDemand_lpObj p dbar hp F hF P θ hrun.measurable_θ
      (fun ω => xsel (θs t ω))
      (hrun.measurable_xsel.comp (hrun.measurable_θs t))
      (Filter.Eventually.of_forall fun ω => hsimplex (θs t ω))
  have hopt (ρ : Θ) :
      lpOpt p a (meanDemand F ρ) (fun j => I j / (T : ℝ)) =
        lpObj p (meanDemand F ρ) (xsel ρ) := by
    rcases hrun.lp_optimal ρ with ⟨hx, hmax⟩
    unfold lpOpt
    apply le_antisymm
    · apply csSup_le
      · exact ⟨_, ⟨xsel ρ, hx, rfl⟩⟩
      · rintro _ ⟨y, hy, rfl⟩
        exact hmax y hy
    · apply le_csSup
      · refine ⟨lpObj p (meanDemand F ρ) (xsel ρ), ?_⟩
        rintro _ ⟨y, hy, rfl⟩
        exact hmax y hy
      · exact ⟨xsel ρ, hx, rfl⟩
  have hbench :
      (∫ ω, lpOpt p a (meanDemand F (θ ω)) (fun j => I j / (T : ℝ)) ∂P) =
        ∫ ω, lpObj p (meanDemand F (θ ω)) (xsel (θ ω)) ∂P := by
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun ω => hopt (θ ω)
  have hperiod (t : ℕ) (ht : t < T) :
      Integrable (fun ω => ∑ i : Fin N, D t ω i * postedPrice p (A t ω) i) P ∧
        (∫ ω, ∑ i : Fin N, D t ω i * postedPrice p (A t ω) i ∂P) =
          ∫ ω, lpObj p (meanDemand F (θ ω)) (xsel (θs t ω)) ∂P := by
    have hd := full_demand_period_mean_replacement p a I dbar hp μ₀ F hF P θ θs
      A D Dsat xsel hrun t ht
    have ha := mean_demand_reward_price_averaging p a I dbar hp μ₀ F hF P θ θs
      A D Dsat xsel hrun t ht
    exact ⟨hd.1, hd.2.trans ha⟩
  have hrev : (∫ ω, revenue p A D T ω ∂P) =
      ∑ t ∈ Finset.range T,
        ∫ ω, lpObj p (meanDemand F (θ ω)) (xsel (θs t ω)) ∂P := by
    calc
      _ = ∑ t ∈ Finset.range T,
          ∫ ω, ∑ i : Fin N, D t ω i * postedPrice p (A t ω) i ∂P := by
        unfold revenue
        exact integral_finsetSum (Finset.range T)
          (fun t ht => (hperiod t (Finset.mem_range.mp ht)).1)
      _ = _ := by
        apply Finset.sum_congr rfl
        intro t ht
        exact (hperiod t (Finset.mem_range.mp ht)).2
  rw [hbench, hrev]
  symm
  calc
    _ = ∑ t ∈ Finset.range T,
        ((∫ ω, lpObj p (meanDemand F (θ ω)) (xsel (θ ω)) ∂P) -
          ∫ ω, lpObj p (meanDemand F (θ ω)) (xsel (θs t ω)) ∂P) := by
      apply Finset.sum_congr rfl
      intro t ht
      exact integral_sub htrue (hsample t)
    _ = _ := by
      simp only [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range,
        nsmul_eq_mul]
      ring
