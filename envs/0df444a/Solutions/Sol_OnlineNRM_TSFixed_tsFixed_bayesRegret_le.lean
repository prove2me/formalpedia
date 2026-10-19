-- Prove2me | solution 1 for OnlineNRM.TSFixed.tsFixed_bayesRegret_le
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-17T14:16:43.529743+00:00
-- url     : https://prove2.me/submissions/cab9c95b-d7b3-4e13-8f5d-f328126523a6
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_OnlineNRM_TSFixed_LP
import Definitions.Def_OnlineNRM_TSFixed_Run
import Theorems.Thm_OnlineNRM_TSFixed_tsFixed_ideal_reward_regret_le
import Theorems.Thm_OnlineNRM_TSFixed_tsFixed_stockout_loss_le

open MeasureTheory ProbabilityTheory OnlineNRM.TSFixed
open scoped BigOperators

theorem solution {N M K T : ℕ} (hK : 2 ≤ K) (hT : 1 ≤ T)
    (p : Fin N → Fin K → ℝ) (a : Fin N → Fin M → ℝ) (I : Fin M → ℝ) (dbar : Fin N → ℝ)
    (hp : ∀ i k, 0 ≤ p i k) (ha : ∀ i j, 0 ≤ a i j) (hI : ∀ j, 0 ≤ I j)
    {Θ : Type*} [MeasurableSpace Θ] [StandardBorelSpace Θ]
    (μ₀ : Measure Θ) [IsProbabilityMeasure μ₀]
    (F : Kernel (Θ × Fin K) (Fin N → ℝ)) [IsMarkovKernel F]
    (hF : ∀ ρ k, ∀ᵐ x ∂(F (ρ, k)), ∀ i, x i ∈ Set.Icc 0 (dbar i))
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (θ : Ω → Θ) (θs : ℕ → Ω → Θ) (A : ℕ → Ω → Option (Fin K))
    (D Dsat : ℕ → Ω → Fin N → ℝ) (xsel : Θ → Fin K → ℝ)
    (hrun : IsTSFixedRun p a I F μ₀ T P θ θs A D Dsat xsel) :
    lpBayesRegret p a I F T P θ A Dsat ≤
      (18 * pmax p dbar + 37 * ∑ i : Fin N, ∑ j : Fin M, pjmax p a j * a i j * dbar i) *
        Real.sqrt ((T : ℝ) * K * Real.log K) := by
  have hIdeal := tsFixed_ideal_reward_regret_le hK hT p a I dbar hp ha hI μ₀ F hF P θ θs A D Dsat xsel hrun
  have hLoss := tsFixed_stockout_loss_le hK hT p a I dbar hp ha hI μ₀ F hF P θ θs A D Dsat xsel hrun
  unfold lpBayesRegret
  linarith