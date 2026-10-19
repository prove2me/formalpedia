-- Prove2me | solution 1 for OnlineNRM.TSFixed.posterior_matching_entropy_monotone
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-17T18:21:46.555539+00:00
-- url     : https://prove2.me/submissions/262fb5e6-e541-4796-91c8-80c536056847

import Definitions.Def_OnlineNRM_TSFixed_LP
import Definitions.Def_OnlineNRM_TSFixed_Run
import Definitions.Def_OnlineNRM_TSFixed_OracleEntropy
import Theorems.Thm_OnlineNRM_TSFixed_finitePosteriorEntropy_mono

open MeasureTheory ProbabilityTheory OnlineNRM.TSFixed
open scoped BigOperators OnlineNRM.TSFixed

theorem solution
    {N K : ℕ}
    {Θ : Type*} [MeasurableSpace Θ] [StandardBorelSpace Θ]
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (θ : Ω → Θ) (A : ℕ → Ω → Option (Fin K)) (D : ℕ → Ω → Fin N → ℝ)
    (xsel : Θ → Fin K → ℝ) (t : ℕ)
    (hθ : Measurable θ) (hx : Measurable xsel)
    (hx0 : ∀ ρ k, 0 ≤ xsel ρ k)
    (hx1 : ∀ ρ, ∑ k : Fin K, xsel ρ k ≤ 1) :
    0 ≤ finitePosteriorEntropy P (histSigma A D t)
        (fun ω a => oracleActionWeights xsel (θ ω) a) -
      finitePosteriorEntropy P (histSigma A D (t + 1))
        (fun ω a => oracleActionWeights xsel (θ ω) a) := by
  classical
  have hhist : histSigma A D t ≤ histSigma A D (t + 1) := by
    unfold histSigma
    refine iSup_le fun s => iSup_le fun hs => ?_
    exact le_iSup_of_le s (le_iSup_of_le (Nat.lt_succ_of_lt hs) le_rfl)
  apply sub_nonneg.mpr
  exact finitePosteriorEntropy_mono P
    (histSigma A D t) (histSigma A D (t + 1))
    hhist
    (fun ω a => oracleActionWeights xsel (θ ω) a)
    (by
      intro a
      cases a with
      | none =>
          change Measurable (fun ω => 1 - ∑ k : Fin K, xsel (θ ω) k)
          exact measurable_const.sub
            (Finset.measurable_sum Finset.univ fun k _ =>
              (measurable_pi_apply k).comp (hx.comp hθ))
      | some k =>
          exact (measurable_pi_apply k).comp (hx.comp hθ))
    (by
      intro ω a
      cases a with
      | none =>
          simp only [oracleActionWeights]
          exact sub_nonneg.mpr (hx1 (θ ω))
      | some k => exact hx0 (θ ω) k)
    (by
      intro ω
      simp only [Fintype.sum_option, oracleActionWeights]
      exact sub_add_cancel _ _)
