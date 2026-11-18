-- Prove2me | solution 1 for OWMR.dfr_guarantee
-- status  : ACCEPTED   (prove)
-- author  : @Ming Hu
-- created : 2026-11-17T09:57:53.265701+00:00
-- url     : https://prove2.me/submissions/e0eb7cb5-8611-40a2-b048-4e375eeef799

import Definitions.Def_owmr_dfr_policy
import Theorems.Thm_OWMR_dfr_retailer_bound
import Theorems.Thm_OWMR_fifo_upper_gen
import Theorems.Thm_OWMR_fifo_feasible
import Theorems.Thm_OWMR_shared_cost_lower_bound
import Theorems.Thm_OWMR_slValue_mono_setup
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.LinearCombination

/-!
Theorem D.1 (DFR demand): under the conditions of Theorem 1 with `m = 1`, if every retailer with
`Kᵢ > 0` has DFR demand and `Kᵢ ≤ (γ - 1) K₀` for all `i`, then `π_DFR(θ)` with
`θ = 1 - 1/γ` is nonanticipative and feasible, and `C(π_DFR(θ)) ≤ γ OPT`, where
`λ = 2 - √2` and `γ = 1 + λ/2 + √(1 + λ²/4)`.

Assembly: the FIFO physical upper bound with general retailer `(s,S)` choices, the per-retailer
bound `(1 + θλ) Jᵢ(Kᵢ/θ)`, the supplier choice `J₀(K₀ + K_max) ≤ J₀(γK₀)`, the identity
`1 + θλ = γ - 1` (equivalently `γ² - (2 + λ)γ + λ = 0`), `Kᵢ/θ = γKᵢ/(γ - 1)`, and the shared
lower bound of Proposition 1.
-/

open scoped ENNReal
open OWMR

namespace DFRMain

lemma lam_nonneg : 0 ≤ dfrLambda := by
  unfold dfrLambda
  have : Real.sqrt 2 ≤ 2 := by
    rw [Real.sqrt_le_left (by norm_num)]; norm_num
  linarith

lemma gamma_ge_two : 2 ≤ dfrGamma := by
  unfold dfrGamma
  have hl := lam_nonneg
  have : 1 ≤ Real.sqrt (1 + dfrLambda ^ 2 / 4) := by
    rw [Real.one_le_sqrt]; nlinarith
  linarith

lemma gamma_quad : dfrGamma ^ 2 - (2 + dfrLambda) * dfrGamma + dfrLambda = 0 := by
  unfold dfrGamma
  have hu : Real.sqrt (1 + dfrLambda ^ 2 / 4) ^ 2 = 1 + dfrLambda ^ 2 / 4 :=
    Real.sq_sqrt (by positivity)
  linear_combination hu

end DFRMain

open DFRMain in
theorem solution {n : ℕ} (hn : 0 < n) (N : Network n) (hN : N.Standing)
    (hH : ∀ i, N.h ≤ N.H i) (hp : N.h ≤ N.p) (hK : ∀ i, N.K i ≤ (dfrGamma - 1) * N.K0)
    (hD : ∀ i, 0 < N.K i → N.DFRPositive i)
    (x : InitState n) (hx : x.Valid) (c : FIFOChoice n) (hc : IsDFRChoice N (1 - 1 / dfrGamma) c) :
    (fifoPolicy N x c).toPolicy.Nonanticipative ∧ (fifoPolicy N x c).toPolicy.Feasible N x ∧
      (fifoPolicy N x c).avgCost N x ≤ ENNReal.ofReal dfrGamma * OPT N x := by
  have hγ2 := gamma_ge_two
  have hquad := gamma_quad
  have hlam := lam_nonneg
  set γ := dfrGamma with hγdef
  set θ := 1 - 1 / γ with hθdef
  have hγ1 : 1 < γ := by linarith
  have hγ0 : 0 < γ := by linarith
  have hθ0 : 0 < θ := by
    have : 1 / γ < 1 := by rw [div_lt_one hγ0]; linarith
    linarith
  have hθ1 : θ ≤ 1 := by
    have : 0 < 1 / γ := by positivity
    linarith
  have hret := fun i => dfr_retailer_bound N hN θ hθ0 hθ1 c hc i (hH i) hp (hD i)
  have hsS : ∀ i, c.s i ≤ c.S i := fun i => (hret i).1
  have hs0 : c.s0 ≤ c.S0 := hc.2.2.1
  obtain ⟨hna, hfe⟩ := fifo_feasible N hN x hx c hsS hs0
  refine ⟨hna, hfe, ?_⟩
  have hup := fifo_upper_gen hn N hN x hx c hsS hs0
  rw [hc.2.2.2] at hup
  have hcoef : 1 + θ * dfrLambda = γ - 1 := by
    have e : 1 + θ * dfrLambda - (γ - 1)
        = -(γ ^ 2 - (2 + dfrLambda) * γ + dfrLambda) / γ := by
      rw [hθdef]; field_simp; ring
    rw [hquad, neg_zero, zero_div] at e
    linarith
  have hKθ : ∀ i, N.K i / θ = γ * N.K i / (γ - 1) := by
    intro i
    have hγ1' : γ - 1 ≠ 0 := by linarith
    rw [hθdef, div_eq_div_iff (by
      have : 1 / γ < 1 := by rw [div_lt_one hγ0]; linarith
      linarith) hγ1']
    field_simp
  have : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  have hKmax : N.Kmax ≤ (γ - 1) * N.K0 := ciSup_le hK
  have hJ0mono : N.J0 (N.K0 + N.Kmax) ≤ N.J0 (γ * N.K0) :=
    slValue_mono_setup _ _ (by linarith)
  have hlow := shared_cost_lower_bound N hN hH x hx γ hγ1
  calc (fifoPolicy N x c).avgCost N x
      ≤ N.J0 (N.K0 + N.Kmax) + ∑ i, (ssAvgCost (N.marginal i) (N.F i) (N.K i) (c.s i) (c.S i)
          + mirrorAvg (N.marginal i) N.h N.p (c.s i) (c.S i) (c.a i)) := hup
    _ ≤ N.J0 (γ * N.K0) + ∑ i, ENNReal.ofReal (γ - 1) * N.J i (γ * N.K i / (γ - 1)) := by
        refine add_le_add hJ0mono (Finset.sum_le_sum fun i _ => ?_)
        have h := (hret i).2
        rw [hcoef, hKθ i] at h
        exact h
    _ = N.J0 (γ * N.K0) + ENNReal.ofReal (γ - 1) * ∑ i, N.J i (γ * N.K i / (γ - 1)) := by
        rw [Finset.mul_sum]
    _ ≤ ENNReal.ofReal γ * OPT N x := hlow
