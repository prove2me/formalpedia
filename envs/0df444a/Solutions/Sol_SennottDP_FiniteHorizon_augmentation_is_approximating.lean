-- Prove2me | solution 1 for SennottDP.FiniteHorizon.augmentation_is_approximating
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-03T07:06:55.062333+00:00
-- url     : https://prove2.me/submissions/3e925b30-bd19-4917-92fa-5ffa5eb23236

import Mathlib
import Definitions.Def_SennottDP_FiniteHorizon_MDC
import Definitions.Def_SennottDP_FiniteHorizon_Criterion
import Definitions.Def_SennottDP_FiniteHorizon_ApproxSeq

open scoped ENNReal NNReal Topology
open Filter

open SennottDP.FiniteHorizon in
theorem augApprox694e_SN_tendsto {S : Type} (N₀ : ℕ) (SN : ℕ → Finset S)
    (hSN : MDC.IsStateApprox N₀ SN) (x : S) : ∀ᶠ N in atTop, x ∈ SN N := by
  obtain ⟨N, hN0, hx⟩ := hSN.2.2 x
  filter_upwards [eventually_ge_atTop N] with n hn
  exact hSN.2.1 N n hN0 hn hx

open SennottDP.FiniteHorizon in
theorem augApprox694e_tail {S : Type} (N₀ : ℕ) (SN : ℕ → Finset S)
    (hSN : MDC.IsStateApprox N₀ SN) (f : S → ℝ≥0∞) (hf : ∑' x, f x ≠ ∞) :
    Tendsto (fun N => ∑' r : {r : S // r ∉ SN N}, f r.1) atTop (𝓝 0) := by
  have h1 : Tendsto SN atTop atTop := by
    rw [tendsto_atTop_atTop]
    intro s
    have : ∀ᶠ N in atTop, ∀ x ∈ s, x ∈ SN N :=
      (eventually_all_finset s).2 (fun x _ => augApprox694e_SN_tendsto N₀ SN hSN x)
    obtain ⟨N, hN⟩ := eventually_atTop.1 this
    exact ⟨N, fun n hn x hx => hN n hn x hx⟩
  exact (ENNReal.tendsto_tsum_compl_atTop_zero hf).comp h1

open SennottDP.FiniteHorizon Filter ENNReal Topology in
theorem solution {S Act : Type} [Countable S] (M : MDC S Act)
    (N₀ : ℕ) (SN : ℕ → Finset S) (hSN : MDC.IsStateApprox N₀ SN)
    (q : ℕ → S → Act → S → S → ℝ≥0∞) (hq : M.IsAugmentation N₀ SN q) :
    (∀ N, N₀ ≤ N → ∀ i ∈ SN N, ∀ a ∈ M.A i, ∑ j ∈ SN N, M.augProb SN q N i a j = 1) ∧
    (∀ i, ∀ a ∈ M.A i, ∀ j,
      Tendsto (fun N => M.augProb SN q N i a j) atTop (𝓝 (M.P i a j))) := by
  constructor
  · intro N hN i hi a ha
    simp only [MDC.augProb]
    rw [Finset.sum_add_distrib,
      ← Summable.tsum_finsetSum (fun _ _ => ENNReal.summable)]
    have h2 : ∀ r : {r : S // r ∉ SN N},
        ∑ j ∈ SN N, M.P i a r.1 * q N i a r.1 j = M.P i a r.1 := by
      intro r
      rw [← Finset.mul_sum, hq N hN i hi a ha r.1 r.2, mul_one]
    rw [tsum_congr h2]
    rw [← M.P_sum i a ha]
    exact ENNReal.sum_add_tsum_compl (SN N) (M.P i a)
  · intro i a ha j
    have htail := augApprox694e_tail N₀ SN hSN (M.P i a) (by rw [M.P_sum i a ha]; exact ENNReal.one_ne_top)
    have hup : Tendsto (fun N => M.P i a j + ∑' r : {r : S // r ∉ SN N}, M.P i a r.1)
        atTop (𝓝 (M.P i a j)) := by
      simpa using (tendsto_const_nhds (x := M.P i a j)).add htail
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hup ?_ ?_
    · exact Eventually.of_forall (fun N => by simp only [MDC.augProb]; exact le_self_add)
    · filter_upwards [augApprox694e_SN_tendsto N₀ SN hSN i,
        augApprox694e_SN_tendsto N₀ SN hSN j, eventually_ge_atTop N₀] with N hi hj hN
      simp only [MDC.augProb]
      gcongr with r
      calc M.P i a r.1 * q N i a r.1 j ≤ M.P i a r.1 * 1 := by
            gcongr
            rw [← hq N hN i hi a ha r.1 r.2]
            exact Finset.single_le_sum (f := fun j' => q N i a r.1 j')
              (fun _ _ => by positivity) hj
        _ = M.P i a r.1 := mul_one _

