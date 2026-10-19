-- Prove2me | solution 1 for OnlineNRM.TSFixed.tsFixed_ideal_reward_regret_le
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-17T14:29:06.644219+00:00
-- url     : https://prove2.me/submissions/1ded4b27-c4eb-4e7f-af3e-a5a59d7058b7
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_OnlineNRM_TSFixed_LP
import Definitions.Def_OnlineNRM_TSFixed_Run
import Theorems.Thm_OnlineNRM_TSFixed_posterior_matching_oracle_gap_le
import Theorems.Thm_OnlineNRM_TSFixed_ideal_regret_accounting_identity

open MeasureTheory ProbabilityTheory OnlineNRM.TSFixed
open scoped BigOperators OnlineNRM.TSFixed

private theorem option_oracle_entropy_scale_le {K T : ℕ} (hK : 2 ≤ K) :
    Real.sqrt ((T : ℝ) * ((K : ℝ) + 1) * Real.log ((K : ℝ) + 1) / 2) ≤
      18 * Real.sqrt ((T : ℝ) * K * Real.log K) := by
  have hk : (2 : ℝ) ≤ K := by exact_mod_cast hK
  have hkpos : (0 : ℝ) < K := by linarith
  have hkp : (0 : ℝ) < (K : ℝ) + 1 := by linarith
  have ht : (0 : ℝ) ≤ T := Nat.cast_nonneg T
  have hl : 0 ≤ Real.log (K : ℝ) := Real.log_nonneg (by linarith)
  have hlog : Real.log ((K : ℝ) + 1) ≤ 2 * Real.log (K : ℝ) := by
    calc
      Real.log ((K : ℝ) + 1) ≤ Real.log ((K : ℝ) * K) :=
        Real.log_le_log hkp (by nlinarith [sq_nonneg ((K : ℝ) - 1)])
      _ = 2 * Real.log (K : ℝ) := by
        rw [Real.log_mul (ne_of_gt hkpos) (ne_of_gt hkpos)]
        ring
  have hmul1 := mul_le_mul_of_nonneg_left hlog
    (mul_nonneg ht (le_of_lt hkp))
  have hmul2 := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left
      (show (K : ℝ) + 1 ≤ 2 * K by linarith) ht)
    (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hl)
  have hrad :
      (T : ℝ) * ((K : ℝ) + 1) * Real.log ((K : ℝ) + 1) / 2 ≤
        2 * ((T : ℝ) * K * Real.log K) := by
    calc
      _ ≤ (T : ℝ) * (2 * K) * (2 * Real.log (K : ℝ)) / 2 :=
        div_le_div_of_nonneg_right (hmul1.trans hmul2) (by norm_num)
      _ = _ := by ring
  have hbase : 0 ≤ (T : ℝ) * K * Real.log K :=
    mul_nonneg (mul_nonneg ht (le_of_lt hkpos)) hl
  apply Real.sqrt_le_iff.mpr
  constructor
  · positivity
  · rw [mul_pow, Real.sq_sqrt hbase]
    nlinarith

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
    (∫ ω, lpOpt p a (meanDemand F (θ ω)) (fun j => I j / (T : ℝ)) ∂P) * (T : ℝ) -
        ∫ ω, revenue p A D T ω ∂P ≤
      18 * pmax p dbar * Real.sqrt ((T : ℝ) * K * Real.log K) := by
  classical
  obtain ⟨ρ⟩ := MeasureTheory.nonempty_of_isProbabilityMeasure μ₀
  let k0 : Fin K := ⟨0, by omega⟩
  obtain ⟨z, hz⟩ := (hF ρ k0).exists
  have hdbar : ∀ i, 0 ≤ dbar i := fun i => (hz i).1.trans (hz i).2
  have hB : 0 ≤ pmax p dbar := by
    unfold pmax
    split_ifs with h
    · exact (Finset.sum_nonneg
        (fun i _ => mul_nonneg (hp i k0) (hdbar i))).trans
        (Finset.le_sup' (fun k : Fin K => ∑ i : Fin N, p i k * dbar i)
          (Finset.mem_univ k0))
    · exact le_rfl
  have hgap := OnlineNRM.TSFixed.posterior_matching_oracle_gap_le
    (by omega : 1 ≤ K) p dbar hp F hF P θ θs A D xsel
    hrun.measurable_θ hrun.measurable_θs hrun.measurable_A hrun.measurable_D
    hrun.measurable_xsel
    (fun ρ k => (hrun.lp_optimal ρ).1.2.2 k)
    (fun ρ => (hrun.lp_optimal ρ).1.2.1)
    hrun.posterior_sample hrun.offer_price hrun.demand
  rw [OnlineNRM.TSFixed.ideal_regret_accounting_identity
    p a I dbar hp μ₀ F hF P θ θs A D Dsat xsel hrun]
  calc
    _ ≤ pmax p dbar *
        Real.sqrt ((T : ℝ) * ((K : ℝ) + 1) * Real.log ((K : ℝ) + 1) / 2) := hgap
    _ ≤ pmax p dbar * (18 * Real.sqrt ((T : ℝ) * K * Real.log K)) :=
      mul_le_mul_of_nonneg_left (option_oracle_entropy_scale_le (T := T) hK) hB
    _ = _ := by ring
