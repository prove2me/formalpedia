-- Prove2me | solution 1 for SyncQueues.WaitingTime.theorem_3_2_stability
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-31T14:37:37.058753+00:00
-- url     : https://prove2.me/submissions/292d5b59-9f7a-483d-b25f-39af94f4ca60

import Mathlib
import Definitions.Def_SyncQueues_WaitingTime_BranchingTree
import Definitions.Def_SyncQueues_WaitingTime_Model
import Theorems.Thm_SyncQueues_WaitingTime_eq_6_1
import Theorems.Thm_SyncQueues_WaitingTime_eq_6_3

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal
open SyncQueues.WaitingTime

theorem solution {m : ℕ} (hm : 0 < m) {lam : ℝ} (hlam : 0 < lam)
    (Bm : Measure (Fin m → ℝ)) [IsProbabilityMeasure Bm] (hBm : ∀ᵐ x ∂Bm, ∀ i, 0 ≤ x i)
    {β : ℝ} (hβ : 0 < β)
    (hint : Integrable (fun x => Real.exp (β * x)) (pieceLaw Bm))
    (hstab : (m : ℝ) * (∫ x, Real.exp (β * x) ∂(pieceLaw Bm)) * (lam * m / (lam * m + β)) < 1)
    {n : ℕ} (hn : m ≤ n)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (E : ℕ → Ω → ℝ) (R : ℕ → Ω → (Fin m → ℕ)) (C : ℕ → Ω → (Fin m → ℝ))
    (hsys : IsSyncSystem P m n lam Bm E R C) :
    ∀ᵐ ω ∂P,
      BddAbove (Set.range fun r => Uhat (fun k => E k ω) (fun k => R k ω) (fun k => C k ω) r) ∧
      Tendsto (fun t0 => waitT (fun k => E k ω) (fun k => R k ω) (fun k => C k ω) t0) atBot (𝓝 (Wn (fun k => E k ω) (fun k => R k ω) (fun k => C k ω))) := by
  -- the stability constant `ρ_β` is `< 1`
  have hrho : rho Bm lam β < 1 := by
    unfold rho
    rw [← ofReal_integral_eq_lintegral_ofReal hint
      (Filter.Eventually.of_forall fun x => (Real.exp_pos _).le)]
    have hq : 0 ≤ lam * m / (lam * m + β) := by
      have : 0 < lam * (m : ℝ) := mul_pos hlam (by exact_mod_cast hm)
      positivity
    have hI : 0 ≤ ∫ x, Real.exp (β * x) ∂(pieceLaw Bm) :=
      integral_nonneg fun x => (Real.exp_pos _).le
    rw [show ((m : ℝ≥0∞)) = ENNReal.ofReal (m : ℝ) by simp,
      ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity)]
    exact (ENNReal.ofReal_lt_one).2 hstab
  -- Borel–Cantelli: `Û_r > 0` only finitely often
  have hsum : (∑' r, P {ω | 0 < Uhat (fun k => E k ω) (fun k => R k ω) (fun k => C k ω) r}) ≠ ∞ := by
    refine ne_top_of_le_ne_top ?_ (ENNReal.tsum_le_tsum fun r =>
      ((eq_6_3 hm hlam Bm hBm hn P E R C hsys hβ r).1.trans
        (eq_6_3 hm hlam Bm hBm hn P E R C hsys hβ r).2))
    rw [ENNReal.tsum_geometric]
    exact ENNReal.inv_ne_top.2 (tsub_pos_of_lt hrho).ne'
  have hBC := ae_eventually_notMem hsum
  filter_upwards [hBC, eq_6_1 hm hlam Bm hBm hn P E R C hsys] with ω hω h61
  set U : ℕ → ℝ := fun r => Uhat (fun k => E k ω) (fun k => R k ω) (fun k => C k ω) r with hU
  have hbdd : BddAbove (Set.range U) := by
    obtain ⟨N, hN⟩ := eventually_atTop.1 hω
    refine ⟨∑ r ∈ Finset.range N, |U r|, ?_⟩
    rintro _ ⟨r, rfl⟩
    by_cases hr : r < N
    · exact (le_abs_self _).trans (Finset.single_le_sum (f := fun r => |U r|)
        (fun _ _ => abs_nonneg _) (Finset.mem_range.2 hr))
    · have h := hN r (not_lt.1 hr)
      simp only [Set.mem_setOf_eq, not_lt] at h
      exact h.trans (Finset.sum_nonneg fun _ _ => abs_nonneg _)
  refine ⟨hbdd, ?_⟩
  have hsup : ((Wn (fun k => E k ω) (fun k => R k ω) (fun k => C k ω) : ℝ) : EReal) =
      ⨆ r : ℕ, ((U r : ℝ) : EReal) := by
    unfold Wn
    exact Monotone.map_ciSup_of_continuousAt continuous_coe_real_ereal.continuousAt
      EReal.coe_strictMono.monotone hbdd
  have h2 := h61.2
  rw [← hsup] at h2
  exact EReal.tendsto_coe.1 h2
