-- Prove2me | solution 1 for OWMR.general_fifo_guarantee
-- status  : ACCEPTED   (prove)
-- author  : @Ming Hu
-- created : 2026-11-16T01:17:49.0052+00:00
-- url     : https://prove2.me/submissions/0a0ede10-928f-43fc-8548-cb655a36b9f5

import Theorems.Thm_OWMR_fifo_physical_upper_bound
import Theorems.Thm_OWMR_shared_cost_lower_bound
import Theorems.Thm_OWMR_fifo_retailer_comparison
import Theorems.Thm_OWMR_slValue_mono_setup
import Theorems.Thm_OWMR_slValue_setup_scale

open MeasureTheory
open scoped ENNReal
open OWMR

theorem solution {n : ℕ} (hn : 0 < n) (N : Network n) (hN : N.Standing)
    (m γ : ℝ) (hm : 1 ≤ m) (hγ : 9 / 4 + 1 / (4 * m) ≤ γ)
    (hH : ∀ i, m * N.h ≤ N.H i) (hp : N.h ≤ N.p) (hK : N.Kmax ≤ (γ - 1) * N.K0)
    (x : InitState n) (hx : x.Valid) (c : FIFOChoice n) (hc : IsFIFOChoice N c) :
    (fifoPolicy N x c).avgCost N x ≤ ENNReal.ofReal γ * OPT N x := by
  have hh : 0 < N.h := hN.h_pos
  have hm0 : 0 < m := by linarith
  have hinv : 0 < 1 / (4 * m) := by positivity
  have hinv' : 1 / (4 * m) ≤ 1 / 4 := by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    linarith
  have hγ1 : 1 < γ := by linarith
  -- `H_i ≥ h`, needed by the shared-cost lower bound
  have hHh : ∀ i, N.h ≤ N.H i := fun i => le_trans (by nlinarith) (hH i)
  -- `F_i ≥ 0`, needed to scale setup costs
  have hF : ∀ i y, 0 ≤ N.F i y := fun i y =>
    integral_nonneg fun z =>
      add_nonneg (mul_nonneg (hN.H_pos i).le (le_max_right _ _))
        (mul_nonneg hN.p_pos.le (le_max_right _ _))
  -- Step 2 of the assembly: align each retailer's bound with setup cost `γ K_i / (γ - 1)`
  have hret : ∀ i, N.augCost i (c.s i) (c.S i)
      ≤ ENNReal.ofReal (γ - 1) * N.J i (γ * N.K i / (γ - 1)) := by
    intro i
    have h1 := fifo_retailer_comparison N hN m hm c hc i (hH i) hp
    have hKi : 0 ≤ N.K i := hN.K_nonneg i
    rcases le_total γ (5 / 2) with hγ52 | hγ52
    · -- `γ ≤ 5/2`: monotonicity in the setup cost
      have hk : 5 * N.K i / 3 ≤ γ * N.K i / (γ - 1) := by
        rw [div_le_div_iff₀ (by norm_num) (by linarith)]
        nlinarith
      have hJ : N.J i (5 * N.K i / 3) ≤ N.J i (γ * N.K i / (γ - 1)) :=
        slValue_mono_setup (N.marginal i) (N.F i) hk
      calc N.augCost i (c.s i) (c.S i)
          ≤ ENNReal.ofReal (5 / 4 + 1 / (4 * m)) * N.J i (5 * N.K i / 3) := h1
        _ ≤ ENNReal.ofReal (γ - 1) * N.J i (γ * N.K i / (γ - 1)) := by
          gcongr
          linarith
    · -- `γ ≥ 5/2`: scale the setup cost by `a = 5(γ-1)/(3γ) ≥ 1`
      have hγ0 : 0 < γ := by linarith
      have ha : 1 ≤ 5 * (γ - 1) / (3 * γ) := by
        rw [le_div_iff₀ (by positivity)]
        linarith
      have heq : 5 * N.K i / 3 = 5 * (γ - 1) / (3 * γ) * (γ * N.K i / (γ - 1)) := by
        have : γ - 1 ≠ 0 := by linarith
        field_simp
      have hJ : N.J i (5 * N.K i / 3)
          ≤ ENNReal.ofReal (5 * (γ - 1) / (3 * γ)) * N.J i (γ * N.K i / (γ - 1)) := by
        rw [heq]
        exact slValue_setup_scale (N.marginal i) (N.F i) (hF i) _ ha
      have hcoef : (5 / 4 + 1 / (4 * m)) * (5 * (γ - 1) / (3 * γ)) ≤ γ - 1 := by
        rw [mul_div_assoc', div_le_iff₀ (by positivity)]
        nlinarith
      calc N.augCost i (c.s i) (c.S i)
          ≤ ENNReal.ofReal (5 / 4 + 1 / (4 * m)) * N.J i (5 * N.K i / 3) := h1
        _ ≤ ENNReal.ofReal (5 / 4 + 1 / (4 * m))
              * (ENNReal.ofReal (5 * (γ - 1) / (3 * γ)) * N.J i (γ * N.K i / (γ - 1))) := by
          gcongr
        _ = ENNReal.ofReal ((5 / 4 + 1 / (4 * m)) * (5 * (γ - 1) / (3 * γ)))
              * N.J i (γ * N.K i / (γ - 1)) := by
          rw [← mul_assoc, ← ENNReal.ofReal_mul (by positivity)]
        _ ≤ ENNReal.ofReal (γ - 1) * N.J i (γ * N.K i / (γ - 1)) := by
          gcongr
  -- Step 3 of the assembly: combine the upper and lower bounds
  have hJ0 : N.J0 (N.K0 + N.Kmax) ≤ N.J0 (γ * N.K0) :=
    slValue_mono_setup N.aggregate N.fL0 (by nlinarith)
  calc (fifoPolicy N x c).avgCost N x
      ≤ N.J0 (N.K0 + N.Kmax) + ∑ i, N.augCost i (c.s i) (c.S i) :=
        fifo_physical_upper_bound hn N hN x hx c hc
    _ ≤ N.J0 (γ * N.K0) + ∑ i, ENNReal.ofReal (γ - 1) * N.J i (γ * N.K i / (γ - 1)) := by
        gcongr with i _
        exact hret i
    _ = N.J0 (γ * N.K0) + ENNReal.ofReal (γ - 1) * ∑ i, N.J i (γ * N.K i / (γ - 1)) := by
        rw [Finset.mul_sum]
    _ ≤ ENNReal.ofReal γ * OPT N x := shared_cost_lower_bound N hN hHh x hx γ hγ1
