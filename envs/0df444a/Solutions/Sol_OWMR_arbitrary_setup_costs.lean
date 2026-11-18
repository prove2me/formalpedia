-- Prove2me | solution 1 for OWMR.arbitrary_setup_costs
-- status  : ACCEPTED   (prove)
-- author  : @Ming Hu
-- created : 2026-11-16T01:38:23.854489+00:00
-- url     : https://prove2.me/submissions/c5b62ba8-799d-4b17-87ae-f736ad70edc1

import Theorems.Thm_OWMR_consolidation_upper_bound
import Theorems.Thm_OWMR_shared_cost_lower_bound

open MeasureTheory
open scoped ENNReal
open OWMR

theorem solution {n : ℕ} (hn : 0 < n) (N : Network n) (hN : N.Standing)
    (hA : N.Associated) (m : ℝ) (hm : 1 ≤ m) (hH : ∀ i, m * N.h ≤ N.H i) (hp : N.h ≤ N.p)
    (x : InitState n) (hx : x.Valid) (c : ConChoice n) (hc : IsConChoice N m c) :
    (conPolicy N x c).avgCost N x ≤ ENNReal.ofReal (13 / 3 + 32 / (57 * m)) * OPT N x := by
  have hh : 0 < N.h := hN.h_pos
  have hm0 : 0 < m := by linarith
  -- the parameter `g = γ̄ / 2 > 1`
  have hg : conG m = (13 / 3 + 32 / (57 * m)) / 2 := rfl
  have hg1 : 1 < conG m := by
    rw [hg]
    have : (0 : ℝ) < 32 / (57 * m) := by positivity
    linarith
  have hHh : ∀ i, N.h ≤ N.H i := fun i => le_trans (by nlinarith) (hH i)
  -- `ζ K_i = g K_i / (g - 1)` and `B = 2 (g - 1)`
  have hz : ∀ i, conZeta m * N.K i = conG m * N.K i / (conG m - 1) := fun i => by
    unfold conZeta
    rw [div_mul_eq_mul_div]
  have hB : ENNReal.ofReal (conB m) = 2 * ENNReal.ofReal (conG m - 1) := by
    unfold conB
    rw [ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_ofNat]
  have hγ : ENNReal.ofReal (13 / 3 + 32 / (57 * m)) = 2 * ENNReal.ofReal (conG m) := by
    rw [← ENNReal.ofReal_ofNat 2, ← ENNReal.ofReal_mul (by norm_num), hg]
    congr 1
    ring
  have hlow := shared_cost_lower_bound N hN hHh x hx (conG m) hg1
  calc (conPolicy N x c).avgCost N x
      ≤ 2 * N.J0 (conG m * N.K0) + ENNReal.ofReal (conB m) * ∑ i, N.J i (conZeta m * N.K i) :=
        consolidation_upper_bound hn N hN hA m hm hH hp x hx c hc
    _ = 2 * (N.J0 (conG m * N.K0)
          + ENNReal.ofReal (conG m - 1) * ∑ i, N.J i (conG m * N.K i / (conG m - 1))) := by
        simp only [hz, hB]
        rw [mul_add, mul_assoc]
    _ ≤ 2 * (ENNReal.ofReal (conG m) * OPT N x) := by gcongr
    _ = ENNReal.ofReal (13 / 3 + 32 / (57 * m)) * OPT N x := by
        rw [hγ, mul_assoc]
