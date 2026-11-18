-- Prove2me | solution 1 for OWMR.selected_policy
-- status  : ACCEPTED   (prove)
-- author  : @Ming Hu
-- created : 2026-11-17T20:48:08.11496+00:00
-- url     : https://prove2.me/submissions/fb11b147-1e7d-4b7b-bd8a-a85345b59ea6

import Theorems.Thm_OWMR_general_fifo_guarantee
import Theorems.Thm_OWMR_arbitrary_setup_costs

/-!
Corollary 1 (Selected Policy). With `m = min_i H_i / h`, the FIFO policy is used when
`1 + K_max / K₀ ≤ γ̄_m` and the consolidation policy otherwise; Theorem 1 at
`γ = max(γ_m, 1 + K_max/K₀)` and Theorem 2 give the factor `min(γ̄_m, max(γ_m, 1 + K_max/K₀))`.
The second part is the remark after the corollary for `K₀ = 0`.
-/

open scoped ENNReal
open OWMR

theorem solution {n : ℕ} (hn : 0 < n) (N : Network n) (hN : N.Standing)
    (hA : N.Associated) (hH : ∀ i, N.h ≤ N.H i) (hp : N.h ≤ N.p)
    (m : ℝ) (hm : m = ⨅ i, N.H i / N.h)
    (x : InitState n) (hx : x.Valid) (cF : FIFOChoice n) (hcF : IsFIFOChoice N cF)
    (cC : ConChoice n) (hcC : IsConChoice N m cC) :
    (0 < N.K0 →
      (if 1 + N.Kmax / N.K0 ≤ 13 / 3 + 32 / (57 * m) then fifoPolicy N x cF
        else conPolicy N x cC).avgCost N x
      ≤ ENNReal.ofReal (min (13 / 3 + 32 / (57 * m))
          (max (9 / 4 + 1 / (4 * m)) (1 + N.Kmax / N.K0))) * OPT N x) ∧
    (N.K0 = 0 →
      (if N.Kmax = 0 then fifoPolicy N x cF else conPolicy N x cC).avgCost N x
      ≤ ENNReal.ofReal (if N.Kmax = 0 then 9 / 4 + 1 / (4 * m) else 13 / 3 + 32 / (57 * m))
        * OPT N x) := by
  have hh : 0 < N.h := hN.h_pos
  have : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  -- `m ≥ 1` and `m h ≤ H_i` for every retailer
  have hm1 : 1 ≤ m := by
    rw [hm]
    exact le_ciInf fun i => by rw [le_div_iff₀ hh, one_mul]; exact hH i
  have hmH : ∀ i, m * N.h ≤ N.H i := by
    intro i
    have : m ≤ N.H i / N.h := by rw [hm]; exact ciInf_le (Set.finite_range _).bddBelow i
    rwa [le_div_iff₀ hh] at this
  have hm0 : 0 < m := by linarith
  -- `γ_m ≤ γ̄_m`
  have hγ : 9 / 4 + 1 / (4 * m) ≤ 13 / 3 + 32 / (57 * m) := by
    have : 1 / (4 * m) ≤ 32 / (57 * m) := by
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith
    linarith
  constructor
  · intro hK0
    split_ifs with hsel
    · -- FIFO at `γ = max(γ_m, 1 + K_max/K₀)`, which is at most `γ̄_m`
      set γ := max (9 / 4 + 1 / (4 * m)) (1 + N.Kmax / N.K0) with hγdef
      have hKγ : N.Kmax ≤ (γ - 1) * N.K0 := by
        have h1 : 1 + N.Kmax / N.K0 ≤ γ := le_max_right _ _
        have h2 : N.Kmax / N.K0 ≤ γ - 1 := by linarith
        calc N.Kmax = N.Kmax / N.K0 * N.K0 := by field_simp
          _ ≤ (γ - 1) * N.K0 := mul_le_mul_of_nonneg_right h2 hK0.le
      have hF := general_fifo_guarantee hn N hN m γ hm1 (le_max_left _ _) hmH hp hKγ x hx cF hcF
      rwa [min_eq_right (max_le hγ hsel)]
    · -- consolidation, and `γ̄_m < 1 + K_max/K₀ ≤ max(γ_m, 1 + K_max/K₀)`
      have hC := arbitrary_setup_costs hn N hN hA m hm1 hmH hp x hx cC hcC
      rwa [min_eq_left (le_max_of_le_right (le_of_lt (not_le.1 hsel)))]
  · intro hK0
    split_ifs with hK
    · exact general_fifo_guarantee hn N hN m _ hm1 le_rfl hmH hp (by rw [hK, hK0, mul_zero])
        x hx cF hcF
    · exact arbitrary_setup_costs hn N hN hA m hm1 hmH hp x hx cC hcC
