-- Prove2me | solution 1 for WeierstrassEllipticZeta.auxiliary_grid_bounded_nonzero_derivative
-- status  : ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-09-08T01:38:29.266128+00:00
-- url     : https://prove2.me/submissions/2384f880-6f20-414c-8bae-556f61db1209

import Theorems.Thm_WeierstrassEllipticZeta_auxiliary_zero_estimate_parameter_bounds
import Theorems.Thm_WeierstrassEllipticZeta_regular_grid_polynomial_zero_estimate
import Mathlib.Tactic.Ring
import Definitions.Def_WeierstrassEllipticZeta_GridJetMatrices
import Definitions.Def_TranscendenceTheory_ComplexAuxiliarySystem

open scoped Polynomial
open Filter WeierstrassEllipticZeta

theorem solution
    (L : PeriodPair) (ω u₁ u₂ : ℂ)
    (h_grid : RegularAuxiliaryGridData L ω u₁ u₂) :
    ∃ K : ℕ, 1 ≤ K ∧ ∀ᶠ N : ℕ in Filter.atTop,
      let m := auxiliaryL0 N
      let l := auxiliaryL N
      ∀ c : Fin (m + 1) × Fin (l + 1) × Fin (l + 1) → ℂ,
        c ≠ 0 → ∃ v ∈ auxiliaryGrid u₁ u₂ ω
          ![3 * auxiliaryS N, 3 * auxiliaryS N, 3 * auxiliaryS3 N],
          ∃ n : ℕ, n ≤ K * m ∧
            iteratedDeriv n (fun w => ∑ i, c i * w ^ i.1.val *
              L.weierstrassP w ^ i.2.1.val * weierstrassZeta L w ^ i.2.2.val)
                (u₁ / 2 + v) ≠ 0 := by
  obtain ⟨C, hC, hzero⟩ := regular_grid_polynomial_zero_estimate L ω u₁ u₂ h_grid
  obtain ⟨k, hk, hparameters⟩ := auxiliary_zero_estimate_parameter_bounds C hC
  refine ⟨k + 6, by omega, ?_⟩
  filter_upwards [hparameters] with N hN
  rcases hN with ⟨hm, hl, hs, hq, hsq, _, hlm, hT, hineq⟩
  dsimp only
  intro c hc
  obtain ⟨v, hv, n, hn, hnonzero⟩ := hzero (auxiliaryL0 N) (auxiliaryL N)
    (auxiliaryS N) (auxiliaryS3 N) (k * auxiliaryL0 N)
    hm hl hs hq hsq hlm hT hineq c hc
  refine ⟨v, hv, n, hn.trans ?_, hnonzero⟩
  calc
    k * auxiliaryL0 N + 6 * auxiliaryL N ≤
        k * auxiliaryL0 N + 6 * auxiliaryL0 N :=
      Nat.add_le_add_left (Nat.mul_le_mul_left 6 hlm) _
    _ = (k + 6) * auxiliaryL0 N := by ring
