-- Prove2me | solution 1 for P2M_FriedCrossing_PureZeros_abs_le_of_vanish___defcde5ba42b
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T04:57:36.589653+00:00
-- url     : https://prove2.me/submissions/1be5d535-6340-4bf5-8390-4b536d664c97

import Definitions.Def_B1s_fried_crossing_firstvariation_9_08
import Definitions.Def_B1s_fried_crossing_purezeros_9_08
import Theorems.Thm_FriedCrossing_Hadamard_entry_slope_eq


set_option autoImplicit true
set_option linter.style.header false
open FriedCrossing
open Filter Topology
open FriedCrossing.PureZeros
open TwinRate
namespace FriedCrossing.PureZeros
theorem _root_.solution {g gθ : ℝ → ℝ → ℝ} {K ε : ℝ} (hε : 0 < ε)
    (h0 : ∀ τ, g 0 τ = 0)
    (hθ : ∀ θ τ, HasDerivAt (fun θ => g θ τ) (gθ θ τ) θ)
    (hK : ∀ θ τ, |θ| < ε → |τ| < ε → |gθ θ τ| ≤ K)
    {θ τ : ℝ} (hθε : |θ| < ε) (hτε : |τ| < ε) : |g θ τ| ≤ K * |θ| := by
  have hK0 : 0 ≤ K :=
    le_trans (abs_nonneg _) (hK 0 0 (by simpa using hε) (by simpa using hε))
  by_cases hθ0 : θ = 0
  · subst hθ0; rw [h0, abs_zero]; positivity
  obtain ⟨η, hη, hslope⟩ := Hadamard.entry_slope_eq (fun t => hθ t τ) hθ0
  rw [h0, sub_zero] at hslope
  have hval : g θ τ = θ * gθ η τ := by rw [← hslope]; field_simp
  rw [hval, abs_mul]
  have hb := hK η τ (lt_trans hη hθε) hτε
  calc |θ| * |gθ η τ| ≤ |θ| * K := by gcongr
    _ = K * |θ| := by ring
end FriedCrossing.PureZeros
