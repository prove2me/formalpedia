-- Prove2me | solution 1 for PerishablePricing.Bounds.phi_min_disposal_decomposition
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T03:40:08.484416+00:00
-- url     : https://prove2.me/submissions/84dab592-7eb7-4d27-8e67-d9151d7b171c

import Mathlib
import Definitions.Def_PerishablePricing_Bounds_Myopic

set_option autoImplicit false
open PerishablePricing.Bounds

theorem solution (M : Model) (hM : M.Standing) (L : ℕ) (hL : 1 ≤ L)
    (hback : (1 - M.γ) * M.c ≤ M.hm) (hγ : M.γ < 1) (hθ : M.hp ≤ (1 - M.γ) * M.θ) (n : ℕ)
    (s : Fin L → ℝ) (hs : s ∈ stateSpace L) (sl : ℝ) (hsl : sLast s ≤ sl) (d ε : ℝ) :
    M.phi (M.f n) s sl d (max (d + ε) (sFirst s)) ε =
      M.v sl (d + ε) - M.θt * max (sFirst s - (d + ε)) 0
        + M.γ * M.f n (next s sl (max (d + ε) (sFirst s))) := by
  have h1 : sFirst s ≤ sl := by
    have : sFirst s ≤ sLast s := by
      unfold sFirst sLast
      rw [dif_pos (by omega), dif_pos (by omega)]
      exact hs (Fin.mk_le_mk.2 (by omega))
    linarith
  unfold Model.phi Model.v Model.θt
  rcases le_total (sFirst s) (d + ε) with h | h
  · have hmax : max (d + ε) (sFirst s) = d + ε := max_eq_left h
    have h2 : max (sFirst s - (d + ε)) 0 = 0 := max_eq_right (by linarith)
    rw [hmax, h2]
    ring
  · have hmax : max (d + ε) (sFirst s) = sFirst s := max_eq_right h
    have h2 : max (sFirst s - (d + ε)) 0 = sFirst s - (d + ε) := max_eq_left (by linarith)
    have h3 : max (sl - sFirst s) 0 = sl - sFirst s := max_eq_left (by linarith)
    have h4 : max (sFirst s - sl) 0 = 0 := max_eq_right (by linarith)
    have h5 : max (sl - (d + ε)) 0 = sl - (d + ε) := max_eq_left (by linarith)
    have h6 : max ((d + ε) - sl) 0 = 0 := max_eq_right (by linarith)
    rw [hmax, h2, h3, h4, h5, h6]
    ring
