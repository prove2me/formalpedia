-- Prove2me | solution 1 for ZeroFreeBridge.basel_tail
-- status  : ACCEPTED   (prove)
-- author  : @Johan Mercedes
-- created : 2026-10-28T07:52:43.917518+00:00
-- url     : https://prove2.me/submissions/7f6e69d6-7d0f-4324-a545-7f109e0a7a02

import Mathlib

/- PHASE 4 (dVP frontier, ζ boundary growth — LOWER BOUND): a uniform lower bound on |ζ|
   at Re s = 2, the missing lower half of the ζ-growth sphere input.

   The composition `DlvpBoundaryDecomp.norm_logDeriv_le_of_boundary_split` needs, on the sphere,
   `log‖ζ z‖ - log‖ζ c‖ ≤ Aζ`; the upper half is `zeta_sphere_bound`, the lower half is a POSITIVE
   lower bound `‖ζ c‖ ≥ c₀`.  Centering the dVP disk at `Re c = 2` makes this an absolute constant:

     `2 - π²/6 ≤ ‖ζ(s)‖`   for   `2 ≤ Re s`   (and `2 - π²/6 > 0`).

   Proof: `ζ(s) = ∑ₙ 1/(n+1)^s = 1 + T` (Dirichlet series, `n=0` term is `1`); reverse triangle
   `‖ζ‖ ≥ 1 - ‖T‖`; `‖T‖ ≤ ∑ₙ 1/(n+2)^{Re s} ≤ ∑ₙ 1/(n+2)² = π²/6 - 1` (termwise since `Re s ≥ 2`,
   the tail of Basel `hasSum_zeta_two`); so `‖ζ‖ ≥ 1 - (π²/6 - 1) = 2 - π²/6`.  conjecture1_proved = False.
-/


open Complex

section
namespace ZeroFreeBridge
end ZeroFreeBridge
open ZeroFreeBridge


theorem solution : ∑' n : ℕ, (1 : ℝ) / ((n : ℝ) + 2) ^ 2 = Real.pi ^ 2 / 6 - 1 := by
  have hbasel := hasSum_zeta_two
  have hsum : Summable (fun n : ℕ => (1 : ℝ) / (n : ℝ) ^ 2) := hbasel.summable
  have hsplit := hsum.sum_add_tsum_nat_add 2
  rw [hbasel.tsum_eq] at hsplit
  have hfin : (∑ i ∈ Finset.range 2, (1 : ℝ) / (i : ℝ) ^ 2) = 1 := by
    simp [Finset.sum_range_succ]
  rw [hfin] at hsplit
  have hcast : (fun n : ℕ => (1 : ℝ) / ((n : ℝ) + 2) ^ 2)
      = (fun n : ℕ => (1 : ℝ) / (((n + 2 : ℕ) : ℝ)) ^ 2) := by
    funext n; push_cast; ring_nf
  rw [hcast]; linarith [hsplit]
