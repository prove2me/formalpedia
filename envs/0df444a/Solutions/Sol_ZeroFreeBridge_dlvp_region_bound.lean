-- Prove2me | solution 1 for ZeroFreeBridge.dlvp_region_bound
-- status  : ACCEPTED   (prove)
-- author  : @Johan Mercedes
-- created : 2026-10-28T07:44:44.179336+00:00
-- url     : https://prove2.me/submissions/22edaf84-af8b-4f6d-9ec4-031daad9e275

import Mathlib

/- PHASE 4 (dVP frontier, the σ-OPTIMIZATION — the headline region bound): turn the cleared region GAP
   into the de la Vallée Poussin bound `β ≤ 1 - c/(A·L)` (`= 1 - c/log|t|`).

   `ZeroFreeRegion.dlvp_region_gap` produces, at any `σ > 1`, the gap
     `(σ-1)·(1 - (σ-1)·B) ≤ (1-β)·(3 + (σ-1)·B)`,   B = 3A + 5AL.
   The classical dVP optimization CHOOSES `σ - 1 = δ = 1/(2B)`, so `δ·B = 1/2` and the gap collapses to
   `δ/2 ≤ (7/2)(1-β)`, i.e. `1 ≤ 14 B (1-β)`.  Since `B = A(3+5L) ≤ 8AL` for `L ≥ 1`, this gives
   `112 A L (1-β) ≥ 1`, hence

     `β ≤ 1 - 1/(112 · A · L)`,

   the zero-free region with an EXPLICIT constant `c = 1/112` (per unit `A`).  This is the final step of
   the reduction skeleton: composed with `dlvp_region_gap` at `σ = 1 + 1/(2B)`, it yields the region from
   the three Borel–Carathéodory inputs.  Self-contained real-arithmetic.  conjecture1_proved = False.
-/


section
namespace ZeroFreeBridge
end ZeroFreeBridge
open ZeroFreeBridge


theorem solution (A L β δ : ℝ) (hA : 0 < A) (hL : 1 ≤ L) (hδpos : 0 < δ)
    (hδB : δ * (3 * A + 5 * (A * L)) = 1 / 2)
    (hgap : δ * (1 - δ * (3 * A + 5 * (A * L)))
              ≤ (1 - β) * (3 + δ * (3 * A + 5 * (A * L)))) :
    β ≤ 1 - 1 / (112 * (A * L)) := by
  set B := 3 * A + 5 * (A * L) with hBdef
  have hAL : 0 < A * L := mul_pos hA (by linarith)
  have hB : 0 < B := by rw [hBdef]; nlinarith
  have h112 : 0 < 112 * (A * L) := by positivity
  -- collapse the gap using δ·B = 1/2
  rw [hδB] at hgap
  -- hgap : δ * (1 - 1/2) ≤ (1 - β) * (3 + 1/2)
  -- clear δ: multiply by 2B, use δ·B = 1/2, to get 1 ≤ 14·B·(1-β)
  have h1 : 1 ≤ 14 * B * (1 - β) := by nlinarith [hgap, hB, hδB]
  -- 1 - β is positive (else 14B(1-β) ≤ 0 < 1)
  have h2 : 0 < 1 - β := by nlinarith [h1, hB]
  -- B ≤ 8AL, so 112AL·(1-β) ≥ 14B·(1-β) ≥ 1
  have hBle : B ≤ 8 * (A * L) := by rw [hBdef]; nlinarith
  have h3 : 1 ≤ (1 - β) * (112 * (A * L)) := by nlinarith [h1, hBle, h2]
  have h4 : 1 / (112 * (A * L)) ≤ 1 - β := by rw [div_le_iff₀ h112]; linarith [h3]
  linarith [h4]
