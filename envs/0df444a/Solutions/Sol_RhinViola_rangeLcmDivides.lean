-- Prove2me | solution 1 for RhinViola.rangeLcmDivides
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-05T22:02:28.939991+00:00
-- url     : https://prove2.me/submissions/c85b8599-1cce-4609-b3e5-6d5e5abf8f3e

import Mathlib.Algebra.GCDMonoid.Finset
import Mathlib.Tactic

theorem solution
    (n r : ℕ) (hr1 : 1 ≤ r) (hrn : r ≤ n) :
    r ∣ (Finset.range n).lcm (fun i : ℕ => i + 1) := by
  have hmem : r - 1 ∈ Finset.range n := by
    simp
    omega
  have h :=
    Finset.dvd_lcm
      (s := Finset.range n) (f := fun i : ℕ => i + 1) hmem
  simpa [Nat.sub_add_cancel hr1] using h
