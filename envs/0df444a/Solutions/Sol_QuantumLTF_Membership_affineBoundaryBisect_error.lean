-- Prove2me | solution 1 for QuantumLTF.Membership.affineBoundaryBisect_error
-- status  : ACCEPTED   (prove)
-- author  : @stockfish-soup
-- created : 2026-11-15T11:36:38.892198+00:00
-- url     : https://prove2.me/submissions/96b6ecb1-21a8-45f1-a1b7-3e71c80d4b31

import Mathlib
import Definitions.Def_QuantumLTF_Membership_affineBoundaryBisect
import Definitions.Def_QuantumLTF_Membership_ltf
import Definitions.Def_QuantumLTF_Membership_height
import Theorems.Thm_QuantumLTF_Membership_affineBoundaryBisect_run
import Theorems.Thm_QuantumLTF_Membership_orientedBisectValue_error

open QuantumLTF.Membership

theorem solution {n : ℕ}
    (w p x : EuclideanSpace ℝ (Fin n)) (θ : ℝ) (q : ℕ) (lo hi : ℝ)
    (ha : inner ℝ w p ≠ 0)
    (hlo : lo ≤ height w θ p x) (hhi : height w θ p x ≤ hi) :
    |(affineBoundaryBisect p x (sgn (inner ℝ w p)) q lo hi).run (ltf w θ) -
      height w θ p x| ≤ (hi - lo) / (2 : ℝ) ^ (q + 1) := by
  rw [affineBoundaryBisect_run w p x θ q lo hi ha]
  exact orientedBisectValue_error _ _ _ _ _ hlo hhi
