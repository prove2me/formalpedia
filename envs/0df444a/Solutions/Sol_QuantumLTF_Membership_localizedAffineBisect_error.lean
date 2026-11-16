-- Prove2me | solution 1 for QuantumLTF.Membership.localizedAffineBisect_error
-- status  : ACCEPTED   (prove)
-- author  : @stockfish-soup
-- created : 2026-11-15T19:05:25.044084+00:00
-- url     : https://prove2.me/submissions/63f93ea6-f5c8-4f7a-8de9-51e85b7bfbef

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Basic
import Definitions.Def_QuantumLTF_Membership_affineBoundaryBisect
import Definitions.Def_QuantumLTF_Membership_ltf
import Definitions.Def_QuantumLTF_Membership_height
import Definitions.Def_QuantumLTF_Membership_rho
import Definitions.Def_QuantumLTF_Membership_gridVec
import Theorems.Thm_QuantumLTF_Membership_height_grid_localization
import Theorems.Thm_QuantumLTF_Membership_affineBoundaryBisect_error

open QAlgorithms
open QuantumLTF.Membership

theorem solution {n b : ℕ}
    (hn : 2 ≤ n) (ε : ℝ) (hε : 0 < ε) (hε2 : ε ≤ 1 / 2)
    (w p : EuclideanSpace ℝ (Fin n)) (θ htil : ℝ)
    (hw : ‖w‖ = 1) (ha : 1 / 10 ≤ |inner ℝ w p|)
    (hhtil : |htil - height w θ p 0| ≤ ε / 100)
    (x : Fin n → Qubits b) (q : ℕ) :
    |(affineBoundaryBisect p (rho n • gridVec n b x) (sgn (inner ℝ w p)) q
        (htil - 1 / 4) (htil + 1 / 4)).run (ltf w θ) -
      height w θ p (rho n • gridVec n b x)| ≤ 1 / (2 : ℝ) ^ (q + 2) := by
  have hloc := height_grid_localization hn ε hε hε2 w p θ htil hw ha hhtil x
  have hloc' : |htil - height w θ p (rho n • gridVec n b x)| ≤ 1 / 4 := by
    simpa [abs_sub_comm] using hloc
  have hbds := abs_le.mp hloc'
  have hane : inner ℝ w p ≠ 0 := by
    intro hz
    rw [hz, abs_zero] at ha
    norm_num at ha
  calc
    |(affineBoundaryBisect p (rho n • gridVec n b x) (sgn (inner ℝ w p)) q
        (htil - 1 / 4) (htil + 1 / 4)).run (ltf w θ) -
      height w θ p (rho n • gridVec n b x)| ≤
        ((htil + 1 / 4) - (htil - 1 / 4)) / (2 : ℝ) ^ (q + 1) :=
      affineBoundaryBisect_error w p (rho n • gridVec n b x) θ q
        (htil - 1 / 4) (htil + 1 / 4) hane (by linarith [hbds.1]) (by linarith [hbds.2])
    _ = 1 / (2 : ℝ) ^ (q + 2) := by
      rw [show q + 2 = (q + 1) + 1 by omega, pow_succ]
      ring
