-- Prove2me | solution 1 for QuantumLTF.Membership.height_rho_grid_affine
-- status  : ACCEPTED   (prove)
-- author  : @stockfish-soup
-- created : 2026-11-15T11:26:31.781928+00:00
-- url     : https://prove2.me/submissions/a07bfe5c-3884-4c0b-999a-3a644764bc46

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Basic
import Definitions.Def_QuantumLTF_Membership_height
import Definitions.Def_QuantumLTF_Membership_rho
import Definitions.Def_QuantumLTF_Membership_gridVec
import Theorems.Thm_QuantumLTF_Membership_height_affine

open QAlgorithms
open QuantumLTF.Membership

theorem solution {n b : ℕ}
    (w p : EuclideanSpace ℝ (Fin n)) (θ : ℝ) (x : Fin n → Qubits b)
    (ha : inner ℝ w p ≠ 0) :
    height w θ p (rho n • gridVec n b x) =
      height w θ p 0 - rho n * inner ℝ w (gridVec n b x) / inner ℝ w p := by
  rw [height_affine w p (rho n • gridVec n b x) θ ha]
  simp only [inner_smul_right]
