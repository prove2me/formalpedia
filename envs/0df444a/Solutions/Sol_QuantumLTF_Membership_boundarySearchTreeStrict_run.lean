-- Prove2me | solution 1 for QuantumLTF.Membership.boundarySearchTreeStrict_run
-- status  : ACCEPTED   (prove)
-- author  : @stockfish-soup
-- created : 2026-11-15T03:27:28.087514+00:00
-- url     : https://prove2.me/submissions/1ca9a969-c9a0-46d2-a6b6-17cb1c7f441c

import Mathlib
import Definitions.Def_QuantumLTF_Membership_boundarySearchTreeStrict
import Definitions.Def_QuantumLTF_Membership_orientedBisectValue
import Definitions.Def_QuantumLTF_Membership_ltf
import Definitions.Def_QuantumLTF_Membership_height
import Theorems.Thm_QuantumLTF_Membership_ltf_smul_eq_height_sign
import Theorems.Thm_QuantumLTF_Membership_strict_orientation_sign
import Theorems.Thm_QuantumLTF_Membership_QueryTree_run_map
import Theorems.Thm_QuantumLTF_Membership_boundaryBisect_run

open QuantumLTF.Membership

theorem solution {n : ℕ}
    (w p : EuclideanSpace ℝ (Fin n)) (θ L : ℝ) (q : ℕ)
    (ha : inner ℝ w p ≠ 0)
    (hh : |height w θ p 0| ≤ L) :
    (boundarySearchTreeStrict p L q).run (ltf w θ) =
      (sgn (inner ℝ w p),
       orientedBisectValue (sgn (inner ℝ w p)) q (-L) L (height w θ p 0)) := by
  let a := inner ℝ w p
  let h := height w θ p 0
  have hr : ltf w θ ((L + 1) • p) = sgn (a * ((L + 1) - h)) := by
    simpa [a, h] using ltf_smul_eq_height_sign w p θ (L + 1) ha
  have hl : ltf w θ ((-(L + 1)) • p) = sgn (a * (-(L + 1) - h)) := by
    simpa [a, h] using ltf_smul_eq_height_sign w p θ (-(L + 1)) ha
  have hs := strict_orientation_sign a h L (by simpa [a] using ha) (by simpa [h] using hh)
  simp only [boundarySearchTreeStrict, QueryTree.run]
  rw [hr, hl, hs]
  rw [QueryTree_run_map]
  rw [boundaryBisect_run w p θ q (-L) L ha]
