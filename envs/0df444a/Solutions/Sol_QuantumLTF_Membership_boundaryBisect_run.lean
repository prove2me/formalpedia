-- Prove2me | solution 1 for QuantumLTF.Membership.boundaryBisect_run
-- status  : ACCEPTED   (prove)
-- author  : @stockfish-soup
-- created : 2026-11-15T03:22:49.446186+00:00
-- url     : https://prove2.me/submissions/c3fa43ef-18f5-48a1-8582-8fefe7ed08f3

import Mathlib
import Definitions.Def_QuantumLTF_Membership_boundarySearchTree
import Definitions.Def_QuantumLTF_Membership_orientedBisectValue
import Definitions.Def_QuantumLTF_Membership_ltf
import Definitions.Def_QuantumLTF_Membership_height
import Theorems.Thm_QuantumLTF_Membership_ltf_smul_eq_height_sign
import Theorems.Thm_QuantumLTF_Membership_sgn_mul_oriented

open QuantumLTF.Membership

theorem solution {n : ℕ}
    (w p : EuclideanSpace ℝ (Fin n)) (θ : ℝ) (q : ℕ) (lo hi : ℝ)
    (ha : inner ℝ w p ≠ 0) :
    (boundaryBisect p (sgn (inner ℝ w p)) q lo hi).run (ltf w θ) =
      orientedBisectValue (sgn (inner ℝ w p)) q lo hi (height w θ p 0) := by
  let a := inner ℝ w p
  let h := height w θ p 0
  induction q generalizing lo hi with
  | zero => rfl
  | succ q ih =>
      let mid := (lo + hi) / 2
      have hquery : ltf w θ (mid • p) = sgn (a * (mid - h)) := by
        simpa [a, h] using ltf_smul_eq_height_sign w p θ mid ha
      have horient := sgn_mul_oriented a (mid - h) (by simpa [a] using ha)
      simp only [boundaryBisect, QueryTree.run, orientedBisectValue]
      rw [hquery]
      by_cases hs : sgn a = 1
      · rw [if_pos hs] at horient ⊢
        rw [horient]
        split
        · exact ih lo mid
        · exact ih mid hi
      · rw [if_neg hs] at horient ⊢
        have hneg : -(mid - h) = h - mid := by ring
        rw [hneg] at horient
        rw [horient]
        split
        · exact ih mid hi
        · exact ih lo mid
