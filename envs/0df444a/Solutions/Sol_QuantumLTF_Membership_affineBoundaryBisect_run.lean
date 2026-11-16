-- Prove2me | solution 1 for QuantumLTF.Membership.affineBoundaryBisect_run
-- status  : ACCEPTED   (prove)
-- author  : @stockfish-soup
-- created : 2026-11-15T11:34:00.478892+00:00
-- url     : https://prove2.me/submissions/3375cc2f-5089-4f8a-80ad-24872ae5b152

import Mathlib
import Definitions.Def_QuantumLTF_Membership_affineBoundaryBisect
import Definitions.Def_QuantumLTF_Membership_orientedBisectValue
import Definitions.Def_QuantumLTF_Membership_ltf
import Definitions.Def_QuantumLTF_Membership_height
import Theorems.Thm_QuantumLTF_Membership_ltf_line_eq_height_sign
import Theorems.Thm_QuantumLTF_Membership_sgn_mul_oriented

open QuantumLTF.Membership

theorem solution {n : ℕ}
    (w p x : EuclideanSpace ℝ (Fin n)) (θ : ℝ) (q : ℕ) (lo hi : ℝ)
    (ha : inner ℝ w p ≠ 0) :
    (affineBoundaryBisect p x (sgn (inner ℝ w p)) q lo hi).run (ltf w θ) =
      orientedBisectValue (sgn (inner ℝ w p)) q lo hi (height w θ p x) := by
  let a := inner ℝ w p
  let h := height w θ p x
  induction q generalizing lo hi with
  | zero => rfl
  | succ q ih =>
      let mid := (lo + hi) / 2
      have hquery : ltf w θ (x + mid • p) = sgn (a * (mid - h)) := by
        simpa [a, h] using ltf_line_eq_height_sign w p x θ mid ha
      have horient := sgn_mul_oriented a (mid - h) (by simpa [a] using ha)
      simp only [affineBoundaryBisect, QueryTree.run, orientedBisectValue]
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
