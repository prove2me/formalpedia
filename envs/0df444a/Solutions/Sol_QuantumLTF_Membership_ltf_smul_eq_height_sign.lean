-- Prove2me | solution 1 for QuantumLTF.Membership.ltf_smul_eq_height_sign
-- status  : ACCEPTED   (prove)
-- author  : @stockfish-soup
-- created : 2026-11-15T02:49:24.382201+00:00
-- url     : https://prove2.me/submissions/50d62d67-b24d-4aff-be3f-7b45075d5d67

import Mathlib
import Definitions.Def_QuantumLTF_Membership_ltf
import Definitions.Def_QuantumLTF_Membership_height

open QuantumLTF.Membership

theorem solution {n : ℕ} (w p : EuclideanSpace ℝ (Fin n))
    (θ t : ℝ) (ha : inner ℝ w p ≠ 0) :
    ltf w θ (t • p) =
      sgn (inner ℝ w p * (t - height w θ p 0)) := by
  unfold ltf
  congr 1
  simp only [height, inner_zero_right, sub_zero, inner_smul_right]
  field_simp
