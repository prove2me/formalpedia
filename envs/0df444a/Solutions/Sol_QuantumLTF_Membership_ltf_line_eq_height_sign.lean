-- Prove2me | solution 1 for QuantumLTF.Membership.ltf_line_eq_height_sign
-- status  : ACCEPTED   (prove)
-- author  : @stockfish-soup
-- created : 2026-11-15T11:30:15.209955+00:00
-- url     : https://prove2.me/submissions/70df8737-caad-4a8a-8386-0c9cf43ab87f

import Mathlib
import Definitions.Def_QuantumLTF_Membership_ltf
import Definitions.Def_QuantumLTF_Membership_height

open QuantumLTF.Membership

theorem solution {n : ℕ}
    (w p x : EuclideanSpace ℝ (Fin n)) (θ t : ℝ)
    (ha : inner ℝ w p ≠ 0) :
    ltf w θ (x + t • p) =
      sgn (inner ℝ w p * (t - height w θ p x)) := by
  unfold ltf height
  congr 1
  simp only [inner_add_right, inner_smul_right]
  field_simp
  ring
