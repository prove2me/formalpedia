-- Prove2me | solution 1 for QuantumLTF.Membership.height_affine
-- status  : ACCEPTED   (prove)
-- author  : @stockfish-soup
-- created : 2026-11-15T11:18:38.877209+00:00
-- url     : https://prove2.me/submissions/90273341-2c3b-40b8-950a-c5743ac460ea

import Mathlib
import Definitions.Def_QuantumLTF_Membership_height

open QuantumLTF.Membership

theorem solution {n : ℕ}
    (w p x : EuclideanSpace ℝ (Fin n)) (θ : ℝ)
    (ha : inner ℝ w p ≠ 0) :
    height w θ p x = height w θ p 0 - inner ℝ w x / inner ℝ w p := by
  unfold height
  simp only [inner_zero_right, sub_zero]
  field_simp
