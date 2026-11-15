-- Prove2me | solution 1 for QuantumLTF.Membership.centered_product_expand
-- status  : ACCEPTED   (prove)
-- author  : @stockfish-soup
-- created : 2026-11-14T21:35:03.77625+00:00
-- url     : https://prove2.me/submissions/c67edaef-f69c-4f27-9ba0-05f162a13152

import Mathlib

theorem solution (N j k c : ℂ) (hN : N ≠ 0) :
    N * (j / N + c) * (k / N + c) =
      j * k / N + c * j + c * k + N * c ^ 2 := by
  field_simp
  ring
