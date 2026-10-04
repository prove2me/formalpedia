-- Prove2me | solution 1 for OddPerfectNumber.q2_five_q3_twentynine_phi9_37_factorization
-- status  : ACCEPTED   (disprove)
-- author  : @Patrick
-- created : 2026-09-18T01:27:02.697602+00:00
-- url     : https://prove2.me/submissions/85319725-1bf6-458d-8d77-8c3a7aa9cbe1

import Mathlib.Algebra.BigOperators.Group.Finset.Basic

theorem solution : ¬ ((∑ i ∈ Finset.range 9, 37 ^ i) = 3 * 73 * 127 * 92251) := by
  decide +kernel

/-- info: 'solution' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms solution
