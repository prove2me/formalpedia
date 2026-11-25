-- Prove2me | solution 1 for Research.tri_norm_le_nine_bounds
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T17:43:20.349914+00:00
-- url     : https://prove2.me/submissions/c07ac6e6-3479-41b0-a848-3965046c6c8a

module
public import Definitions.Def_Research_Basic
public import Definitions.Def_Research_TriangularShells

set_option autoImplicit true
@[expose] public section
public section
open Research
namespace Research
theorem _root_.solution (a b : ℤ)
    (h : a ^ 2 + a * b + b ^ 2 ≤ 9) :
    -3 ≤ a ∧ a ≤ 3 ∧ -3 ≤ b ∧ b ≤ 3 := by
  have ha2 : 3 * a ^ 2 ≤ 36 := by
    nlinarith [sq_nonneg (a + 2 * b)]
  have hb2 : 3 * b ^ 2 ≤ 36 := by
    nlinarith [sq_nonneg (2 * a + b)]
  constructor
  · by_contra hn
    have ha : a ≤ -4 := by omega
    nlinarith [sq_nonneg (a + 4)]
  constructor
  · by_contra hn
    have ha : 4 ≤ a := by omega
    nlinarith [sq_nonneg (a - 4)]
  constructor
  · by_contra hn
    have hb : b ≤ -4 := by omega
    nlinarith [sq_nonneg (b + 4)]
  · by_contra hn
    have hb : 4 ≤ b := by omega
    nlinarith [sq_nonneg (b - 4)]
end Research
