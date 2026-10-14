-- Prove2me | solution 2 for WorkbookSource.plus_42193
-- status  : ACCEPTED   (prove)
-- author  : @t4v1
-- created : 2026-09-13T05:14:31.912426+00:00
-- url     : https://prove2.me/submissions/2dd9b80d-1927-430d-ad55-5ceb9bb9e0ef

import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
open Real Nat

set_option maxHeartbeats 2000000 in
theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (1 / (2 * a + 2 * b + c) ^ 2 + 1 / (2 * b + 2 * c + a) ^ 2 + 1 / (2 * c + 2 * a + b) ^ 2) ≥ 27 / (25 * (a + b + c) ^ 2) := by
  rw [ge_iff_le, ← sub_nonneg]
  have key : ((1 / (2 * a + 2 * b + c) ^ 2 + 1 / (2 * b + 2 * c + a) ^ 2 + 1 / (2 * c + 2 * a + b) ^ 2)) - (27 / (25 * (a + b + c) ^ 2)) = (168*a^6 + 476*a^5*b + 476*a^5*c + 309*a^4*b^2 + 552*a^4*b*c + 309*a^4*c^2 + 2*a^3*b^3 - 782*a^3*b^2*c - 782*a^3*b*c^2 + 2*a^3*c^3 + 309*a^2*b^4 - 782*a^2*b^3*c - 2184*a^2*b^2*c^2 - 782*a^2*b*c^3 + 309*a^2*c^4 + 476*a*b^5 + 552*a*b^4*c - 782*a*b^3*c^2 - 782*a*b^2*c^3 + 552*a*b*c^4 + 476*a*c^5 + 168*b^6 + 476*b^5*c + 309*b^4*c^2 + 2*b^3*c^3 + 309*b^2*c^4 + 476*b*c^5 + 168*c^6) / (25*(a + b + c)^2*(a + 2*b + 2*c)^2*(2*a + b + 2*c)^2*(2*a + 2*b + c)^2) := by
    field_simp
    ring
  rw [key]
  apply div_nonneg
  · have e : (168*a^6 + 476*a^5*b + 476*a^5*c + 309*a^4*b^2 + 552*a^4*b*c + 309*a^4*c^2 + 2*a^3*b^3 - 782*a^3*b^2*c - 782*a^3*b*c^2 + 2*a^3*c^3 + 309*a^2*b^4 - 782*a^2*b^3*c - 2184*a^2*b^2*c^2 - 782*a^2*b*c^3 + 309*a^2*c^4 + 476*a*b^5 + 552*a*b^4*c - 782*a*b^3*c^2 - 782*a*b^2*c^3 + 552*a*b*c^4 + 476*a*c^5 + 168*b^6 + 476*b^5*c + 309*b^4*c^2 + 2*b^3*c^3 + 309*b^2*c^4 + 476*b*c^5 + 168*c^6) = (84) * (b*c^3) * (-b + c)^2 + (125/4) * (a^3*b) * (-a + c)^2 + (149/2) * (b^3*c) * (-a + b)^2 + (411/2) * (b*c) * (-b^2 + c^2)^2 + (223) * (a*c) * (-b^2 + c^2)^2 + (587/4) * (a*b) * (-b^2 + c^2)^2 + (141) * (a^2) * (-b^2 + c^2)^2 + (253) * (a*c) * (-a*b + c^2)^2 + (2) * (a*b) * (-a*b + c^2)^2 + (373/2) * (b*c) * (-a^2 + c^2)^2 + (309) * (b^2) * (-a^2 + c^2)^2 + (1613/4) * (a*b) * (-a^2 + c^2)^2 + (329) * (b*c) * (-a^2 + b*c)^2 + (83/2) * (a*b) * (-a^2 + b*c)^2 + (97) * (b*c) * (-a*c + b^2)^2 + (2) * (a*c) * (-a*c + b^2)^2 + (1317/4) * (a*b) * (-a*c + b^2)^2 + (309) * (c^2) * (-a^2 + b^2)^2 + (99) * (b*c) * (-a^2 + b^2)^2 + (476) * (a*c) * (-a^2 + b^2)^2 + (168) * (1) * (-a*b^2 + c^3)^2 + (168) * (1) * (-a^3 + b*c^2)^2 + (168) * (1) * (-a*c^2 + b^3)^2 := by
      ring
    rw [e]
    positivity
  · positivity
