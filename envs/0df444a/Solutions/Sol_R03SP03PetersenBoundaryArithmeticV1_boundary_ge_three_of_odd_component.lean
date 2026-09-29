-- Prove2me | solution 1 for R03SP03PetersenBoundaryArithmeticV1.boundary_ge_three_of_odd_component
-- status  : ACCEPTED   (prove)
-- author  : @hao jia
-- created : 2026-09-17T00:54:59.947897+00:00
-- url     : https://prove2.me/submissions/0238d1c2-4cab-4d29-ad25-e26cf8263b92

import Mathlib

namespace R03SP03PetersenBoundaryArithmeticV1


end R03SP03PetersenBoundaryArithmeticV1

open R03SP03PetersenBoundaryArithmeticV1
theorem solution
    (component_vertices internal_edges boundary_edges : Nat)
    (hodd : Odd component_vertices)
    (hhandshake : 3 * component_vertices =
      2 * internal_edges + boundary_edges)
    (hnot_zero : boundary_edges ≠ 0)
    (hnot_one : boundary_edges ≠ 1) :
    3 ≤ boundary_edges := by
  rcases hodd with ⟨k, hk⟩
  omega

