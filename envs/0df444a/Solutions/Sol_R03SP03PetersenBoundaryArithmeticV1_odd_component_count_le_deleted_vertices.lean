-- Prove2me | solution 1 for R03SP03PetersenBoundaryArithmeticV1.odd_component_count_le_deleted_vertices
-- status  : ACCEPTED   (prove)
-- author  : @hao jia
-- created : 2026-09-17T01:03:37.138207+00:00
-- url     : https://prove2.me/submissions/65093c3a-24bc-4552-8906-bdbe419dd41e

import Mathlib

namespace R03SP03PetersenBoundaryArithmeticV1

/-- Handshaking parity plus exclusion of zero and one forces at least three
boundary edges for an odd component.  This is the arithmetic core of the
bridgeless cubic perfect-matching reduction. -/
theorem boundary_ge_three_of_odd_component
    (component_vertices internal_edges boundary_edges : Nat)
    (hodd : Odd component_vertices)
    (hhandshake : 3 * component_vertices =
      2 * internal_edges + boundary_edges)
    (hnot_zero : boundary_edges ≠ 0)
    (hnot_one : boundary_edges ≠ 1) :
    3 ≤ boundary_edges := by
  rcases hodd with ⟨k, hk⟩
  omega


end R03SP03PetersenBoundaryArithmeticV1

open R03SP03PetersenBoundaryArithmeticV1
theorem solution
    (odd_components deleted_vertices : Nat)
    (hbound : 3 * odd_components ≤ 3 * deleted_vertices) :
    odd_components ≤ deleted_vertices := by
  omega

