-- Prove2me | solution 1 for R03SP03CubicOrderParity.even_order_of_cubic
-- status  : ACCEPTED   (prove)
-- author  : @hao jia
-- created : 2026-09-17T10:47:53.08782+00:00
-- url     : https://prove2.me/submissions/cbd5051f-2dce-436f-863a-6e30fd1fe21c

import Mathlib
import Definitions.Def_cubic_p3_partition_models

namespace R03SP03CubicOrderParity

open CubicP3Partition

universe u

noncomputable section

/-- A fixed, explicit Mathlib degree used by the handshaking theorem. -/
noncomputable def canonicalDegree {V : Type u} [Fintype V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (v : V) : Nat :=
  @SimpleGraph.degree V G v
    (@Subtype.fintype V (Membership.mem (G.neighborSet v))
      (@SimpleGraph.neighborSet.memDecidable V G v inferInstance) inferInstance)

/-- The explicit Mathlib degree agrees with the project's cardinal degree. -/
theorem canonicalDegree_eq_project_degree
    {V : Type u} [Fintype V] {G : SimpleGraph V}
    [DecidableRel G.Adj] (v : V) :
    canonicalDegree G v = CubicP3Partition.degree G v := by
  unfold canonicalDegree CubicP3Partition.degree
  rw [Nat.card_eq_fintype_card]
  exact (SimpleGraph.card_neighborSet_eq_degree G v).symm


end
end R03SP03CubicOrderParity

open R03SP03CubicOrderParity
open CubicP3Partition
universe u
theorem solution
    {V : Type u} [Fintype V] {G : SimpleGraph V}
    (hCubic : Cubic G) :
    Even (Fintype.card V) := by
  classical
  letI : DecidableRel G.Adj := Classical.decRel _
  have hEven := G.even_card_odd_degree_vertices
  have hAll :
      (Finset.univ.filter (fun v : V => Odd (G.degree v))) =
        (Finset.univ : Finset V) := by
    ext v
    have hdeg : G.degree v = 3 := by
      change canonicalDegree G v = 3
      rw [canonicalDegree_eq_project_degree v]
      exact hCubic v
    simp [hdeg]
    decide
  rw [hAll] at hEven
  simpa using hEven

