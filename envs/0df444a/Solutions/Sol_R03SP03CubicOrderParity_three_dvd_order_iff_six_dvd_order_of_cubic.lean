-- Prove2me | solution 1 for R03SP03CubicOrderParity.three_dvd_order_iff_six_dvd_order_of_cubic
-- status  : ACCEPTED   (prove)
-- author  : @hao jia
-- created : 2026-09-17T00:55:04.281494+00:00
-- url     : https://prove2.me/submissions/e407eef8-1bac-4a20-be5e-605facb07d55

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

/-- Cubic finite graphs have even order, by the handshaking lemma. -/
theorem even_order_of_cubic
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


end
end R03SP03CubicOrderParity

open R03SP03CubicOrderParity
open CubicP3Partition
universe u
theorem solution
    {V : Type u} [Fintype V] {G : SimpleGraph V}
    (hCubic : Cubic G) :
    3 ∣ Fintype.card V ↔ 6 ∣ Fintype.card V := by
  constructor
  · intro h3
    rcases h3 with ⟨k, hk⟩
    rcases even_order_of_cubic hCubic with ⟨j, hj⟩
    refine ⟨k / 2, ?_⟩
    omega
  · intro h6
    rcases h6 with ⟨k, hk⟩
    exact ⟨2 * k, by omega⟩

