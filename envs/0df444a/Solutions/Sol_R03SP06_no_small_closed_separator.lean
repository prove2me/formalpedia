-- Prove2me | solution 1 for R03SP06.no_small_closed_separator
-- status  : ACCEPTED   (prove)
-- author  : @hao jia
-- created : 2026-09-17T10:47:57.975224+00:00
-- url     : https://prove2.me/submissions/564517a5-fa7a-4a54-8532-c7f26de40789

import Mathlib
import Definitions.Def_cubic_p3_partition_models

/-!
Candidate formalization of the separator-port obstruction used in the q=5
leaf analyses.  A residual component with no edge to the deleted set cannot be
closed by at most two residual separator vertices in a three-vertex-connected
completion.  The theorem is deliberately stated at the finite-set boundary
level; the graph-specific extraction of A, B, S and T remains external.
-/

namespace R03SP06

open CubicP3Partition

variable {V : Type} [Fintype V] [DecidableEq V]


end R03SP06

open R03SP06
open CubicP3Partition
variable {V : Type} [Fintype V] [DecidableEq V]
theorem solution
    {G : SimpleGraph V} (h3 : ThreeVertexConnected G)
    {A B T : Finset V}
    (hA : A.Nonempty) (hB : B.Nonempty)
    (hAB : Disjoint A B) (hAT : Disjoint A T) (hBT : Disjoint B T)
    (hclosed : ∀ ⦃u v : V⦄, u ∈ A → G.Adj u v → v ∈ A ∪ T)
    (hT : T.card ≤ 2) : False := by
  classical
  let H : SimpleGraph {v : V // v ∉ T} := G.induce {v : V | v ∉ T}
  have hnot : ¬ H.Connected := by
    intro hconn
    obtain ⟨x, hxA⟩ := hA
    obtain ⟨y, hyB⟩ := hB
    have hxT : x ∉ T := by
      intro hx
      exact (Finset.disjoint_left.1 hAT) hxA hx
    have hyT : y ∉ T := by
      intro hy
      exact (Finset.disjoint_left.1 hBT) hyB hy
    have hreach : H.Reachable ⟨x, hxT⟩ ⟨y, hyT⟩ :=
      hconn.preconnected ⟨x, hxT⟩ ⟨y, hyT⟩
    have stay : ∀ {u v : {v : V // v ∉ T}},
        (p : H.Walk u v) → u.1 ∈ A → v.1 ∈ A := by
      intro u v p
      induction p with
      | nil =>
          intro hu
          exact hu
      | @cons u w v hadj tail ih =>
          intro hu
          have hw : w.1 ∈ A ∪ T := hclosed hu hadj
          have hw' : w.1 ∈ A ∨ w.1 ∈ T := by
            simpa [Finset.mem_union] using hw
          have hwA : w.1 ∈ A := by
            rcases hw' with hwA | hwT
            · exact hwA
            · exact False.elim (w.2 hwT)
          exact ih hwA
    have hyA : y ∈ A := stay hreach.some hxA
    exact (Finset.disjoint_left.1 hAB) hyA hyB
  exact hnot (h3.2 T hT)

