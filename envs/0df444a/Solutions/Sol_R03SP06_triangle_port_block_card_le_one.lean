-- Prove2me | solution 1 for R03SP06.triangle_port_block_card_le_one
-- status  : ACCEPTED   (prove)
-- author  : @hao jia
-- created : 2026-09-17T10:48:05.826532+00:00
-- url     : https://prove2.me/submissions/8a9f0546-81d8-48da-995f-295d4a451326

import Mathlib
import Definitions.Def_cubic_p3_partition_models

set_option maxHeartbeats 800000

/-!
Candidate-only q=3 port-count formalization.  A triangle in a cubic
three-vertex-connected graph has exactly three distinct external neighbors.
The result is structural only and asserts no P3-factor.
-/

namespace R03SP06

open CubicP3Partition

variable {V : Type} [Fintype V] [DecidableEq V]

noncomputable def triangleExternalBoundary (G : SimpleGraph V) (T : Finset V) : Finset V := by
  classical
  exact Finset.univ.filter (fun v => v ∉ T ∧ ∃ t ∈ T, G.Adj t v)

lemma no_small_closed_side_for_triangle_boundary
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

lemma triangle_external_boundary_ge_three
    {G : SimpleGraph V} (h3 : ThreeVertexConnected G)
    {T : Finset V} (hT : T.card = 3) (horder : 6 ≤ Fintype.card V) :
    3 ≤ (triangleExternalBoundary G T).card := by
  classical
  by_contra hlt
  have hE : (triangleExternalBoundary G T).card ≤ 2 := by omega
  let E := triangleExternalBoundary G T
  have hE' : E.card ≤ 2 := by simpa [E] using hE
  have hTE : Disjoint T E := by
    refine Finset.disjoint_left.mpr ?_
    intro v hvT hvE
    exact (Finset.mem_filter.mp hvE).2.1 hvT
  have hunion : (T ∪ E).card ≤ 5 := by
    have hcard := Finset.card_union_le T E
    rw [hT] at hcard
    omega
  have hrestcard : (Finset.univ \ (T ∪ E)).card =
      Fintype.card V - (T ∪ E).card :=
    Finset.card_sdiff_of_subset (Finset.subset_univ _)
  have hrestpos : 0 < (Finset.univ \ (T ∪ E)).card := by
    rw [hrestcard]
    omega
  let B : Finset V := Finset.univ \ (T ∪ E)
  have hB : B.Nonempty := Finset.card_pos.mp (by simpa [B] using hrestpos)
  have hA : T.Nonempty := Finset.card_pos.mp (by omega)
  have hAB : Disjoint T B := by
    refine Finset.disjoint_left.mpr ?_
    intro v hvT hvB
    exact (Finset.mem_sdiff.mp hvB).2 (Finset.mem_union_left E hvT)
  have hBT : Disjoint B E := by
    refine Finset.disjoint_left.mpr ?_
    intro v hvB hvE
    exact (Finset.mem_sdiff.mp hvB).2 (Finset.mem_union_right T hvE)
  have hclosed : ∀ ⦃u v : V⦄, u ∈ T → G.Adj u v → v ∈ T ∪ E := by
    intro u v hu huv
    by_cases hvT : v ∈ T
    · exact Finset.mem_union_left E hvT
    · apply Finset.mem_union_right T
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hvT, ⟨u, hu, huv⟩⟩
  exact no_small_closed_side_for_triangle_boundary h3 hA hB hAB hTE hBT hclosed hE


end R03SP06

open R03SP06
open CubicP3Partition
variable {V : Type} [Fintype V] [DecidableEq V]
theorem solution
    {G : SimpleGraph V} [DecidableRel G.Adj] {T : Finset V} {t : V}
    (ht : t ∈ T)
    (hport : ∀ ⦃t u v : V⦄, t ∈ T → u ∉ T → v ∉ T →
      G.Adj t u → G.Adj t v → u = v) :
    (Finset.univ.filter (fun v : V => v ∉ T ∧ G.Adj t v)).card ≤ 1 := by
  classical
  apply Finset.card_le_one_iff.mpr
  intro u v hu hv
  exact hport ht (Finset.mem_filter.mp hu).2.1 (Finset.mem_filter.mp hv).2.1
    (Finset.mem_filter.mp hu).2.2 (Finset.mem_filter.mp hv).2.2

