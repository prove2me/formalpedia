-- Prove2me | solution 1 for R03ThreeVertexSeparatorCandidate.not_reachable_across_partition
-- status  : ACCEPTED   (prove)
-- author  : @hao jia
-- created : 2026-09-16T11:13:01.908462+00:00
-- url     : https://prove2.me/submissions/16d29d34-8162-42c7-b880-6103cfe050d1

import Definitions.Def_cubic_p3_partition_models
import Definitions.Def_cubic_p3_partition_external_boundary

/-!
# Three-vertex separator boundary candidate

Candidate-only Lean formalization for `problem:opg-46613-p3-partition`.
It records the elementary separator consequence of the project's
`ThreeVertexConnected` definition. It does not construct a P3-factor or close
the root problem.
-/

namespace R03ThreeVertexSeparatorCandidate

universe u
variable {V : Type u} [Fintype V] [DecidableEq V]

open CubicP3Partition

/-- A walk cannot move from one side of a partition to the other when no edge
joins the two sides. -/
lemma not_reachable_across_partition
    {U : Type u} (H : SimpleGraph U)
    (A B : Set U)
    (hdisj : Disjoint A B)
    (hpart : ∀ x, x ∈ A ∨ x ∈ B)
    (hno : ∀ {x y}, x ∈ A → y ∈ B → ¬ H.Adj x y)
    {u v : U} (hu : u ∈ A) (hv : v ∈ B) :
    ¬ H.Reachable u v := by
  intro hreach
  rcases hreach with ⟨p⟩
  have hstay : ∀ {x y : U} (p : H.Walk x y), x ∈ A → y ∈ A := by
    intro x y p
    induction p with
    | nil =>
        intro hx
        exact hx
    | @cons x y z h p ih =>
        intro hx
        have hyA : y ∈ A := by
          rcases hpart y with hyA | hyB
          · exact hyA
          · exact False.elim (hno hx hyB h)
        exact ih hyA
  exact (Set.disjoint_left.1 hdisj) (hstay p hu) hv

/-- In a finite simple graph satisfying the project's three-vertex-connectivity
predicate, every separator separating two nonempty sides has at least three
vertices. -/
theorem three_vertex_connected_separator_card_ge_three
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hG : ThreeVertexConnected G)
    (Q N R : Finset V)
    (hQN : Disjoint Q N)
    (hQR : Disjoint Q R)
    (hNR : Disjoint N R)
    (hcover : Q ∪ N ∪ R = Finset.univ)
    (hQ : Q.Nonempty)
    (hR : R.Nonempty)
    (hno : ∀ q ∈ Q, ∀ r ∈ R, ¬ G.Adj q r) :
    3 ≤ N.card := by
  classical
  by_contra hNsmall
  have hNle : N.card ≤ 2 := by omega
  have hconn0 := hG.2 N hNle
  obtain ⟨q, hq⟩ := hQ
  obtain ⟨r, hr⟩ := hR
  have hqN : q ∉ N := by
    intro hqN
    exact Finset.disjoint_left.1 hQN hq hqN
  have hrN : r ∉ N := by
    intro hrN
    exact Finset.disjoint_left.1 hNR hrN hr
  let U := {v : V // v ∉ N}
  let H : SimpleGraph U := G.induce {v : V | v ∉ N}
  have hconnH : H.Connected := by
    simpa [H, U] using hconn0
  let q' : U := ⟨q, by simpa [U] using hqN⟩
  let r' : U := ⟨r, by simpa [U] using hrN⟩
  let A : Set U := {x | x.1 ∈ Q}
  let B : Set U := {x | x.1 ∈ R}
  have hpart : ∀ x : U, x ∈ A ∨ x ∈ B := by
    intro x
    by_cases hxQ : x.1 ∈ Q
    · exact Or.inl hxQ
    · have hxN : x.1 ∉ N := x.property
      have hxcover : x.1 ∈ Q ∪ N ∪ R := by
        rw [hcover]
        simp
      rcases Finset.mem_union.mp hxcover with hxQN | hxR
      · rcases Finset.mem_union.mp hxQN with hxQ' | hxN'
        · exact False.elim (hxQ hxQ')
        · exact False.elim (hxN hxN')
      · exact Or.inr hxR
  have hdisjAB : Disjoint A B := by
    refine Set.disjoint_left.2 ?_
    intro x hxA hxB
    exact Finset.disjoint_left.1 hQR hxA hxB
  have hnoAB : ∀ {x y : U}, x ∈ A → y ∈ B → ¬ H.Adj x y := by
    intro x y hxA hyB hadj
    have hadj' : G.Adj x.1 y.1 := by
      apply SimpleGraph.induce_adj.mp
      simpa [H] using hadj
    exact hno x.1 hxA y.1 hyB hadj'
  have hqA : q' ∈ A := by
    exact hq
  have hrB : r' ∈ B := by
    exact hr
  have hnreach : ¬ H.Reachable q' r' :=
    not_reachable_across_partition H A B hdisjAB hpart hnoAB hqA hrB
  exact False.elim (hnreach (hconnH q' r'))

/-- If both the set and the part remaining after deleting its external
boundary are nonempty, three-vertex-connectivity forces that boundary to have
at least three vertices. -/
theorem three_vertex_connected_external_boundary_card_ge_three
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hG : ThreeVertexConnected G)
    (Q : Finset V)
    (hQ : Q.Nonempty)
    (hR : (Finset.univ \ (Q ∪ externalBoundary G Q)).Nonempty) :
    3 ≤ (externalBoundary G Q).card := by
  classical
  let N : Finset V := externalBoundary G Q
  let R : Finset V := Finset.univ \ (Q ∪ N)
  have hQN : Disjoint Q N := by
    refine Finset.disjoint_left.2 ?_
    intro v hvQ hvN
    exact (Finset.mem_sdiff.mp (show v ∈
      Q.biUnion (fun v => G.neighborFinset v) \ Q by
        simpa [N, externalBoundary] using hvN)).2 hvQ
  have hQR : Disjoint Q R := by
    refine Finset.disjoint_left.2 ?_
    intro v hvQ hvR
    exact (Finset.mem_sdiff.mp (show v ∈
      Finset.univ \ (Q ∪ N) by simpa [R] using hvR)).2
      (Finset.mem_union.mpr (Or.inl hvQ))
  have hNR : Disjoint N R := by
    refine Finset.disjoint_left.2 ?_
    intro v hvN hvR
    exact (Finset.mem_sdiff.mp (show v ∈
      Finset.univ \ (Q ∪ N) by simpa [R] using hvR)).2
      (Finset.mem_union.mpr (Or.inr hvN))
  have hcover : Q ∪ N ∪ R = Finset.univ := by
    ext v
    constructor
    · intro hv
      simp
    · intro hv
      by_cases hvQN : v ∈ Q ∪ N
      · exact Finset.mem_union.mpr (Or.inl hvQN)
      · exact Finset.mem_union.mpr (Or.inr
          (Finset.mem_sdiff.mpr ⟨Finset.mem_univ v, hvQN⟩))
  have hR' : R.Nonempty := by
    simpa [R, N, externalBoundary] using hR
  have hno : ∀ q ∈ Q, ∀ r ∈ R, ¬ G.Adj q r := by
    intro q hq r hr hadj
    have hr' : r ∈ Finset.univ \ (Q ∪ N) := by simpa [R] using hr
    have hrnotQ : r ∉ Q := by
      intro hrQ
      exact (Finset.mem_sdiff.mp hr').2
        (Finset.mem_union.mpr (Or.inl hrQ))
    have hrbi : r ∈ Q.biUnion (fun v => G.neighborFinset v) := by
      exact Finset.mem_biUnion.mpr ⟨q, hq,
        (SimpleGraph.mem_neighborFinset G q r).mpr hadj⟩
    have hrN : r ∈ N := by
      dsimp [N, externalBoundary]
      exact Finset.mem_sdiff.mpr ⟨hrbi, hrnotQ⟩
    exact (Finset.mem_sdiff.mp hr').2
      (Finset.mem_union.mpr (Or.inr hrN))
  have hbound := three_vertex_connected_separator_card_ge_three
    G hG Q N R hQN hQR hNR hcover hQ hR' hno
  exact hbound

/-- If the ambient order is divisible by three and `Q` has exactly three
vertices, the external boundary cannot have fewer than three vertices. The
case where the boundary exhausts the complement is handled explicitly; the
separator theorem is used only when a nonempty remainder survives. -/
theorem three_vertex_connected_external_boundary_card_ge_three_of_divisible_order
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hG : ThreeVertexConnected G)
    (hdiv : 3 ∣ Fintype.card V)
    (Q : Finset V)
    (hQcard : Q.card = 3) :
    3 ≤ (externalBoundary G Q).card := by
  classical
  have hVge : 6 ≤ Fintype.card V := by
    have h4 := hG.1
    omega
  have hQsub : Q ⊆ Finset.univ := by
    intro v hv
    simp
  have hcompcard : (Finset.univ \ Q).card = Fintype.card V - Q.card := by
    simpa using (Finset.card_sdiff_of_subset hQsub)
  have hcompge : 3 ≤ (Finset.univ \ Q).card := by
    rw [hcompcard, hQcard]
    omega
  have hQnonempty : Q.Nonempty := Finset.card_pos.mp (by omega)
  by_cases hR : (Finset.univ \ (Q ∪ externalBoundary G Q)).Nonempty
  · exact three_vertex_connected_external_boundary_card_ge_three G hG Q
      hQnonempty hR
  · have hNsub : externalBoundary G Q ⊆ Finset.univ \ Q := by
      intro v hv
      have hv' : v ∈ Q.biUnion (fun v => G.neighborFinset v) \ Q := by
        simpa [externalBoundary] using hv
      exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ v,
        (Finset.mem_sdiff.mp hv').2⟩
    have hsubN : Finset.univ \ Q ⊆ externalBoundary G Q := by
      intro v hv
      have hvnotQ : v ∉ Q := (Finset.mem_sdiff.mp hv).2
      by_contra hvN
      apply hR
      refine ⟨v, Finset.mem_sdiff.mpr ⟨Finset.mem_univ v, ?_⟩⟩
      intro hvQN
      rcases Finset.mem_union.mp hvQN with hvQ | hvN'
      · exact hvnotQ hvQ
      · exact hvN hvN'
    have hEq : externalBoundary G Q = Finset.univ \ Q :=
      Finset.Subset.antisymm hNsub hsubN
    rw [hEq, hcompcard, hQcard]
    omega


end R03ThreeVertexSeparatorCandidate

open CubicP3Partition R03ThreeVertexSeparatorCandidate

universe u
variable {V : Type u} [Fintype V] [DecidableEq V]

theorem solution
    {U : Type u} (H : SimpleGraph U)
    (A B : Set U)
    (hdisj : Disjoint A B)
    (hpart : ∀ x, x ∈ A ∨ x ∈ B)
    (hno : ∀ {x y}, x ∈ A → y ∈ B → ¬ H.Adj x y)
    {u v : U} (hu : u ∈ A) (hv : v ∈ B) :
    ¬ H.Reachable u v := by
  intro hreach
  rcases hreach with ⟨p⟩
  have hstay : ∀ {x y : U} (p : H.Walk x y), x ∈ A → y ∈ A := by
    intro x y p
    induction p with
    | nil =>
        intro hx
        exact hx
    | @cons x y z h p ih =>
        intro hx
        have hyA : y ∈ A := by
          rcases hpart y with hyA | hyB
          · exact hyA
          · exact False.elim (hno hx hyB h)
        exact ih hyA
  exact (Set.disjoint_left.1 hdisj) (hstay p hu) hv
