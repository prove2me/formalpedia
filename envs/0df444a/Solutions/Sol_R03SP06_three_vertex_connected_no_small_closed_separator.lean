-- Prove2me | solution 1 for R03SP06.three_vertex_connected_no_small_closed_separator
-- status  : ACCEPTED   (prove)
-- author  : @hao jia
-- created : 2026-09-16T10:45:01.002438+00:00
-- url     : https://prove2.me/submissions/55a1b178-ba4d-4c03-8199-866bbd7e00ac

import Mathlib
import Definitions.Def_cubic_p3_partition_models

/-!
Candidate formalization of the separator mechanism behind the P3-deletion
connectivity argument.  It is graph-generic: a nonempty set A closed under
all edges except through a separator T cannot coexist with a nonempty set B
outside A after T is deleted.  No 3-connectivity or cubic hypothesis is
used here; those hypotheses are needed only to bound the separator in the
application.
-/

namespace R03SP06

open CubicP3Partition

variable {V : Type} [DecidableEq V]

/-- A finite separator disconnects an induced graph when one nonempty side is
closed under all edges except into the separator. -/
theorem induced_not_connected_of_closed_side
    {G : SimpleGraph V} {A B T : Finset V}
    (hA : A.Nonempty) (hB : B.Nonempty)
    (hAB : Disjoint A B) (hAT : Disjoint A T) (hBT : Disjoint B T)
    (hclosed : ∀ ⦃u v : V⦄, u ∈ A → G.Adj u v → v ∈ A ∪ T) :
    ¬ (G.induce {v : V | v ∉ T}).Connected := by
  intro hconn
  obtain ⟨x, hxA⟩ := hA
  obtain ⟨y, hyB⟩ := hB
  have hxT : x ∉ T := by
    intro hx
    exact (Finset.disjoint_left.1 hAT) hxA hx
  have hyT : y ∉ T := by
    intro hy
    exact (Finset.disjoint_left.1 hBT) hyB hy
  let H : SimpleGraph {v : V // v ∉ T} := G.induce {v : V | v ∉ T}
  have hreach : H.Reachable ⟨x, hxT⟩ ⟨y, hyT⟩ := by
    exact hconn.preconnected ⟨x, hxT⟩ ⟨y, hyT⟩
  have stay_in_A : ∀ {u v : {v : V // v ∉ T}},
      (p : H.Walk u v) → u.1 ∈ A → v.1 ∈ A := by
    intro u v p
    induction p with
    | nil =>
        intro hu
        exact hu
    | @cons u w v hadj tail ih =>
        intro hu
        have hwAT : w.1 ∈ A ∪ T := by
          apply hclosed hu
          exact hadj
        have hwAT' : w.1 ∈ A ∨ w.1 ∈ T := by
          simpa [Finset.mem_union] using hwAT
        have hwA : w.1 ∈ A := by
          rcases hwAT' with hwA | hwT
          · exact hwA
          · exact False.elim (w.2 hwT)
        exact ih hwA
  have hyA : y ∈ A := by
    exact stay_in_A hreach.some hxA
  exact (Finset.disjoint_left.1 hAB) hyA hyB


/-- In the project connectivity model, a three-vertex-connected graph cannot
have a nonempty proper side A separated from another nonempty side B by a
separator of size at most two, when A has no edge to the outside except
through that separator. -/
theorem three_vertex_connected_no_small_closed_separator
    {G : SimpleGraph V} [Fintype V]
    (h3 : ThreeVertexConnected G) {A B T : Finset V}
    (hA : A.Nonempty) (hB : B.Nonempty)
    (hAB : Disjoint A B) (hAT : Disjoint A T) (hBT : Disjoint B T)
    (hclosed : ∀ ⦃u v : V⦄, u ∈ A → G.Adj u v → v ∈ A ∪ T)
    (hT : T.card ≤ 2) : False := by
  apply induced_not_connected_of_closed_side hA hB hAB hAT hBT hclosed
  exact h3.2 T hT


/-- A reusable residual-connectivity theorem.  If the center b has no two
 distinct neighbors in the residual that can lie in different residual
components, then deleting the P3 endpoints and center leaves a connected
induced graph.  The premise is deliberately expressed as a boundary-state
condition; the cubic counting file supplies it for a cubic P3 center. -/
theorem residual_p3_deletion_connected_of_center_condition
    {G : SimpleGraph V} [Fintype V]
    {a b c : V} (hac : a ≠ c)
    (h2 : ∀ S : Finset V, S.card ≤ 2 →
      (G.induce {v : V | v ∉ S}).Connected)
    (hres : ∃ v : V, v ≠ a ∧ v ≠ b ∧ v ≠ c)
    (hcenter : ∀ {x y : {v : V // v ≠ a ∧ v ≠ b ∧ v ≠ c}},
      x.1 ≠ y.1 → G.Adj b x.1 → G.Adj b y.1 → False) :
    (G.induce {v : V | v ≠ a ∧ v ≠ b ∧ v ≠ c}).Connected := by
  classical
  let H : SimpleGraph {v : V // v ≠ a ∧ v ≠ b ∧ v ≠ c} :=
    G.induce {v : V | v ≠ a ∧ v ≠ b ∧ v ≠ c}
  have hpre : H.Preconnected := by
    intro x y
    by_contra hxy
    have component_separator : ∀
        (z other : {v : V // v ≠ a ∧ v ≠ b ∧ v ≠ c}),
        ¬ H.Reachable z other →
        (∀ u : {v : V // v ≠ a ∧ v ≠ b ∧ v ≠ c},
          H.Reachable z u → ¬ G.Adj b u.1) → False := by
      intro z other hnot hno
      let A : Finset V := Finset.univ.filter
        (fun v : V => ∃ hv : v ≠ a ∧ v ≠ b ∧ v ≠ c,
          H.Reachable z ⟨v, hv⟩)
      let B : Finset V := {other.1}
      let T : Finset V := {a, c}
      have hA : A.Nonempty := by
        refine ⟨z.1, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩⟩
        exact ⟨z.2, SimpleGraph.Reachable.refl z⟩
      have hB : B.Nonempty := by
        exact ⟨other.1, by simp [B]⟩
      have hAB : Disjoint A B := by
        refine Finset.disjoint_left.mpr ?_
        intro v hvA hvB
        have hvEq : v = other.1 := by simpa [B] using hvB
        subst v
        obtain ⟨hv, hreach⟩ := (Finset.mem_filter.mp hvA).2
        exact hnot hreach
      have hAT : Disjoint A T := by
        refine Finset.disjoint_left.mpr ?_
        intro v hvA hvT
        obtain ⟨hv, _⟩ := (Finset.mem_filter.mp hvA).2
        have hvT' : v = a ∨ v = c := by simpa [T] using hvT
        rcases hvT' with rfl | rfl
        · exact hv.1 rfl
        · exact hv.2.2 rfl
      have hBT : Disjoint B T := by
        refine Finset.disjoint_left.mpr ?_
        intro v hvB hvT
        have hvEq : v = other.1 := by simpa [B] using hvB
        subst v
        have hvT' : other.1 = a ∨ other.1 = c := by simpa [T] using hvT
        rcases hvT' with hEq | hEq
        · exact other.2.1 hEq
        · exact other.2.2.2 hEq
      have hclosed : ∀ ⦃u v : V⦄, u ∈ A → G.Adj u v → v ∈ A ∪ T := by
        intro u v hu huv
        obtain ⟨huR, hzu⟩ := (Finset.mem_filter.mp hu).2
        by_cases hva : v = a
        · simp [T, hva]
        by_cases hvc : v = c
        · simp [T, hvc]
        by_cases hvb : v = b
        · subst v
          exact False.elim (hno ⟨u, huR⟩ hzu huv.symm)
        have hvR : v ≠ a ∧ v ≠ b ∧ v ≠ c := ⟨hva, hvb, hvc⟩
        have huvH : H.Adj ⟨u, huR⟩ ⟨v, hvR⟩ := huv
        have hzv : H.Reachable z ⟨v, hvR⟩ :=
          hzu.trans huvH.reachable
        have hvA : v ∈ A := by
          exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, ⟨hvR, hzv⟩⟩
        exact Finset.mem_union_left T hvA
      have hT : T.card ≤ 2 := by simp [T, hac]
      exact (induced_not_connected_of_closed_side hA hB hAB hAT hBT hclosed) (h2 T hT)
    by_cases hxcomp : ∃ u : {v : V // v ≠ a ∧ v ≠ b ∧ v ≠ c},
        H.Reachable x u ∧ G.Adj b u.1
    · have hycomp : ∀ u : {v : V // v ≠ a ∧ v ≠ b ∧ v ≠ c},
          H.Reachable y u → ¬ G.Adj b u.1 := by
        intro u hyu hbu
        obtain ⟨u₀, hxu₀, hbu₀⟩ := hxcomp
        apply hcenter
        · intro heq
          apply hxy
          have heq' : u₀ = u := Subtype.ext heq.symm
          have huy : H.Reachable u₀ y := by
            rw [heq']
            exact hyu.symm
          exact hxu₀.trans huy
        · exact hbu
        · exact hbu₀
      exact component_separator y x (fun h => hxy h.symm) hycomp
    · have hxno : ∀ u : {v : V // v ≠ a ∧ v ≠ b ∧ v ≠ c},
          H.Reachable x u → ¬ G.Adj b u.1 := by
        intro u hxu hbu
        exact hxcomp ⟨u, hxu, hbu⟩
      exact component_separator x y hxy hxno
  have hnonempty : Nonempty {v : V // v ≠ a ∧ v ≠ b ∧ v ≠ c} := by
    obtain ⟨v, hv⟩ := hres
    exact ⟨⟨v, hv⟩⟩
  have hH : H.Connected := { preconnected := hpre, nonempty := hnonempty }
  simpa [H] using hH


/-- Full candidate formalization of the previously recorded connectivity
lemma.  Only the degree-three condition at the P3 center is needed: the
center has one residual neighbor, so one of two residual components would be
a closed side behind the two endpoints. -/
theorem degree_three_p3_deletion_connected
    {G : SimpleGraph V} [Fintype V] [DecidableRel G.Adj]
    {a b c : V} (hab : G.Adj a b) (hbc : G.Adj b c) (hac : a ≠ c)
    (hdeg : (Finset.univ.filter (fun w : V => G.Adj b w)).card = 3)
    (h2 : ∀ S : Finset V, S.card ≤ 2 →
      (G.induce {v : V | v ∉ S}).Connected) :
    (G.induce {v : V | v ≠ a ∧ v ≠ b ∧ v ≠ c}).Connected := by
  classical
  let N : Finset V := Finset.univ.filter (fun w : V => G.Adj b w)
  have hsub : {a, c} ⊆ N := by
    intro v hv
    simp only [Finset.mem_insert, Finset.mem_singleton] at hv
    rcases hv with rfl | rfl
    · simpa [N] using (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hab.symm⟩)
    · simpa [N] using (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hbc⟩)
  have hN : N.card = 3 := by simpa [N] using hdeg
  have hone : (N \ {a, c}).card = 1 := by
    rw [Finset.card_sdiff_of_subset hsub, hN]
    simp [hac]
  have hres : ∃ v : V, v ≠ a ∧ v ≠ b ∧ v ≠ c := by
    have hne : (N \ {a, c}).Nonempty := by
      apply Finset.card_pos.mp
      rw [hone]
      decide
    obtain ⟨v, hv⟩ := hne
    have hvN : v ∈ N := (Finset.mem_sdiff.mp hv).1
    have hvAC : v ≠ a ∧ v ≠ c := by
      simpa using (Finset.mem_sdiff.mp hv).2
    have hvAdj : G.Adj b v := (Finset.mem_filter.mp hvN).2
    refine ⟨v, hvAC.1, ?_, hvAC.2⟩
    intro hvb
    subst v
    exact SimpleGraph.irrefl G hvAdj
  have hcenter : ∀ {x y : {v : V // v ≠ a ∧ v ≠ b ∧ v ≠ c}},
      x.1 ≠ y.1 → G.Adj b x.1 → G.Adj b y.1 → False := by
    intro x y hxy hbx hby
    have hxN : x.1 ∈ N := by
      simpa [N] using (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hbx⟩)
    have hyN : y.1 ∈ N := by
      simpa [N] using (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hby⟩)
    have hxE : x.1 ∈ N \ {a, c} := by
      refine Finset.mem_sdiff.mpr ⟨hxN, ?_⟩
      simp [x.2.1, x.2.2.2]
    have hyE : y.1 ∈ N \ {a, c} := by
      refine Finset.mem_sdiff.mpr ⟨hyN, ?_⟩
      simp [y.2.1, y.2.2.2]
    have hxyE : ({x.1, y.1} : Finset V) ⊆ N \ {a, c} := by
      intro v hv
      simp only [Finset.mem_insert, Finset.mem_singleton] at hv
      rcases hv with rfl | rfl
      · exact hxE
      · exact hyE
    have hcard := Finset.card_le_card hxyE
    rw [hone] at hcard
    simp [hxy] at hcard
  exact residual_p3_deletion_connected_of_center_condition hac h2 hres hcenter


/-- Project-model wrapper: the local degree hypothesis is supplied by
`Cubic`, and the two-vertex deletion connectivity hypothesis is supplied by
`ThreeVertexConnected`.  This closes the candidate formalization of the
connectivity-after-P3-deletion lemma, but it still says nothing about a
P3-factor in the residual graph. -/
theorem cubic_three_vertex_connected_p3_deletion_connected
    {G : SimpleGraph V} [Fintype V] [DecidableRel G.Adj]
    (hC : Cubic G) (h3 : ThreeVertexConnected G)
    {a b c : V} (hab : G.Adj a b) (hbc : G.Adj b c) (hac : a ≠ c) :
    (G.induce {v : V | v ≠ a ∧ v ≠ b ∧ v ≠ c}).Connected := by
  classical
  have hdegree : Nat.card {w : V // G.Adj b w} = 3 := by
    exact hC b
  have hcard : (G.neighborFinset b).card =
      Nat.card {w : V // G.Adj b w} := by
    change (G.neighborFinset b).card = Nat.card (G.neighborSet b)
    rw [Nat.card_coe_set_eq]
    symm
    simpa [SimpleGraph.neighborFinset] using
      (Set.ncard_eq_toFinset_card' (G.neighborSet b))
  have hdegN : (G.neighborFinset b).card = 3 := hcard.trans hdegree
  have hdegFilter :
      (Finset.univ.filter (fun w : V => G.Adj b w)).card = 3 := by
    simpa [SimpleGraph.neighborFinset_eq_filter] using hdegN
  exact degree_three_p3_deletion_connected hab hbc hac hdegFilter h3.2


/-- Exact project-model form using the declared `P3Path` and `eraseP3`
definitions. -/
theorem cubic_three_vertex_connected_eraseP3_connected
    {G : SimpleGraph V} [Fintype V] [DecidableRel G.Adj]
    (hC : Cubic G) (h3 : ThreeVertexConnected G) (L : P3Path G) :
    (eraseP3 G L).Connected := by
  simpa [eraseP3] using
    (cubic_three_vertex_connected_p3_deletion_connected hC h3
      L.edge_left L.edge_right L.left_ne_right)


end R03SP06

open CubicP3Partition R03SP06

variable {V : Type} [DecidableEq V]

theorem solution
    {G : SimpleGraph V} [Fintype V]
    (h3 : ThreeVertexConnected G) {A B T : Finset V}
    (hA : A.Nonempty) (hB : B.Nonempty)
    (hAB : Disjoint A B) (hAT : Disjoint A T) (hBT : Disjoint B T)
    (hclosed : ∀ ⦃u v : V⦄, u ∈ A → G.Adj u v → v ∈ A ∪ T)
    (hT : T.card ≤ 2) : False := by
  apply induced_not_connected_of_closed_side hA hB hAB hAT hBT hclosed
  exact h3.2 T hT
