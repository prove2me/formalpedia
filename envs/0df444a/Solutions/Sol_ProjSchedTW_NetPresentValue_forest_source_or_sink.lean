-- Prove2me | solution 1 for ProjSchedTW.NetPresentValue.forest_source_or_sink
-- status  : ACCEPTED   (prove)
-- author  : @ducloc
-- created : 2026-11-17T13:37:50.978985+00:00
-- url     : https://prove2.me/submissions/893d9103-2aa8-4820-b386-72bcfda8e238

import Mathlib

theorem solution {V : Type} [Fintype V] [DecidableEq V] [Nonempty V]
    (A : Finset (V × V)) (hasymm : ∀ a b : V, (a, b) ∈ A → (b, a) ∉ A)
    (hacyc : (SimpleGraph.fromRel (fun a b => (a, b) ∈ A)).IsAcyclic) :
    ∃ v : V,
      ((∀ u, (u, v) ∉ A) ∧ (A.filter (fun e => e.1 = v)).card ≤ 1) ∨
      ((∀ w, (v, w) ∉ A) ∧ (A.filter (fun e => e.2 = v)).card = 1) := by
  classical
  set G : SimpleGraph V := SimpleGraph.fromRel (fun a b => (a, b) ∈ A) with hG
  have hadj : ∀ a b : V, G.Adj a b ↔ a ≠ b ∧ ((a, b) ∈ A ∨ (b, a) ∈ A) := by
    intro a b
    rw [hG]
    exact SimpleGraph.fromRel_adj _ _ _
  obtain ⟨v₀⟩ := ‹Nonempty V›
  let C := G.connectedComponentMk v₀
  have hCtree : C.toSimpleGraph.IsTree := hacyc.isTree_connectedComponent C
  have hv₀ : v₀ ∈ C := SimpleGraph.ConnectedComponent.connectedComponentMk_mem
  by_cases hsub : Subsingleton C
  · have hno_out : ∀ u : V, (v₀, u) ∉ A := by
      intro u hmem
      have hne : v₀ ≠ u := by
        intro h
        have huu : (u, u) ∈ A := by simpa [h] using hmem
        exact hasymm u u huu huu
      have hAdj : G.Adj v₀ u := (hadj v₀ u).mpr ⟨hne, Or.inl hmem⟩
      have huC : u ∈ C := C.mem_supp_of_adj_mem_supp hv₀ hAdj
      have hEq : (⟨u, huC⟩ : C) = ⟨v₀, hv₀⟩ := Subsingleton.elim _ _
      exact hne (congrArg Subtype.val hEq).symm
    have hno_in : ∀ u : V, (u, v₀) ∉ A := by
      intro u hmem
      have hne : u ≠ v₀ := by
        intro h
        have huu : (v₀, v₀) ∈ A := by simpa [h] using hmem
        exact hasymm v₀ v₀ huu huu
      have hAdj : G.Adj u v₀ := (hadj u v₀).mpr ⟨hne, Or.inl hmem⟩
      have huC : u ∈ C := C.mem_supp_of_adj_mem_supp hv₀ hAdj.symm
      have hEq : (⟨u, huC⟩ : C) = ⟨v₀, hv₀⟩ := Subsingleton.elim _ _
      exact hne (congrArg Subtype.val hEq)
    refine ⟨v₀, Or.inl ⟨hno_in, ?_⟩⟩
    have hempty : A.filter (fun e => e.1 = v₀) = ∅ := by
      rw [Finset.filter_eq_empty_iff]
      intro e he he1
      have : (v₀, e.2) ∈ A := by
        rw [← he1]
        exact he
      exact hno_out e.2 this
    rw [hempty]
    simp
  · haveI : Nontrivial C := not_subsingleton_iff_nontrivial.mp hsub
    obtain ⟨u, hu_deg⟩ := hCtree.exists_vert_degree_one_of_nontrivial
    rw [SimpleGraph.degree_eq_one_iff_existsUnique_adj] at hu_deg
    obtain ⟨w, hw_adj, hw_uniq⟩ := hu_deg
    have hwG : G.Adj u.val w.val := (C.toSimpleGraph_adj u.2 w.2).mp hw_adj
    have huniqG : ∀ y : V, G.Adj u.val y → y = w.val := by
      intro y hy
      have hyC : y ∈ C := C.mem_supp_of_adj_mem_supp u.2 hy
      have hcomp : C.toSimpleGraph.Adj u ⟨y, hyC⟩ := (C.toSimpleGraph_adj u.2 hyC).mpr hy
      have hEq := hw_uniq ⟨y, hyC⟩ hcomp
      exact congrArg Subtype.val hEq
    rcases ((hadj u.val w.val).mp hwG).2 with huv | hvu
    · refine ⟨u.val, Or.inl ⟨?_, ?_⟩⟩
      · intro y hy
        have hne : y ≠ u.val := by
          intro h
          have huu : (u.val, u.val) ∈ A := by simpa [h] using hy
          exact hasymm u.val u.val huu huu
        have hAdj : G.Adj y u.val := (hadj y u.val).mpr ⟨hne, Or.inl hy⟩
        have hyw : y = w.val := huniqG y hAdj.symm
        rw [hyw] at hy
        exact hasymm u.val w.val huv hy
      · have hsub' : A.filter (fun e => e.1 = u.val) ⊆ {(u.val, w.val)} := by
          intro e he
          have heA : e ∈ A := (Finset.mem_filter.mp he).1
          have he1 : e.1 = u.val := (Finset.mem_filter.mp he).2
          have hmemA : (u.val, e.2) ∈ A := by
            rw [← he1]
            exact heA
          have hne2 : u.val ≠ e.2 := by
            intro h
            have huu : (u.val, u.val) ∈ A := by simpa [h] using hmemA
            exact hasymm u.val u.val huu huu
          have hadj₂ : G.Adj u.val e.2 := (hadj u.val e.2).mpr ⟨hne2, Or.inl hmemA⟩
          have heq2 : e.2 = w.val := huniqG e.2 hadj₂
          have heq : e = (u.val, w.val) := by
            rw [← he1, ← heq2]
          simp [heq]
        calc (A.filter (fun e => e.1 = u.val)).card
            ≤ ({(u.val, w.val)} : Finset (V × V)).card := Finset.card_le_card hsub'
          _ = 1 := by simp
    · refine ⟨u.val, Or.inr ⟨?_, ?_⟩⟩
      · intro y hy
        have hne : u.val ≠ y := by
          intro h
          have huu : (u.val, u.val) ∈ A := by simpa [h] using hy
          exact hasymm u.val u.val huu huu
        have hAdj : G.Adj u.val y := (hadj u.val y).mpr ⟨hne, Or.inl hy⟩
        have hyw : y = w.val := huniqG y hAdj
        rw [hyw] at hy
        exact hasymm w.val u.val hvu hy
      · have heq : A.filter (fun e => e.2 = u.val) = {(w.val, u.val)} := by
          rw [Finset.eq_singleton_iff_unique_mem]
          constructor
          · exact Finset.mem_filter.mpr ⟨hvu, rfl⟩
          · intro e he
            have heA : e ∈ A := (Finset.mem_filter.mp he).1
            have he2 : e.2 = u.val := (Finset.mem_filter.mp he).2
            have hmemA : (e.1, u.val) ∈ A := by
              rw [← he2]
              exact heA
            have hne1 : u.val ≠ e.1 := by
              intro h
              have huu : (u.val, u.val) ∈ A := by simpa [h] using hmemA
              exact hasymm u.val u.val huu huu
            have hadj₁ : G.Adj u.val e.1 := (hadj u.val e.1).mpr ⟨hne1, Or.inr hmemA⟩
            have heq1 : e.1 = w.val := huniqG e.1 hadj₁
            have heqe : e = (w.val, u.val) := by
              rw [← heq1, ← he2]
            exact heqe
        rw [heq]
        simp
