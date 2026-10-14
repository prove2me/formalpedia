-- Prove2me | solution 1 for SingleMachinePrec.IntervalReduction.claim_1
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-13T03:32:17.803685+00:00
-- url     : https://prove2.me/submissions/cc5ab70e-c167-4fba-ae7a-7d365dd17996

import Mathlib
import Definitions.Def_SingleMachinePrec_IntervalReduction_TreeLayout



namespace SingleMachinePrec.IntervalReduction

variable {N : ℕ} {G : SimpleGraph (Fin N)}

def GPVertex.equivSum (L : TreeLayout G) :
    GPVertex L ≃ Fin N ⊕ Fin N ⊕ Fin N ⊕ NonTreeEdge L ⊕ NonTreeEdge L where
  toFun
    | .v i => .inl i
    | .u1 i => .inr (.inl i)
    | .u2 i => .inr (.inr (.inl i))
    | .e1 q => .inr (.inr (.inr (.inl q)))
    | .e2 q => .inr (.inr (.inr (.inr q)))
  invFun
    | .inl i => .v i
    | .inr (.inl i) => .u1 i
    | .inr (.inr (.inl i)) => .u2 i
    | .inr (.inr (.inr (.inl q))) => .e1 q
    | .inr (.inr (.inr (.inr q))) => .e2 q
  left_inv x := by cases x <;> rfl
  right_inv x := by rcases x with i | i | i | q | q <;> rfl

noncomputable instance GPVertex.instFintype (L : TreeLayout G) : Fintype (GPVertex L) :=
  Fintype.ofEquiv _ (GPVertex.equivSum L).symm

lemma card_dec (L : TreeLayout G) (C : Finset (GPVertex L)) :
    C.card = (Finset.univ.filter (fun i : Fin N => GPVertex.v i ∈ C)).card
      + (Finset.univ.filter (fun i : Fin N => GPVertex.u1 i ∈ C)).card
      + (Finset.univ.filter (fun i : Fin N => GPVertex.u2 i ∈ C)).card
      + (Finset.univ.filter (fun q : NonTreeEdge L => GPVertex.e1 q ∈ C)).card
      + (Finset.univ.filter (fun q : NonTreeEdge L => GPVertex.e2 q ∈ C)).card := by
  have h1 : C.card = ∑ x : GPVertex L, if x ∈ C then 1 else 0 := by
    rw [← Finset.card_filter]; congr 1; ext x; simp
  rw [h1, Fintype.sum_equiv (GPVertex.equivSum L) _ (fun s => if (GPVertex.equivSum L).symm s ∈ C then 1 else 0)
    (by intro x; simp)]
  simp only [Fintype.sum_sum_type, Finset.card_filter]
  simp only [GPVertex.equivSum, Equiv.coe_fn_symm_mk, add_assoc]
  congr!

open Classical in
lemma cl1_up (L : TreeLayout G) (C0 : Finset (Fin N)) (hC0 : G.IsVertexCover (C0 : Set (Fin N))) :
    ∃ C' : Finset (GPVertex L), (GPrime L).IsVertexCover (C' : Set (GPVertex L)) ∧
      C'.card = C0.card + N + Fintype.card (NonTreeEdge L) := by
  let P : GPVertex L → Prop := fun x => match x with
    | .v i => i ∈ C0
    | .u2 i => i ∈ C0
    | .u1 i => i ∉ C0
    | .e1 q => q.1.2 ∈ C0
    | .e2 q => q.1.2 ∉ C0
  refine ⟨Finset.univ.filter P, ?_, ?_⟩
  · intro x y hxy
    rw [GPrime, SimpleGraph.fromRel_adj] at hxy
    obtain ⟨hne, h⟩ := hxy
    simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq]
    rcases h with h | h <;> cases x <;> cases y <;> simp only [gpRel] at h <;> simp only [P]
    all_goals first
      | exact hC0 (L.par_adj _ _ h)
      | exact (hC0 (L.par_adj _ _ h)).symm
      | (subst h; tauto)
      | (subst h; exact hC0 (‹NonTreeEdge L›).2.2.1)
      | (subst h; exact (hC0 (‹NonTreeEdge L›).2.2.1).symm)
  · rw [card_dec]
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, P]
    have h1 : (Finset.univ.filter (fun i : Fin N => i ∈ C0)) = C0 := by ext; simp
    have h2 := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (Fin N)))
      (fun i : Fin N => i ∈ C0)
    have h3 := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (NonTreeEdge L)))
      (fun q : NonTreeEdge L => q.1.2 ∈ C0)
    rw [h1] at h2 ⊢
    simp only [Finset.card_univ, Fintype.card_fin] at h2 h3
    omega

open Classical in
lemma cl1_low (L : TreeLayout G) (C' : Finset (GPVertex L))
    (hC' : (GPrime L).IsVertexCover (C' : Set (GPVertex L))) :
    ∃ C0 : Finset (Fin N), G.IsVertexCover (C0 : Set (Fin N)) ∧
      C0.card + N + Fintype.card (NonTreeEdge L) ≤ C'.card := by
  have hadj : ∀ x y, gpRel L x y → x ∈ C' ∨ y ∈ C' := by
    intro x y h
    have : (GPrime L).Adj x y := by
      rw [GPrime, SimpleGraph.fromRel_adj]
      refine ⟨?_, Or.inl h⟩
      rintro rfl
      cases x <;> simp only [gpRel] at h
      exact lt_irrefl _ (L.par_lt _ _ h)
    exact hC' this
  set A : Finset (Fin N) := Finset.univ.filter (fun i => GPVertex.v i ∈ C') with hA
  set B : Finset (Fin N) := Finset.univ.filter (fun i => GPVertex.u1 i ∈ C' ∧ GPVertex.u2 i ∈ C') with hB
  set Q2 : Finset (NonTreeEdge L) :=
    Finset.univ.filter (fun q => GPVertex.e1 q ∈ C' ∧ GPVertex.e2 q ∈ C') with hQ2
  refine ⟨A ∪ B ∪ Q2.image (fun q => q.1.1), ?_, ?_⟩
  · have key : ∀ a b, G.Adj a b → a < b → a ∈ A ∪ B ∪ Q2.image (fun q => q.1.1) ∨
        b ∈ A ∪ B ∪ Q2.image (fun q => q.1.1) := by
      intro a b hab hlt
      by_cases hp : L.par b = some a
      · rcases hadj (.v a) (.v b) hp with h | h
        · left; simp [hA, h]
        · right; simp [hA, h]
      · let q : NonTreeEdge L := ⟨(a, b), hlt, hab, hp⟩
        by_contra hcon
        push_neg at hcon
        obtain ⟨ha, hb⟩ := hcon
        have h1 : GPVertex.v a ∉ C' := fun h => ha (by simp [hA, h])
        have h2 : GPVertex.v b ∉ C' := fun h => hb (by simp [hA, h])
        have h3 : ¬ (GPVertex.e1 q ∈ C' ∧ GPVertex.e2 q ∈ C') := fun h =>
          ha (by simp only [Finset.mem_union, Finset.mem_image]; right; exact ⟨q, by simp [hQ2, h], rfl⟩)
        have h4 : ¬ (GPVertex.u1 b ∈ C' ∧ GPVertex.u2 b ∈ C') := fun h =>
          hb (by simp [hB, h])
        have e1 : GPVertex.e1 q ∈ C' := by
          rcases hadj (.v a) (.e1 q) rfl with h | h
          · exact absurd h h1
          · exact h
        have e2 : GPVertex.e2 q ∉ C' := fun h => h3 ⟨e1, h⟩
        have e3 : GPVertex.u2 b ∈ C' := by
          rcases hadj (.e2 q) (.u2 b) rfl with h | h
          · exact absurd h e2
          · exact h
        have e4 : GPVertex.u1 b ∉ C' := fun h => h4 ⟨h, e3⟩
        rcases hadj (.u1 b) (.v b) rfl with h | h
        · exact e4 h
        · exact h2 h
    intro a b hab
    rcases lt_or_gt_of_ne hab.ne with h | h
    · exact key a b hab h
    · exact (key b a hab.symm h).symm
  · have hc := card_dec L C'
    have hU : (Finset.univ.filter (fun i : Fin N => GPVertex.u1 i ∈ C')).card +
        (Finset.univ.filter (fun i : Fin N => GPVertex.u2 i ∈ C')).card = N + B.card := by
      have := Finset.card_union_add_card_inter (Finset.univ.filter (fun i : Fin N => GPVertex.u1 i ∈ C'))
        (Finset.univ.filter (fun i : Fin N => GPVertex.u2 i ∈ C'))
      have hu : (Finset.univ.filter (fun i : Fin N => GPVertex.u1 i ∈ C')) ∪
          (Finset.univ.filter (fun i : Fin N => GPVertex.u2 i ∈ C')) = Finset.univ := by
        ext i
        simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and, iff_true]
        rcases hadj (.u2 i) (.u1 i) rfl with h | h
        · right; exact h
        · left; exact h
      have hi : (Finset.univ.filter (fun i : Fin N => GPVertex.u1 i ∈ C')) ∩
          (Finset.univ.filter (fun i : Fin N => GPVertex.u2 i ∈ C')) = B := by
        ext i; simp [hB]
      rw [hu, hi] at this
      simp only [Finset.card_univ, Fintype.card_fin] at this
      omega
    have hE : (Finset.univ.filter (fun q : NonTreeEdge L => GPVertex.e1 q ∈ C')).card +
        (Finset.univ.filter (fun q : NonTreeEdge L => GPVertex.e2 q ∈ C')).card =
        Fintype.card (NonTreeEdge L) + Q2.card := by
      have := Finset.card_union_add_card_inter (Finset.univ.filter (fun q : NonTreeEdge L => GPVertex.e1 q ∈ C'))
        (Finset.univ.filter (fun q : NonTreeEdge L => GPVertex.e2 q ∈ C'))
      have hu : (Finset.univ.filter (fun q : NonTreeEdge L => GPVertex.e1 q ∈ C')) ∪
          (Finset.univ.filter (fun q : NonTreeEdge L => GPVertex.e2 q ∈ C')) = Finset.univ := by
        ext q
        simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and, iff_true]
        exact hadj (.e1 q) (.e2 q) rfl
      have hi : (Finset.univ.filter (fun q : NonTreeEdge L => GPVertex.e1 q ∈ C')) ∩
          (Finset.univ.filter (fun q : NonTreeEdge L => GPVertex.e2 q ∈ C')) = Q2 := by
        ext q; simp [hQ2]
      rw [hu, hi] at this
      simp only [Finset.card_univ] at this
      omega
    have hAc : A.card = (Finset.univ.filter (fun i : Fin N => GPVertex.v i ∈ C')).card := rfl
    have h1 : (A ∪ B ∪ Q2.image (fun q => q.1.1)).card ≤ A.card + B.card + Q2.card :=
      (Finset.card_union_le _ _).trans
        (add_le_add (Finset.card_union_le _ _) Finset.card_image_le)
    omega

lemma vc_exists' {V : Type*} [Finite V] (H : SimpleGraph V) :
    ∃ D : Finset V, H.IsVertexCover (D : Set V) ∧ (D.card : ℕ∞) = H.vertexCoverNum := by
  obtain ⟨s, hs1, hs2⟩ := SimpleGraph.vertexCoverNum_exists H
  refine ⟨(Set.toFinite s).toFinset, by simpa using hs2, ?_⟩
  rw [← hs1, ← Set.encard_coe_eq_coe_finsetCard]; simp

lemma vc_le_card' {V : Type*} (H : SimpleGraph V) (D : Finset V) (hD : H.IsVertexCover (D : Set V)) :
    H.vertexCoverNum ≤ (D.card : ℕ∞) := by
  have := hD.vertexCoverNum_le
  rwa [Set.encard_coe_eq_coe_finsetCard] at this

theorem claim1_core {N : ℕ} (G : SimpleGraph (Fin N)) (L : TreeLayout G) :
    (GPrime L).vertexCoverNum =
      G.vertexCoverNum + (N : ℕ∞) + (Fintype.card (NonTreeEdge L) : ℕ∞) := by
  obtain ⟨C0, hC0, hC0c⟩ := vc_exists' G
  obtain ⟨C1, hC1, hC1c⟩ := vc_exists' (GPrime L)
  obtain ⟨C', hC', hC'c⟩ := cl1_up L C0 hC0
  obtain ⟨C2, hC2, hC2c⟩ := cl1_low L C1 hC1
  have h1 : (GPrime L).vertexCoverNum ≤ (C'.card : ℕ∞) := vc_le_card' _ _ hC'
  have h2 : G.vertexCoverNum ≤ (C2.card : ℕ∞) := vc_le_card' _ _ hC2
  rw [← hC0c]
  apply le_antisymm
  · rw [hC'c] at h1; exact_mod_cast h1
  · rw [← hC1c]
    have : C0.card ≤ C2.card := by
      have := h2; rw [← hC0c] at this; exact_mod_cast this
    exact_mod_cast (by omega : C0.card + N + Fintype.card (NonTreeEdge L) ≤ C1.card)

end SingleMachinePrec.IntervalReduction

open SingleMachinePrec.IntervalReduction


theorem solution {N : ℕ} (G : SimpleGraph (Fin N)) (L : TreeLayout G) :
    (GPrime L).vertexCoverNum =
      G.vertexCoverNum + (N : ℕ∞) + (Fintype.card (NonTreeEdge L) : ℕ∞) := by
  exact claim1_core G L
