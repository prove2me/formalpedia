-- Prove2me | solution 1 for SingleExpBisect.Main.lemma_3_7
-- status  : ACCEPTED   (prove)
-- author  : @Soh Kumabe
-- created : 2026-11-26T08:59:37.191887+00:00
-- url     : https://prove2.me/submissions/4e5f1d34-1fa0-4d34-b71b-16b5c8fd6a67

/- The auxiliary cut and minimizer lemmas below are from Secousses, Prove2Me submission 797eedb1-a223-4590-b528-4b3d16d0ab3c for Lemma 3.8 (Apache-2.0). -/
import Mathlib
import Definitions.Def_SingleExpBisect_Main_NodeData

set_option autoImplicit false

open scoped Classical

open SingleExpBisect.Main

open MinBisectFPT

private lemma mem_cutEdges_mk {n : ℕ} (H : SimpleGraph (Fin n)) (X : Finset (Fin n)) (a b : Fin n) :
    s(a, b) ∈ cutEdges H X ↔ H.Adj a b ∧ ((a ∈ X ∧ b ∉ X) ∨ (b ∈ X ∧ a ∉ X)) := by
  simp only [cutEdges, Finset.mem_filter, Finset.mem_univ, true_and, SimpleGraph.mem_edgeSet,
    Sym2.eq_iff]
  constructor
  · rintro ⟨hadj, u, hu, v, hv, (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)⟩
    · exact ⟨hadj, Or.inl ⟨hu, hv⟩⟩
    · exact ⟨hadj, Or.inr ⟨hu, hv⟩⟩
  · rintro ⟨hadj, (⟨ha, hb⟩ | ⟨hb, ha⟩)⟩
    · exact ⟨hadj, a, ha, b, hb, Or.inl ⟨rfl, rfl⟩⟩
    · exact ⟨hadj, b, hb, a, ha, Or.inr ⟨rfl, rfl⟩⟩

/-- Submodularity of the cut function. -/
private lemma cut_submod {n : ℕ} (G : SimpleGraph (Fin n)) (X Y : Finset (Fin n)) :
    cutSize G (X ∪ Y) + cutSize G (X ∩ Y) ≤ cutSize G X + cutSize G Y := by
  unfold cutSize
  have h1 : cutEdges G (X ∪ Y) ∪ cutEdges G (X ∩ Y) ⊆ cutEdges G X ∪ cutEdges G Y := by
    intro e he
    induction e using Sym2.ind with
    | _ a b =>
      simp only [Finset.mem_union, mem_cutEdges_mk, Finset.mem_inter] at he ⊢
      tauto
  have h2 : cutEdges G (X ∪ Y) ∩ cutEdges G (X ∩ Y) ⊆ cutEdges G X ∩ cutEdges G Y := by
    intro e he
    induction e using Sym2.ind with
    | _ a b =>
      simp only [Finset.mem_union, mem_cutEdges_mk, Finset.mem_inter] at he ⊢
      tauto
  rw [← Finset.card_union_add_card_inter, ← Finset.card_union_add_card_inter (cutEdges G X)]
  exact Nat.add_le_add (Finset.card_le_card h1) (Finset.card_le_card h2)

private lemma mu_le {n : ℕ} (G : SimpleGraph (Fin n)) (W S A : Finset (Fin n)) (h : A ∩ W = S) :
    mu G W S ≤ cutSize G A :=
  Nat.sInf_le ⟨A, h, rfl⟩

private lemma mu_attained {n : ℕ} (G : SimpleGraph (Fin n)) (W S : Finset (Fin n)) (hS : S ⊆ W) :
    ∃ A : Finset (Fin n), A ∩ W = S ∧ cutSize G A = mu G W S :=
  Nat.sInf_mem (s := {c : ℕ | ∃ A : Finset (Fin n), A ∩ W = S ∧ cutSize G A = c})
    ⟨cutSize G S, S, Finset.inter_eq_left.mpr hS, rfl⟩

private lemma union_mem {n : ℕ} (G : SimpleGraph (Fin n)) (W S A B : Finset (Fin n))
    (hA : A ∩ W = S ∧ cutSize G A = mu G W S) (hB : B ∩ W = S ∧ cutSize G B = mu G W S) :
    (A ∪ B) ∩ W = S ∧ cutSize G (A ∪ B) = mu G W S := by
  have e1 : (A ∪ B) ∩ W = S := by rw [Finset.union_inter_distrib_right, hA.1, hB.1, Finset.union_self]
  have e2 : (A ∩ B) ∩ W = S := by
    have : (A ∩ B) ∩ W = (A ∩ W) ∩ (B ∩ W) := by
      ext x; simp only [Finset.mem_inter]; tauto
    rw [this, hA.1, hB.1, Finset.inter_self]
  have := cut_submod G A B
  have := mu_le G W S _ e1
  have := mu_le G W S _ e2
  exact ⟨e1, by omega⟩

private lemma phi_mem {n : ℕ} (G : SimpleGraph (Fin n)) (W S : Finset (Fin n)) (hS : S ⊆ W) :
    Phi G W S ∩ W = S ∧ cutSize G (Phi G W S) = mu G W S := by
  obtain ⟨A0, hA0⟩ := mu_attained G W S hS
  unfold Phi
  have hne : ((Finset.univ : Finset (Finset (Fin n))).filter
      (fun A => A ∩ W = S ∧ cutSize G A = mu G W S)).Nonempty :=
    ⟨A0, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hA0⟩⟩
  rw [← Finset.sup'_eq_sup hne]
  refine Finset.sup'_induction hne id (p := fun X => X ∩ W = S ∧ cutSize G X = mu G W S) ?_ ?_
  · intro a ha b hb
    exact union_mem G W S a b ha hb
  · intro b hb
    exact (Finset.mem_filter.mp hb).2

private lemma le_phi {n : ℕ} (G : SimpleGraph (Fin n)) (W S A : Finset (Fin n))
    (hA : A ∩ W = S ∧ cutSize G A = mu G W S) : A ⊆ Phi G W S := by
  unfold Phi
  exact Finset.le_sup (f := id) (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hA⟩)

theorem solution {n : ℕ} (G : SimpleGraph (Fin n)) (W S : Finset (Fin n)) (hS : S ⊆ W) :
    IsGreatest {A : Finset (Fin n) | A ∩ W = S ∧ cutSize G A = mu G W S} (Phi G W S) := by
  exact ⟨phi_mem G W S hS, fun A hA => le_phi G W S A hA⟩
