-- Prove2me | solution 1 for Relabel.orelabel_reduced
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T07:08:59.623985+00:00
-- url     : https://prove2.me/submissions/02bf7c9b-6340-4af5-81b7-a57e3c025c3d

import Definitions.Def_Bdd_Basic
import Definitions.Def_Bdd_Relabel
import Theorems.Thm_DecisionTree_relabel_injective
import Theorems.Thm_Nary_restrict_const
import Theorems.Thm_OBdd_toTree_usesVar
import Theorems.Thm_P2M_OBdd_toTree_terminal__6f80b985dd51
attribute [local simp] Nary.restrict_const


section
set_option autoImplicit true
attribute [local implicit_reducible] OBdd Bdd.Ordered Bdd.RelevantMayPrecede
namespace Relabel
attribute [local implicit_reducible] relabel relabel_heap relabel_node
attribute [local implicit_reducible] orelabel
private lemma brelabel_low {B : Bdd n m} {o : Bdd.Ordered B} {h : B.root = .node j} {f : Nat → Nat} (hf : ∀ i : Fin n, f i < f n)
    (hu : ∀ i i' : Fin n, i < i' → B.usesVar i → B.usesVar i' → f i < f i') :
    (OBdd.low ⟨relabel hf B, relabel_ordered hu o⟩ h) =
      ⟨relabel hf (OBdd.low ⟨B, o⟩ h).1, relabel_ordered (fun i i' hii' hi hi' ↦ hu i i' hii' (OBdd.usesVar_of_low_usesVar hi) (OBdd.usesVar_of_low_usesVar hi')) (OBdd.low ⟨B, o⟩ h).2⟩ := by
  exact orelabel_low (O := ⟨B, o⟩) hf hu
private lemma brelabel_high {B : Bdd n m} {o : Bdd.Ordered B} {h : B.root = .node j} {f : Nat → Nat} (hf : ∀ i : Fin n, f i < f n)
    (hu : ∀ i i' : Fin n, i < i' → B.usesVar i → B.usesVar i' → f i < f i') :
    (OBdd.high ⟨relabel hf B, relabel_ordered hu o⟩ h) =
      ⟨relabel hf (OBdd.high ⟨B, o⟩ h).1, relabel_ordered (fun i i' hii' hi hi' ↦ hu i i' hii' (OBdd.usesVar_of_high_usesVar hi) (OBdd.usesVar_of_high_usesVar hi')) (OBdd.high ⟨B, o⟩ h).2⟩ := by
  exact orelabel_high (O := ⟨B, o⟩) hf hu
private lemma relabel_preserves_noRedundancy {n m : Nat} {f : Nat → Nat} {hf : ∀ i : Fin n, f i < f n} {B : Bdd n m} : B.NoRedundancy → (relabel hf B).NoRedundancy := by
  rintro hnr ⟨p, hp⟩ contra
  simp +instances only at contra
  cases p_def : p with
  | terminal _ =>
    cases contra with
    | red _ => contradiction
  | node j =>
    rw [p_def] at contra
    cases contra with
    | red red =>
      simp +instances only [relabel, relabel_heap, Fin.getElem_fin] at red
      apply hnr ⟨p, relabel_reachable_iff.mpr hp⟩
      simp_rw [p_def]
      constructor
      simp_all +instances only [Vector.getElem_map, Fin.getElem_fin]
      simp +instances only [relabel_node] at red
      exact red
private lemma relabel_toTree_relabel (O : OBdd n m) {f : Nat → Nat} (hf : ∀ i : Fin n, f i < f n)
    (hu : ∀ i i' : Fin n, i < i' → O.1.usesVar i → O.1.usesVar i' → f i < f i') :
    OBdd.toTree (orelabel O hf hu) = DecisionTree.relabel hf (OBdd.toTree O) := by
  simp +instances only [orelabel]
  cases O_root_def : O.1.root with
  | terminal _ =>
    simp +instances only [relabel]
    rw [OBdd.toTree_terminal' O_root_def]
    simp_rw [O_root_def]
    rw [OBdd.toTree_terminal]
    simp +instances [DecisionTree.relabel]
  | node _ =>
    rw [OBdd.toTree_node O_root_def]
    rw [OBdd.toTree_node (O := ⟨relabel hf O.1, relabel_ordered hu O.2⟩) O_root_def]
    simp +instances only [Fin.getElem_fin]
    congr 1
    · simp +instances only [relabel, relabel_heap, Vector.getElem_map, relabel_node, Fin.eta,
      Bdd.Ordered.eq_1, Fin.mk.injEq]
    · have := relabel_toTree_relabel (O := (O.low O_root_def)) hf (fun i i' hii' hi hi' ↦ hu i i' hii' (OBdd.usesVar_of_low_usesVar hi) (OBdd.usesVar_of_low_usesVar hi'))
      rw [← orelabel_low] at this
      exact this
    · have := relabel_toTree_relabel (O := (O.high O_root_def)) hf (fun i i' hii' hi hi' ↦ hu i i' hii' (OBdd.usesVar_of_high_usesVar hi) (OBdd.usesVar_of_high_usesVar hi'))
      rw [← orelabel_high] at this
      exact this
termination_by O
decreasing_by all_goals first | exact oedge_of_low | exact oedge_of_high | decreasing_tactic
private lemma relabel_toTree_relabel' {B : Bdd n m} {o : B.Ordered} {f : Nat → Nat} (hf : ∀ i : Fin n, f i < f n)
    (hu : ∀ i i' : Fin n, i < i' → B.usesVar i → B.usesVar i' → f i < f i') :
    OBdd.toTree ⟨relabel hf B, relabel_ordered hu o⟩ = DecisionTree.relabel hf (OBdd.toTree ⟨B, o⟩) := relabel_toTree_relabel ⟨B, o⟩ hf hu
private lemma orelabel_preserves_similarRP {O : OBdd n m} {f : Nat → Nat} {hf : ∀ i : Fin n, f i < f n}
    {hu : ∀ i i' : Fin n, i < i' → O.1.usesVar i → O.1.usesVar i' → f i < f i'}
    {p q : Pointer m}
    {hp : Pointer.Reachable (orelabel O hf hu).1.heap (orelabel O hf hu).1.root p}
    {hq : Pointer.Reachable (orelabel O hf hu).1.heap (orelabel O hf hu).1.root q} :
    (orelabel O hf hu).SimilarRP ⟨p, hp⟩ ⟨q, hq⟩ → O.SimilarRP ⟨p, relabel_reachable_iff.mpr hp⟩ ⟨q, relabel_reachable_iff.mpr hq⟩ := by
  intro sim
  simp +instances only [OBdd.SimilarRP, OBdd.Similar, OBdd.HSimilar] at sim
  simp +instances only [OBdd.SimilarRP, OBdd.Similar, OBdd.HSimilar]
  generalize_proofs at sim ⊢
  cases p with
  | terminal _ =>
    cases q with
    | terminal _ =>
      rw [OBdd.toTree_terminal, OBdd.toTree_terminal] at sim ⊢
      injection sim with h
      cases h
      rfl
    | node _ =>
      rw [OBdd.toTree_terminal] at sim
      rw [OBdd.toTree_node rfl] at sim
      contradiction
  | node j =>
    cases q with
    | terminal _ =>
      rw [OBdd.toTree_terminal] at sim
      rw [OBdd.toTree_node rfl] at sim
      contradiction
    | node i =>
      conv at sim =>
        lhs
        rw [OBdd.toTree_node rfl]
      conv at sim =>
        rhs
        rw [OBdd.toTree_node rfl]
      injection sim with ha hb hc
      simp +instances only [Fin.getElem_fin] at ha
      simp +instances only [orelabel, relabel, relabel_heap, Vector.getElem_map, relabel_node, Fin.eta,
        Fin.mk.injEq] at ha
      conv =>
        lhs
        rw [OBdd.toTree_node rfl]
      conv =>
        rhs
        rw [OBdd.toTree_node rfl]
      have help1 : ∀ x, Bdd.usesVar { heap := O.1.heap, root := Pointer.node j } x → O.1.usesVar x := by
          rintro x ⟨jj, h1, h2⟩
          use jj
          constructor
          · trans Pointer.node j
            · exact relabel_reachable_iff.mpr hp
            · exact h1
          · exact h2
      have help2 : ∀ x, Bdd.usesVar { heap := O.1.heap, root := Pointer.node i } x → O.1.usesVar x := by
          rintro x ⟨jj, h1, h2⟩
          use jj
          constructor
          · trans Pointer.node i
            · exact relabel_reachable_iff.mpr hq
            · exact h1
          · exact h2
      congr 1
      · simp +instances only
        by_contra c
        apply ne_iff_lt_or_gt.mp at c
        cases c with
        | inl h => exact (ne_iff_lt_or_gt.mpr (.inl (hu O.1.heap[j].var O.1.heap[i].var h ⟨j, relabel_reachable_iff.mpr hp, rfl⟩ ⟨i, relabel_reachable_iff.mpr hq, rfl⟩))) ha
        | inr h => exact (ne_iff_lt_or_gt.mpr (.inr (hu O.1.heap[i].var O.1.heap[j].var h ⟨i, relabel_reachable_iff.mpr hq, rfl⟩ ⟨j, relabel_reachable_iff.mpr hp, rfl⟩))) ha
      · simp +instances only [orelabel] at hb
        simp +instances only [relabel] at hb
        simp_rw [← relabel.eq_1] at hb
        conv at hb =>
          lhs
          rw [brelabel_low (h := rfl) (o := Bdd.ordered_of_reachable (relabel_reachable_iff.mpr hp)) hf (by simp_all +instances)]
        conv at hb =>
          rhs
          rw [brelabel_low (h := rfl) (o := Bdd.ordered_of_reachable (relabel_reachable_iff.mpr hq)) hf (by simp_all +instances)]
        simp +instances only [OBdd.low] at hb
        simp +instances only [OBdd.low]
        have helplj : ∀ x, Bdd.usesVar (({ heap := O.1.heap, root := Pointer.node j } : Bdd n m).low rfl) x → O.1.usesVar x := by
          rintro _ hx
          apply help1
          apply Bdd.usesVar_of_low_usesVar hx
        have helpli : ∀ x, Bdd.usesVar (({ heap := O.1.heap, root := Pointer.node i } : Bdd n m).low rfl) x → O.1.usesVar x := by
          rintro _ hx
          apply help2
          apply Bdd.usesVar_of_low_usesVar hx
        conv at hb =>
          lhs
          rw [relabel_toTree_relabel' (o := (by apply Bdd.low_ordered; exact Bdd.ordered_of_reachable (relabel_reachable_iff.mpr hp))) hf (by simp_all +instances)]
        conv at hb =>
          rhs
          rw [relabel_toTree_relabel' (o := (by apply Bdd.low_ordered; exact Bdd.ordered_of_reachable (relabel_reachable_iff.mpr hq))) hf (by simp_all +instances)]
        rw [DecisionTree.relabel_injective hb]
        intro ii ii' hii hii' hfi
        rw [← OBdd.toTree_usesVar] at hii hii'
        contrapose hfi
        apply ne_iff_lt_or_gt.mpr
        cases ne_iff_lt_or_gt.mp hfi with
        | inl hfi =>
          left
          apply hu
          · exact hfi
          · apply help1
            apply Bdd.usesVar_of_low_usesVar
            exact hii
            rfl
          · apply help2
            apply Bdd.usesVar_of_low_usesVar
            exact hii'
            rfl
        | inr hfi =>
          right
          apply hu
          · exact hfi
          · apply help2
            apply Bdd.usesVar_of_low_usesVar
            exact hii'
            rfl
          · apply help1
            apply Bdd.usesVar_of_low_usesVar
            exact hii
            rfl
      · simp +instances only [orelabel] at hc
        simp +instances only [relabel] at hc
        simp_rw [← relabel.eq_1] at hc
        conv at hc =>
          lhs
          rw [brelabel_high (h := rfl) (o := Bdd.ordered_of_reachable (relabel_reachable_iff.mpr hp)) hf (by simp_all +instances)]
        conv at hc =>
          rhs
          rw [brelabel_high (h := rfl) (o := Bdd.ordered_of_reachable (relabel_reachable_iff.mpr hq)) hf (by simp_all +instances)]
        simp +instances only [OBdd.high] at hc
        simp +instances only [OBdd.high]
        have helphj : ∀ x, Bdd.usesVar (({ heap := O.1.heap, root := Pointer.node j } : Bdd n m).high rfl) x → O.1.usesVar x := by
          rintro _ hx
          apply help1
          apply Bdd.usesVar_of_high_usesVar hx
        have helphi : ∀ x, Bdd.usesVar (({ heap := O.1.heap, root := Pointer.node i } : Bdd n m).high rfl) x → O.1.usesVar x := by
          rintro _ hx
          apply help2
          apply Bdd.usesVar_of_high_usesVar hx
        conv at hc =>
          lhs
          rw [relabel_toTree_relabel' (o := (by apply Bdd.high_ordered; exact Bdd.ordered_of_reachable (relabel_reachable_iff.mpr hp))) hf (by simp_all +instances)]
        conv at hc =>
          rhs
          rw [relabel_toTree_relabel' (o := (by apply Bdd.high_ordered; exact Bdd.ordered_of_reachable (relabel_reachable_iff.mpr hq))) hf (by simp_all +instances)]
        rw [DecisionTree.relabel_injective hc]
        intro ii ii' hii hii' hfi
        rw [← OBdd.toTree_usesVar] at hii hii'
        contrapose hfi
        apply ne_iff_lt_or_gt.mpr
        cases ne_iff_lt_or_gt.mp hfi with
        | inl hfi =>
          left
          apply hu
          · exact hfi
          · apply help1
            apply Bdd.usesVar_of_high_usesVar
            exact hii
            rfl
          · apply help2
            apply Bdd.usesVar_of_high_usesVar
            exact hii'
            rfl
        | inr hfi =>
          right
          apply hu
          · exact hfi
          · apply help2
            apply Bdd.usesVar_of_high_usesVar
            exact hii'
            rfl
          · apply help1
            apply Bdd.usesVar_of_high_usesVar
            exact hii
            rfl
end Relabel
end

set_option autoImplicit true
attribute [local implicit_reducible] OBdd Bdd.Ordered Bdd.RelevantMayPrecede
open Relabel
attribute [local implicit_reducible] relabel relabel_heap relabel_node
attribute [local implicit_reducible] orelabel
namespace Relabel
theorem _root_.solution {O : OBdd n m} {f : Nat → Nat} {hf : ∀ i : Fin n, f i < f n}
    {hu : ∀ i i' : Fin n, i < i' → O.1.usesVar i → O.1.usesVar i' → f i < f i'} :
    O.Reduced → (orelabel O hf hu).Reduced := by
  rintro ⟨r1, r2⟩
  constructor
  · exact relabel_preserves_noRedundancy r1
  · rintro _ _ sim
    exact r2 (orelabel_preserves_similarRP sim)
end Relabel
