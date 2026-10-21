-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Claimed50.P02.proposition_A_1
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-20T11:08:15.201773+00:00
-- url     : https://prove2.me/submissions/b46a2497-5e74-4708-ab17-9a9085d66caf

import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P02
open QAlgorithms.Papers.Independent.Claimed50.P02

open scoped BigOperators Matrix ComplexConjugate ComplexOrder

open QAlgorithms.Papers.Independent.Information100.P69 (Sites choi)

noncomputable section

lemma g58a_mono {p q : ℕ} (pi : Diagram p q) (a b : Bool × Fin (p+q))
    (h : (traceConnectivity ∅ pi).r a b) : (traceConnectivity Finset.univ pi).r a b := by
  refine Relation.EqvGen.mono ?_ a b h
  rintro x y (h1 | ⟨i, hi, -⟩)
  · exact Or.inl h1
  · exact absurd hi (Finset.notMem_empty i)

lemma g58a_glue {p q : ℕ} (pi : Diagram p q) (a : Bool × Fin (p+q)) :
    (Quotient.mk (traceConnectivity Finset.univ pi) a : Quotient (traceConnectivity Finset.univ pi)) =
      Quotient.mk (traceConnectivity Finset.univ pi) (false, a.2) := by
  obtain ⟨b, i⟩ := a
  cases b
  · rfl
  · apply Quotient.sound
    exact Relation.EqvGen.symm _ _ (Relation.EqvGen.rel _ _ (Or.inr ⟨i, Finset.mem_univ _, rfl, rfl⟩))

def g58a_equiv (d : ℕ) {p q : ℕ} (pi : Diagram p q) :
    {x : Fin (p+q) → Fin d // ∀ a b, (traceConnectivity ∅ pi).r a b → x a.2 = x b.2} ≃
      (Quotient (traceConnectivity Finset.univ pi) → Fin d) where
  toFun x := Quotient.lift (fun a => x.1 a.2) (by
    intro a b hab
    change Relation.EqvGen _ a b at hab
    induction hab with
    | rel a b h =>
      rcases h with h | ⟨i, -, rfl, rfl⟩
      · exact x.2 a b (Relation.EqvGen.rel _ _ (Or.inl h))
      · rfl
    | refl => rfl
    | symm _ _ _ ih => exact ih.symm
    | trans _ _ _ _ _ ih1 ih2 => exact ih1.trans ih2)
  invFun g := ⟨fun i => g (Quotient.mk _ (false, i)), by
    intro a b hab
    simp only
    rw [← g58a_glue, ← g58a_glue]
    congr 1
    exact Quotient.sound (g58a_mono pi a b hab)⟩
  left_inv x := by
    ext i; rfl
  right_inv g := by
    funext c
    induction c using Quotient.ind with
    | _ a =>
      simp only [Quotient.lift_mk]
      rw [← g58a_glue]

lemma g58a_trace (d : ℕ) {p q : ℕ} (pi : Diagram p q) :
    Matrix.trace (diagramMatrix d pi) = (d : ℂ) ^ closedLoops Finset.univ pi := by
  classical
  have h1 : Matrix.trace (diagramMatrix d pi) =
      ((Finset.univ.filter fun x : Fin (p+q) → Fin d =>
        ∀ a b, (traceConnectivity ∅ pi).r a b → x a.2 = x b.2).card : ℂ) := by
    simp only [Matrix.trace, Matrix.diag, diagramMatrix, relationMatrix, ite_self]
    rw [Finset.sum_boole]
  rw [h1]
  have h2 : (Finset.univ.filter fun x : Fin (p+q) → Fin d =>
        ∀ a b, (traceConnectivity ∅ pi).r a b → x a.2 = x b.2).card =
      d ^ closedLoops Finset.univ pi := by
    rw [← Fintype.card_subtype, ← Nat.card_eq_fintype_card, Nat.card_congr (g58a_equiv d pi),
      Nat.card_fun, Nat.card_eq_fintype_card (α := Fin d), Fintype.card_fin]
    congr 1
    unfold closedLoops
    exact (Nat.card_congr (Equiv.subtypeUnivEquiv (fun C => by
      intro a _; exact Finset.mem_univ _))).symm
  rw [h2]; push_cast; rfl

theorem solution {d p q : ℕ} (hd : 2 ≤ d) :
    (∀ z : DiagramSum p q, Matrix.trace (diagramAction d z) = diagramTrace d z) ∧
    (∀ pi : Diagram p q,
      Matrix.trace (diagramMatrix d pi) = (d : ℂ) ^ closedLoops Finset.univ pi) := by
  refine ⟨fun z => ?_, fun pi => g58a_trace d pi⟩
  unfold diagramAction diagramTrace Finsupp.sum
  rw [Matrix.trace_sum]
  refine Finset.sum_congr rfl fun pi _ => ?_
  rw [Matrix.trace_smul, g58a_trace, smul_eq_mul]

end
