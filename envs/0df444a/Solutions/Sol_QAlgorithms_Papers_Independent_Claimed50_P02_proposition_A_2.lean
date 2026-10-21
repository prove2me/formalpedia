-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Claimed50.P02.proposition_A_2
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-20T11:11:41.398595+00:00
-- url     : https://prove2.me/submissions/d1d47746-1b6a-4830-82eb-4b9585fc6ea5

import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P02
open QAlgorithms.Papers.Independent.Claimed50.P02

open scoped BigOperators Matrix ComplexConjugate ComplexOrder

open QAlgorithms.Papers.Independent.Information100.P69 (Sites choi)

noncomputable section

section
variable {p q : ℕ} (d : ℕ) (S : Finset (Fin (p+q))) (pi : Diagram p q)

/-- full labelling of endpoints -/
def g58a_L (x y : Remaining S → Fin d) (w : {i : Fin (p+q) // i ∈ S} → Fin d) :
    Bool × Fin (p+q) → Fin d :=
  fun a => if a.1 then joinLabels y w a.2 else joinLabels x w a.2

def g58a_labr (x y : Remaining S → Fin d) : Bool × Remaining S → Fin d :=
  fun a => if a.1 then y a.2 else x a.2

lemma g58a_glueS (i : Fin (p+q)) (hi : i ∈ S) :
    (Quotient.mk (traceConnectivity S pi) (true, i) : Quotient (traceConnectivity S pi)) =
      Quotient.mk (traceConnectivity S pi) (false, i) :=
  Quotient.sound (Relation.EqvGen.symm _ _ (Relation.EqvGen.rel _ _ (Or.inr ⟨i, hi, rfl, rfl⟩)))

lemma g58a_valid_iff (x y : Remaining S → Fin d) (w : {i : Fin (p+q) // i ∈ S} → Fin d) :
    (∀ a b, (traceConnectivity ∅ pi).r a b → g58a_L d S x y w a = g58a_L d S x y w b) ↔
    (∀ a b, (traceConnectivity S pi).r a b → g58a_L d S x y w a = g58a_L d S x y w b) := by
  constructor
  · intro h a b hab
    change Relation.EqvGen _ a b at hab
    induction hab with
    | rel a b hr =>
      rcases hr with hr | ⟨i, hi, rfl, rfl⟩
      · exact h a b (Relation.EqvGen.rel _ _ (Or.inl hr))
      · simp [g58a_L, joinLabels, hi]
    | refl => rfl
    | symm _ _ _ ih => exact ih.symm
    | trans _ _ _ _ _ ih1 ih2 => exact ih1.trans ih2
  · intro h a b hab
    refine h a b (Relation.EqvGen.mono ?_ a b hab)
    rintro u v (h1 | ⟨i, hi, -⟩)
    · exact Or.inl h1
    · exact absurd hi (Finset.notMem_empty i)

def g58a_G (x y : Remaining S → Fin d) :=
  {g : Quotient (traceConnectivity S pi) → Fin d //
    ∀ a : Bool × Remaining S, g (Quotient.mk _ (a.1, a.2.val)) = g58a_labr d S x y a}

lemma g58a_L_retained (x y : Remaining S → Fin d) (w : {i : Fin (p+q) // i ∈ S} → Fin d)
    (a : Bool × Remaining S) : g58a_L d S x y w (a.1, a.2.val) = g58a_labr d S x y a := by
  obtain ⟨b, i, hi⟩ := a
  cases b <;> simp [g58a_L, g58a_labr, joinLabels, hi]

def g58a_eqv1 (x y : Remaining S → Fin d) :
    {w : {i : Fin (p+q) // i ∈ S} → Fin d //
      ∀ a b, (traceConnectivity S pi).r a b → g58a_L d S x y w a = g58a_L d S x y w b} ≃
      g58a_G d S pi x y where
  toFun w := ⟨Quotient.lift (g58a_L d S x y w.1) (fun a b hab => w.2 a b hab),
    fun a => by simp only [Quotient.lift_mk]; exact g58a_L_retained d S x y w.1 a⟩
  invFun g := ⟨fun i => g.1 (Quotient.mk _ (false, i.val)), by
    have key : ∀ e, g58a_L d S x y (fun i => g.1 (Quotient.mk _ (false, i.val))) e =
        g.1 (Quotient.mk _ e) := by
      intro e
      obtain ⟨b, i⟩ := e
      by_cases hi : i ∈ S
      · cases b
        · simp [g58a_L, joinLabels, hi]
        · simp only [g58a_L, joinLabels, hi, dif_pos, if_true]
          rw [g58a_glueS S pi i hi]
      · have := g.2 (b, ⟨i, hi⟩)
        rw [← g58a_L_retained d S x y (fun i => g.1 (Quotient.mk _ (false, i.val)))] at this
        exact this.symm
    intro a b hab
    rw [key, key]
    exact congrArg g.1 (Quotient.sound hab)⟩
  left_inv w := by
    apply Subtype.ext
    funext i
    simp [g58a_L, joinLabels, i.2]
  right_inv g := by
    apply Subtype.ext
    funext C
    induction C using Quotient.ind with
    | _ e =>
      simp only [Quotient.lift_mk]
      obtain ⟨b, i⟩ := e
      by_cases hi : i ∈ S
      · cases b
        · simp [g58a_L, joinLabels, hi]
        · simp only [g58a_L, joinLabels, hi, dif_pos, if_true]
          rw [g58a_glueS S pi i hi]
      · have := g.2 (b, ⟨i, hi⟩)
        rw [← g58a_L_retained d S x y (fun i => g.1 (Quotient.mk _ (false, i.val)))] at this
        exact this.symm

abbrev g58a_K := {C : Quotient (traceConnectivity S pi) //
    ∀ a : Bool × Fin (p+q), Quotient.mk (traceConnectivity S pi) a = C → a.2 ∈ S}

lemma g58a_empty (x y : Remaining S → Fin d)
    (hc : ¬ ∀ a b : Bool × Remaining S, (contractedRelation S pi).r a b →
      g58a_labr d S x y a = g58a_labr d S x y b) : IsEmpty (g58a_G d S pi x y) := by
  refine ⟨fun g => hc fun a b hab => ?_⟩
  rw [← g.2 a, ← g.2 b]
  exact congrArg g.1 (Quotient.sound hab)

noncomputable def g58a_eqv2 (x y : Remaining S → Fin d)
    (hc : ∀ a b : Bool × Remaining S, (contractedRelation S pi).r a b →
      g58a_labr d S x y a = g58a_labr d S x y b) :
    g58a_G d S pi x y ≃ (g58a_K S pi → Fin d) := by
  classical
  have hopen : ∀ C : Quotient (traceConnectivity S pi),
      ¬ (∀ a : Bool × Fin (p+q), Quotient.mk (traceConnectivity S pi) a = C → a.2 ∈ S) →
      ∃ a : Bool × Remaining S, Quotient.mk (traceConnectivity S pi) (a.1, a.2.val) = C := by
    intro C hC
    push Not at hC
    obtain ⟨a, ha, haS⟩ := hC
    exact ⟨(a.1, ⟨a.2, haS⟩), ha⟩
  exact
  { toFun := fun g C => g.1 C.1
    invFun := fun h => ⟨fun C => if hC : (∀ a : Bool × Fin (p+q),
        Quotient.mk (traceConnectivity S pi) a = C → a.2 ∈ S) then h ⟨C, hC⟩
        else g58a_labr d S x y (hopen C hC).choose, by
      intro a
      have hC : ¬ (∀ e : Bool × Fin (p+q), Quotient.mk (traceConnectivity S pi) e =
          Quotient.mk (traceConnectivity S pi) (a.1, a.2.val) → e.2 ∈ S) :=
        fun h => a.2.2 (h _ rfl)
      simp only [dif_neg hC]
      apply hc
      exact Quotient.exact (s := traceConnectivity S pi) ((hopen _ hC).choose_spec)⟩
    left_inv := fun g => by
      apply Subtype.ext
      funext C
      simp only
      split_ifs with hC
      · rfl
      · have := (hopen C hC).choose_spec
        rw [← g.2, this]
    right_inv := fun h => by
      funext C
      simp only [dif_pos C.2] }

lemma g58a_entry (x y : Remaining S → Fin d) :
    matrixPartialTrace S (diagramMatrix d pi) x y =
      ((d : ℂ) ^ closedLoops S pi • relationMatrix d (contractedRelation S pi)) x y := by
  classical
  have h1 : matrixPartialTrace S (diagramMatrix d pi) x y =
      ((Finset.univ.filter fun w : {i : Fin (p+q) // i ∈ S} → Fin d =>
        ∀ a b, (traceConnectivity ∅ pi).r a b → g58a_L d S x y w a = g58a_L d S x y w b).card : ℂ) := by
    simp only [matrixPartialTrace, diagramMatrix, relationMatrix]
    rw [← Finset.sum_boole]
    rfl
  rw [h1]
  simp only [g58a_valid_iff]
  rw [← Fintype.card_subtype, ← Nat.card_eq_fintype_card, Nat.card_congr (g58a_eqv1 d S pi x y)]
  simp only [Matrix.smul_apply, relationMatrix, smul_eq_mul]
  by_cases hc : ∀ a b : Bool × Remaining S, (contractedRelation S pi).r a b →
      g58a_labr d S x y a = g58a_labr d S x y b
  · rw [Nat.card_congr (g58a_eqv2 d S pi x y hc), Nat.card_fun]
    have : (∀ a b : Bool × Remaining S, (contractedRelation S pi).r a b →
        (if a.1 then y a.2 else x a.2) = (if b.1 then y b.2 else x b.2)) := hc
    rw [if_pos this, mul_one, Nat.card_eq_fintype_card (α := Fin d), Fintype.card_fin]
    push_cast
    rfl
  · haveI := g58a_empty d S pi x y hc
    have : ¬ (∀ a b : Bool × Remaining S, (contractedRelation S pi).r a b →
        (if a.1 then y a.2 else x a.2) = (if b.1 then y b.2 else x b.2)) := hc
    rw [if_neg this, mul_zero, Nat.card_of_isEmpty]
    simp

end

theorem solution {d p q : ℕ} (hd : 2 ≤ d) (S : Finset (Fin (p+q))) :
    (∀ z : DiagramSum p q,
      matrixPartialTrace S (diagramAction d z) = relationAction d (diagramPartialTrace d S z)) ∧
    (∀ pi : Diagram p q, matrixPartialTrace S (diagramMatrix d pi) =
      ((d : ℂ) ^ closedLoops S pi) • relationMatrix d (contractedRelation S pi)) := by
  have h2 : ∀ pi : Diagram p q, matrixPartialTrace S (diagramMatrix d pi) =
      ((d : ℂ) ^ closedLoops S pi) • relationMatrix d (contractedRelation S pi) := by
    intro pi; ext x y; exact g58a_entry d S pi x y
  refine ⟨fun z => ?_, h2⟩
  have hlin : ∀ (s : Finset (Diagram p q)) (f : Diagram p q → Matrix (Sites (Fin d) (p+q)) (Sites (Fin d) (p+q)) ℂ),
      matrixPartialTrace S (∑ pi ∈ s, f pi) = ∑ pi ∈ s, matrixPartialTrace S (f pi) := by
    intro s f; ext x y
    simp only [matrixPartialTrace, Matrix.sum_apply]
    rw [Finset.sum_comm]
  have hsm : ∀ (c : ℂ) (M : Matrix (Sites (Fin d) (p+q)) (Sites (Fin d) (p+q)) ℂ),
      matrixPartialTrace S (c • M) = c • matrixPartialTrace S M := by
    intro c M; ext x y
    simp only [matrixPartialTrace, Matrix.smul_apply, smul_eq_mul, Finset.mul_sum]
  classical
  unfold diagramAction diagramPartialTrace
  rw [Finsupp.sum, hlin]
  simp only [hsm, h2]
  unfold relationAction
  rw [Finsupp.sum_sum_index (fun R => by simp) (fun R c1 c2 => by simp [add_smul])]
  simp only [Finsupp.sum_single_index, zero_smul]
  rw [Finsupp.sum]
  refine Finset.sum_congr rfl fun pi _ => ?_
  rw [smul_smul, mul_comm]

end
