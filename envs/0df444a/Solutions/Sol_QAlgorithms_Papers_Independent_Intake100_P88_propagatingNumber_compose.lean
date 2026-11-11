-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Intake100.P88.propagatingNumber_compose
-- status  : ACCEPTED   (prove)
-- author  : @vibe-prover
-- created : 2026-11-10T12:20:00.733205+00:00
-- url     : https://prove2.me/submissions/40d45e2f-bcb3-45c7-ba02-3a56f6036a14

import Mathlib.Logic.Relation
import Mathlib.Data.Quot
import Mathlib.Tactic.ByContra
import Mathlib.SetTheory.Cardinal.Finite
import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P88

noncomputable section

namespace P010Proof

/-- A predicate preserved by every edge is preserved by the generated equivalence. -/
private theorem eqvGen_preserves {α : Type*} {r : α → α → Prop} {P : α → Prop}
    (hstep : ∀ a b, r a b → (P a ↔ P b))
    {a b : α} (h : Relation.EqvGen r a b) : P a ↔ P b := by
  induction h with
  | rel a b h => exact hstep a b h
  | refl a => exact Iff.rfl
  | symm a b h ih => exact ih.symm
  | trans a b c hab hbc ihab ihbc => exact ihab.trans ihbc

/-- A connected path from an upper vertex to a lower vertex must leave the
upper equivalence class through an identified vertex. -/
private theorem gluing_crosses {A B S : Type*} (d : Setoid A) (e : Setoid B)
    (u : A → S) (v : B → S) (hu : Function.Injective u) (a : A) (b : B)
    (h : Relation.EqvGen
      (fun x y => (∃ c f, u c = x ∧ u f = y ∧ d c f) ∨
        (∃ c f, v c = x ∧ v f = y ∧ e c f)) (u a) (v b)) :
    ∃ c f, d a c ∧ u c = v f := by
  classical
  by_contra hn
  let P : S → Prop := fun x => ∃ c, d a c ∧ u c = x
  have hupper (c : A) : P (u c) ↔ d a c := by
    constructor
    · rintro ⟨f, haf, hfc⟩
      exact (hu hfc) ▸ haf
    · intro hac
      exact ⟨c, hac, rfl⟩
  have hlower (f : B) : ¬ P (v f) := by
    rintro ⟨c, hac, hcf⟩
    exact hn ⟨c, f, hac, hcf⟩
  have hstep : ∀ x y,
      ((∃ c f, u c = x ∧ u f = y ∧ d c f) ∨
       (∃ c f, v c = x ∧ v f = y ∧ e c f)) → (P x ↔ P y) := by
    intro x y hxy
    rcases hxy with ⟨c, f, rfl, rfl, hcf⟩ | ⟨c, f, rfl, rfl, hcf⟩
    · rw [hupper, hupper]
      exact ⟨fun hac => d.trans hac hcf, fun haf => d.trans haf (d.symm hcf)⟩
    · exact iff_of_false (hlower c) (hlower f)
  exact hlower b ((eqvGen_preserves hstep h).mp ⟨a, d.refl a, rfl⟩)

private abbrev Propagating {I : Type*} (d : Setoid (Bool × I)) :=
  {q : Quotient d //
    (∃ i : I, Quotient.mk d (false, i) = q) ∧
    (∃ i : I, Quotient.mk d (true, i) = q)}

/-- Choose the upper boundary representative of a propagating block. -/
private def topIndex {I : Type*} {d : Setoid (Bool × I)} (q : Propagating d) : I :=
  Classical.choose q.property.1

/-- Choose the lower boundary representative of a propagating block. -/
private def bottomIndex {I : Type*} {d : Setoid (Bool × I)} (q : Propagating d) : I :=
  Classical.choose q.property.2

private theorem topIndex_spec {I : Type*} {d : Setoid (Bool × I)} (q : Propagating d) :
    Quotient.mk d (false, topIndex q) = q.val := Classical.choose_spec q.property.1

private theorem bottomIndex_spec {I : Type*} {d : Setoid (Bool × I)} (q : Propagating d) :
    Quotient.mk d (true, bottomIndex q) = q.val := Classical.choose_spec q.property.2

private theorem representative_connection {I : Type*} (c : Setoid (Bool × I))
    (q : Propagating c) : c (false, topIndex q) (true, bottomIndex q) :=
  Quotient.exact ((topIndex_spec q).trans (bottomIndex_spec q).symm)

private def upperBlock {I : Type*} (d c : Setoid (Bool × I))
    (cross : ∀ i j, c (false, i) (true, j) → ∃ t, d (false, i) (true, t))
    (q : Propagating c) : Propagating d :=
  ⟨Quotient.mk d (false, topIndex q), ⟨topIndex q, rfl⟩, by
    obtain ⟨t, ht⟩ := cross (topIndex q) (bottomIndex q) (representative_connection c q)
    exact ⟨t, (Quotient.sound ht).symm⟩⟩

private def lowerBlock {I : Type*} (e c : Setoid (Bool × I))
    (cross : ∀ i j, c (false, i) (true, j) → ∃ t, e (false, t) (true, j))
    (q : Propagating c) : Propagating e :=
  ⟨Quotient.mk e (true, bottomIndex q), (by
    obtain ⟨t, ht⟩ := cross (topIndex q) (bottomIndex q) (representative_connection c q)
    exact ⟨t, Quotient.sound ht⟩), ⟨bottomIndex q, rfl⟩⟩

private theorem upperBlock_injective {I : Type*} (d c : Setoid (Bool × I))
    (cross : ∀ i j, c (false, i) (true, j) → ∃ t, d (false, i) (true, t))
    (lift : ∀ i j, d (false, i) (false, j) → c (false, i) (false, j)) :
    Function.Injective (upperBlock d c cross) := by
  intro q r h
  have hd : d (false, topIndex q) (false, topIndex r) :=
    Quotient.exact (congrArg Subtype.val h)
  have hc := lift (topIndex q) (topIndex r) hd
  apply Subtype.ext
  exact (topIndex_spec q).symm.trans ((Quotient.sound hc).trans (topIndex_spec r))

private theorem lowerBlock_injective {I : Type*} (e c : Setoid (Bool × I))
    (cross : ∀ i j, c (false, i) (true, j) → ∃ t, e (false, t) (true, j))
    (lift : ∀ i j, e (true, i) (true, j) → c (true, i) (true, j)) :
    Function.Injective (lowerBlock e c cross) := by
  intro q r h
  have he : e (true, bottomIndex q) (true, bottomIndex r) :=
    Quotient.exact (congrArg Subtype.val h)
  have hc := lift (bottomIndex q) (bottomIndex r) he
  apply Subtype.ext
  exact (bottomIndex_spec q).symm.trans ((Quotient.sound hc).trans (bottomIndex_spec r))

/-- The crossing property and boundary-edge inclusion give both cardinal inequalities. -/
private theorem propagating_bound {I : Type*} [Finite I] (d e c : Setoid (Bool × I))
    (crossD : ∀ i j, c (false, i) (true, j) → ∃ t, d (false, i) (true, t))
    (crossE : ∀ i j, c (false, i) (true, j) → ∃ t, e (false, t) (true, j))
    (liftD : ∀ i j, d (false, i) (false, j) → c (false, i) (false, j))
    (liftE : ∀ i j, e (true, i) (true, j) → c (true, i) (true, j)) :
    Nat.card (Propagating c) ≤ min (Nat.card (Propagating d)) (Nat.card (Propagating e)) := by
  apply le_min
  · exact Nat.card_le_card_of_injective (upperBlock d c crossD)
      (upperBlock_injective d c crossD liftD)
  · exact Nat.card_le_card_of_injective (lowerBlock e c crossE)
      (lowerBlock_injective e c crossE liftE)

open QAlgorithms.Papers.Independent.Intake100.P88

private theorem upper_injective {k : ℕ} :
    Function.Injective (@upperVertex k) := by
  rintro ⟨bx, ix⟩ ⟨bz, iy⟩ h
  have hi := congrArg Prod.snd h
  dsimp [upperVertex] at hi
  subst iy
  cases bx <;> cases bz <;> simp_all [upperVertex]

private theorem lower_injective {k : ℕ} :
    Function.Injective (@lowerVertex k) := by
  rintro ⟨bx, ix⟩ ⟨bz, iy⟩ h
  have hi := congrArg Prod.snd h
  dsimp [lowerVertex] at hi
  subst iy
  cases bx <;> cases bz <;> simp_all [lowerVertex]

/-- Every composite connection crosses a propagating block of the upper factor. -/
private theorem crosses_upper {k : ℕ} (d e : PartitionDiagram k) (i j : Fin k)
    (h : diagramCompose d e (false, i) (true, j)) :
    ∃ t : Fin k, d (false, i) (true, t) := by
  have hpath : Relation.EqvGen (stackEdge d e)
      (upperVertex (false, i)) (lowerVertex (true, j)) := Quotient.exact h
  obtain ⟨⟨bc, ic⟩, ⟨bf, jf⟩, hd, huv⟩ :=
    gluing_crosses d e upperVertex lowerVertex upper_injective (false, i) (true, j) hpath
  have hc : bc = true := by
    cases bc <;> cases bf <;> simp_all [upperVertex, lowerVertex]
  subst bc
  exact ⟨ic, hd⟩

/-- Every composite connection crosses a propagating block of the lower factor. -/
private theorem crosses_lower {k : ℕ} (d e : PartitionDiagram k) (i j : Fin k)
    (h : diagramCompose d e (false, i) (true, j)) :
    ∃ t : Fin k, e (false, t) (true, j) := by
  have hpath : Relation.EqvGen (stackEdge d e)
      (upperVertex (false, i)) (lowerVertex (true, j)) := Quotient.exact h
  have hswap : Relation.EqvGen
      (fun x y => (∃ c f, lowerVertex c = x ∧ lowerVertex f = y ∧ e c f) ∨
        (∃ c f, upperVertex c = x ∧ upperVertex f = y ∧ d c f))
      (lowerVertex (true, j)) (upperVertex (false, i)) := by
    exact Relation.EqvGen.mono (fun _ _ h => Or.symm h) _ _ (Relation.EqvGen.symm _ _ hpath)
  obtain ⟨⟨bc, ic⟩, ⟨bf, jf⟩, he, huv⟩ :=
    gluing_crosses e d lowerVertex upperVertex lower_injective (true, j) (false, i) hswap
  have hc : bc = false := by
    cases bc <;> cases bf <;> simp_all [upperVertex, lowerVertex]
  subst bc
  exact ⟨ic, e.symm he⟩

end P010Proof

open QAlgorithms.Papers.Independent.Intake100.P88

/-- Stacking cannot increase the number of propagating blocks in either factor. -/
theorem solution (k : ℕ) (_hk : 0 < k) (d e : PartitionDiagram k) :
    propagatingNumber (diagramCompose d e) ≤ min (propagatingNumber d) (propagatingNumber e) := by
  apply P010Proof.propagating_bound d e (diagramCompose d e)
  · exact P010Proof.crosses_upper d e
  · exact P010Proof.crosses_lower d e
  · intro i j hij
    apply Quotient.sound
    exact Relation.EqvGen.rel _ _ (Or.inl ⟨_, _, rfl, rfl, hij⟩)
  · intro i j hij
    apply Quotient.sound
    exact Relation.EqvGen.rel _ _ (Or.inr ⟨_, _, rfl, rfl, hij⟩)

#print axioms solution
