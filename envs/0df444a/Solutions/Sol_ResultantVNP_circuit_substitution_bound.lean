-- Prove2me | solution 1 for ResultantVNP.circuit_substitution_bound
-- status  : ACCEPTED   (prove)
-- author  : @gjindal
-- created : 2026-11-14T09:20:08.584426+00:00
-- url     : https://prove2.me/submissions/35ada9f7-97c7-4073-bab0-7c4a00265cc3

import Mathlib
import Definitions.Def_ResultantVNP_Circuit

set_option autoImplicit false

namespace CircuitSubstitution

open ResultantVNP

private noncomputable def run {σ : Type} (ns : List (Node σ))
    (vs : List (MvPolynomial σ ℂ)) :=
  ns.foldl (fun vals nd => vals ++ [nd.eval vals]) vs

private lemma run_length {σ : Type} (ns : List (Node σ))
    (vs : List (MvPolynomial σ ℂ)) : (run ns vs).length = vs.length + ns.length := by
  induction ns generalizing vs with
  | nil => simp [run]
  | cons nd ns ih =>
    change (run ns (vs ++ [nd.eval vs])).length = _
    simp [ih, Nat.add_assoc, Nat.add_comm]

private lemma values_length {σ : Type} (C : Circuit σ) :
    C.values.length = C.nodes.length := by
  simpa [Circuit.values, run] using run_length C.nodes []

private lemma values_nonempty {σ : Type} (C : Circuit σ) : C.values ≠ [] := by
  have := List.length_pos_iff_ne_nil.mpr C.nonempty
  intro h
  rw [← values_length C, h] at this
  contradiction

private lemma getD_last {α : Type} (l : List α) (d : α) :
    l.getD (l.length - 1) d = l.getLastD d := by
  simp only [List.getD_eq_getElem?_getD, List.getLastD_eq_getLast?,
    List.getLast?_eq_getElem?]

private def shift {σ : Type} (offset : ℕ) : Node σ → Node σ
  | .var x => .var x
  | .const a => .const a
  | .add i j => .add (offset + i) (offset + j)
  | .mul i j => .mul (offset + i) (offset + j)

private lemma shift_reads {σ : Type} (nd : Node σ) (offset k : ℕ)
    (h : nd.ReadsBelow k) : (shift offset nd).ReadsBelow (offset + k) := by
  cases nd <;> simp_all [shift, Node.ReadsBelow]

private lemma shift_eval {σ : Type} (basevals vs : List (MvPolynomial σ ℂ))
    (nd : Node σ) : (shift basevals.length nd).eval (basevals ++ vs) = nd.eval vs := by
  have hg (i : ℕ) : (basevals ++ vs).getD (basevals.length + i) 0 = vs.getD i 0 := by
    rw [List.getD_append_right _ _ _ _ (by omega), Nat.add_sub_cancel_left]
  cases nd <;> simp only [shift, Node.eval, hg]

private lemma run_shift {σ : Type} (ns : List (Node σ))
    (basevals vs : List (MvPolynomial σ ℂ)) :
    run (ns.map (shift basevals.length)) (basevals ++ vs) = basevals ++ run ns vs := by
  induction ns generalizing vs with
  | nil => rfl
  | cons nd ns ih =>
    change run (ns.map (shift basevals.length))
      ((basevals ++ vs) ++ [(shift basevals.length nd).eval (basevals ++ vs)]) = _
    rw [shift_eval, List.append_assoc, ih]
    rfl

private def appendCircuit {σ : Type} (C D : Circuit σ) : Circuit σ where
  nodes := C.nodes ++ D.nodes.map (shift C.nodes.length)
  nonempty := by simp [C.nonempty]
  wf := by
    intro k hk
    by_cases h : k < C.nodes.length
    · simpa only [List.getElem_append_left h] using C.wf k h
    · have hd : k - C.nodes.length < D.nodes.length := by
        simp only [List.length_append, List.length_map] at hk
        omega
      rw [List.getElem_append_right (by omega), List.getElem_map]
      have hs := shift_reads (D.nodes[k - C.nodes.length]) C.nodes.length
        (k - C.nodes.length) (D.wf _ hd)
      simpa only [Nat.add_sub_of_le (by omega : C.nodes.length ≤ k)] using hs

private lemma appendCircuit_values {σ : Type} (C D : Circuit σ) :
    (appendCircuit C D).values = C.values ++ D.values := by
  change run (C.nodes ++ D.nodes.map (shift C.nodes.length)) [] = _
  unfold run
  rw [List.foldl_append]
  change run (D.nodes.map (shift C.nodes.length)) C.values = C.values ++ run D.nodes []
  rw [← values_length C]
  simpa only [List.append_nil] using run_shift D.nodes C.values []

private lemma appendCircuit_size {σ : Type} (C D : Circuit σ) :
    (appendCircuit C D).size = C.size + D.size := by
  have hg : ∀ nd : Node σ, (shift C.nodes.length nd).isGate = nd.isGate := by
    intro nd; cases nd <;> rfl
  simp [Circuit.size, appendCircuit, List.countP_map, Function.comp_def, hg]

private def constCircuit {σ : Type} (a : ℂ) : Circuit σ where
  nodes := [.const a]
  nonempty := by simp
  wf := by intro k hk; simp at hk; subst k; trivial

private lemma constCircuit_value {σ : Type} (a : ℂ) :
    (constCircuit a : Circuit σ).value = MvPolynomial.C a := by
  simp [constCircuit, Circuit.value, Circuit.values, Node.eval]

private lemma constCircuit_size {σ : Type} (a : ℂ) :
    (constCircuit a : Circuit σ).size = 0 := by
  simp [constCircuit, Circuit.size, Node.isGate]

private def Extends {σ : Type} (C D : Circuit σ) : Prop :=
  ∃ tail, D.values = C.values ++ tail

private lemma extends_refl {σ : Type} (C : Circuit σ) : Extends C C :=
  ⟨[], by simp⟩

private lemma extends_trans {σ : Type} {C D E : Circuit σ}
    (h : Extends C D) (h' : Extends D E) : Extends C E := by
  obtain ⟨a, ha⟩ := h
  obtain ⟨b, hb⟩ := h'
  exact ⟨a ++ b, by rw [hb, ha, List.append_assoc]⟩

private def Realized {σ : Type} (C : Circuit σ) (p : MvPolynomial σ ℂ) : Prop :=
  ∃ i, i < C.values.length ∧ C.values.getD i 0 = p

private lemma realized_mono {σ : Type} {C D : Circuit σ} {p : MvPolynomial σ ℂ}
    (h : Extends C D) (hp : Realized C p) : Realized D p := by
  obtain ⟨tail, ht⟩ := h
  obtain ⟨i, hi, hp⟩ := hp
  refine ⟨i, ?_, ?_⟩
  · rw [ht, List.length_append]; omega
  · rw [ht, List.getD_append _ _ _ _ hi, hp]

private lemma realized_output {σ : Type} (C : Circuit σ) : Realized C C.value := by
  refine ⟨C.values.length - 1, ?_, getD_last _ _⟩
  have := List.length_pos_iff_ne_nil.mpr (values_nonempty C)
  omega

private def Covered {σ : Type} (C : Circuit σ) (s : ℕ)
    (p : MvPolynomial σ ℂ) : Prop :=
  Realized C p ∨ ∃ D : Circuit σ, D.value = p ∧ D.size ≤ s

private lemma covered_mono {σ : Type} {C D : Circuit σ} {s : ℕ}
    {p : MvPolynomial σ ℂ} (h : Extends C D) (hp : Covered C s p) : Covered D s p := by
  rcases hp with hp | hp
  · exact Or.inl (realized_mono h hp)
  · exact Or.inr hp

private lemma covered_const {σ : Type} (C : Circuit σ) (s : ℕ) (a : ℂ) :
    Covered C s (MvPolynomial.C a) := by
  exact Or.inr ⟨constCircuit a, constCircuit_value a, by simp [constCircuit_size]⟩

private lemma materialize {σ : Type} (C : Circuit σ) (s : ℕ)
    (p : MvPolynomial σ ℂ) (hp : Covered C s p) :
    ∃ D : Circuit σ, Extends C D ∧ D.size ≤ C.size + s ∧ Realized D p := by
  rcases hp with hp | ⟨D, hv, hs⟩
  · exact ⟨C, extends_refl C, by omega, hp⟩
  · refine ⟨appendCircuit C D, ⟨D.values, appendCircuit_values C D⟩, ?_, ?_⟩
    · rw [appendCircuit_size]; omega
    · refine ⟨C.values.length + (D.values.length - 1), ?_, ?_⟩
      · rw [appendCircuit_values, List.length_append]
        have := List.length_pos_iff_ne_nil.mpr (values_nonempty D)
        omega
      · rw [appendCircuit_values, List.getD_append_right _ _ _ _ (by omega),
          Nat.add_sub_cancel_left, getD_last]
        exact hv

private def appendNode {σ : Type} (C : Circuit σ) (nd : Node σ)
    (h : nd.ReadsBelow C.nodes.length) : Circuit σ where
  nodes := C.nodes ++ [nd]
  nonempty := by simp
  wf := by
    intro k hk
    by_cases hk' : k < C.nodes.length
    · simpa only [List.getElem_append_left hk'] using C.wf k hk'
    · have heq : k = C.nodes.length := by
        simp only [List.length_append, List.length_singleton] at hk
        omega
      subst k
      simpa using h

private lemma appendNode_values {σ : Type} (C : Circuit σ) (nd : Node σ)
    (h : nd.ReadsBelow C.nodes.length) :
    (appendNode C nd h).values = C.values ++ [nd.eval C.values] := by
  simp [appendNode, Circuit.values, List.foldl_append]

private lemma appendNode_value {σ : Type} (C : Circuit σ) (nd : Node σ)
    (h : nd.ReadsBelow C.nodes.length) :
    (appendNode C nd h).value = nd.eval C.values := by
  simp [Circuit.value, appendNode_values]

private lemma appendNode_size {σ : Type} (C : Circuit σ) (nd : Node σ)
    (h : nd.ReadsBelow C.nodes.length) :
    (appendNode C nd h).size = C.size + if nd.isGate then 1 else 0 := by
  simp [appendNode, Circuit.size]

private def binaryNode {σ : Type} (m : Bool) (i j : ℕ) : Node σ :=
  if m then .mul i j else .add i j

private noncomputable def binaryValue {σ : Type} (m : Bool)
    (a b : MvPolynomial σ ℂ) : MvPolynomial σ ℂ := if m then a * b else a + b

private lemma combine {σ : Type} (C : Circuit σ) (s : ℕ) (m : Bool)
    (a b : MvPolynomial σ ℂ) (ha : Covered C s a) (hb : Covered C s b) :
    ∃ D : Circuit σ, Extends C D ∧ D.size ≤ C.size + (2 * s + 1) ∧
      D.value = binaryValue m a b := by
  obtain ⟨C₁, he₁, hs₁, hr₁⟩ := materialize C s a ha
  obtain ⟨C₂, he₂, hs₂, hr₂⟩ := materialize C₁ s b (covered_mono he₁ hb)
  obtain ⟨i, hi, hia⟩ := realized_mono he₂ hr₁
  obtain ⟨j, hj, hjb⟩ := hr₂
  have hw : (binaryNode m i j : Node σ).ReadsBelow C₂.nodes.length := by
    rw [← values_length C₂]
    cases m <;> simpa [binaryNode, Node.ReadsBelow] using And.intro hi hj
  let D := appendNode C₂ (binaryNode m i j) hw
  refine ⟨D, extends_trans (extends_trans he₁ he₂)
    ⟨[(binaryNode m i j).eval C₂.values], appendNode_values _ _ _⟩, ?_, ?_⟩
  · change (appendNode _ _ _).size ≤ _
    rw [appendNode_size]
    have hg : (binaryNode m i j : Node σ).isGate = true := by
      cases m <;> rfl
    rw [hg]
    simp only [ite_true]
    omega
  · change (appendNode _ _ _).value = _
    rw [appendNode_value]
    cases m <;> simp only [binaryNode, binaryValue, Bool.false_eq_true,
      ite_false, ite_true, Node.eval, hia, hjb]

private lemma covered_getD {σ τ : Type} (f : σ → MvPolynomial τ ℂ)
    (C : Circuit τ) (s : ℕ) (vs : List (MvPolynomial σ ℂ))
    (hvs : ∀ p ∈ vs, Covered C s (MvPolynomial.aeval f p)) (i : ℕ) :
    Covered C s (MvPolynomial.aeval f (vs.getD i 0)) := by
  by_cases h : i < vs.length
  · rw [List.getD_eq_getElem _ _ h]
    exact hvs _ (List.getElem_mem h)
  · rw [List.getD_eq_default _ _ (by omega), map_zero]
    simpa using covered_const C s 0

private lemma step {σ τ : Type} (f : σ → MvPolynomial τ ℂ) (s : ℕ)
    (hf : ∀ x, ∃ D : Circuit τ, D.value = f x ∧ D.size ≤ s)
    (C : Circuit τ) (vs : List (MvPolynomial σ ℂ))
    (hvs : ∀ p ∈ vs, Covered C s (MvPolynomial.aeval f p)) (nd : Node σ) :
    ∃ D : Circuit τ, Extends C D ∧
      D.size ≤ C.size + (if nd.isGate then 2 * s + 1 else 0) ∧
      Covered D s (MvPolynomial.aeval f (nd.eval vs)) := by
  cases nd with
  | var x =>
    refine ⟨C, extends_refl C, by simp [Node.isGate], ?_⟩
    simp only [Node.eval, MvPolynomial.aeval_X]
    exact Or.inr (hf x)
  | const a =>
    refine ⟨C, extends_refl C, by simp [Node.isGate], ?_⟩
    simpa [Node.eval] using covered_const C s a
  | add i j =>
    obtain ⟨D, he, hs, hv⟩ := combine C s false _ _
      (covered_getD f C s vs hvs i) (covered_getD f C s vs hvs j)
    refine ⟨D, he, by simpa [Node.isGate] using hs, Or.inl ?_⟩
    have hr := realized_output D
    rw [hv] at hr
    simpa [Node.eval, binaryValue, map_add] using hr
  | mul i j =>
    obtain ⟨D, he, hs, hv⟩ := combine C s true _ _
      (covered_getD f C s vs hvs i) (covered_getD f C s vs hvs j)
    refine ⟨D, he, by simpa [Node.isGate] using hs, Or.inl ?_⟩
    have hr := realized_output D
    rw [hv] at hr
    simpa [Node.eval, binaryValue, map_mul] using hr

private lemma process {σ τ : Type} (f : σ → MvPolynomial τ ℂ) (s : ℕ)
    (hf : ∀ x, ∃ D : Circuit τ, D.value = f x ∧ D.size ≤ s)
    (ns : List (Node σ)) (vs : List (MvPolynomial σ ℂ))
    (C : Circuit τ) (hvs : ∀ p ∈ vs, Covered C s (MvPolynomial.aeval f p)) :
    ∃ D : Circuit τ, D.size ≤ C.size + ns.countP Node.isGate * (2 * s + 1) ∧
      ∀ p ∈ run ns vs, Covered D s (MvPolynomial.aeval f p) := by
  induction ns generalizing C vs with
  | nil => exact ⟨C, by simp, hvs⟩
  | cons nd ns ih =>
    obtain ⟨E, he, hs, hp⟩ := step f s hf C vs hvs nd
    have hE : ∀ p ∈ vs ++ [nd.eval vs], Covered E s (MvPolynomial.aeval f p) := by
      intro p h
      rcases List.mem_append.mp h with h | h
      · exact covered_mono he (hvs p h)
      · simpa only [List.mem_singleton.mp h] using hp
    obtain ⟨D, hD, hcover⟩ := ih (vs ++ [nd.eval vs]) E hE
    refine ⟨D, ?_, hcover⟩
    cases nd <;> simp only [Node.isGate, Bool.false_eq_true, ite_false, ite_true,
      List.countP_cons] at hs ⊢ <;> nlinarith

theorem substitution_bound {σ τ : Type} (C : Circuit σ)
    (f : σ → MvPolynomial τ ℂ) (s : ℕ)
    (hf : ∀ x, ∃ D : Circuit τ, D.value = f x ∧ D.size ≤ s) :
    ∃ D : Circuit τ, D.value = MvPolynomial.aeval f C.value ∧
      D.size ≤ (2 * C.size + 1) * (s + 1) := by
  obtain ⟨E, hE, hcover⟩ := process f s hf C.nodes [] (constCircuit 0)
    (by simp)
  have hE' : E.size ≤ C.size * (2 * s + 1) := by
    change E.size ≤ (constCircuit 0 : Circuit τ).size + C.size * (2 * s + 1) at hE
    simpa only [constCircuit_size, zero_add] using hE
  have hc : ∀ p ∈ C.values, Covered E s (MvPolynomial.aeval f p) := hcover
  have hout : Covered E s (MvPolynomial.aeval f C.value) := by
    simpa only [getD_last, Circuit.value] using
      covered_getD f E s C.values hc (C.values.length - 1)
  obtain ⟨E', he, hs, hr⟩ := materialize E s _ hout
  obtain ⟨D, _, hD, hv⟩ := combine E' 0 false _ 0 (Or.inl hr)
    (by simpa using covered_const E' 0 0)
  refine ⟨D, ?_, ?_⟩
  · simpa [binaryValue] using hv
  · nlinarith

end CircuitSubstitution

theorem solution {σ τ : Type} (C : ResultantVNP.Circuit σ)
    (f : σ → MvPolynomial τ ℂ) (s : ℕ)
    (hf : ∀ x, ∃ D : ResultantVNP.Circuit τ, D.value = f x ∧ D.size ≤ s) :
    ∃ D : ResultantVNP.Circuit τ,
      D.value = MvPolynomial.aeval f C.value ∧
      D.size ≤ (2 * C.size + 1) * (s + 1) :=
  CircuitSubstitution.substitution_bound C f s hf

#print axioms solution
