-- Prove2me | solution 1 for ResultantVNP.circuit_affine_coefficient_bound
-- status  : ACCEPTED   (prove)
-- author  : @gjindal
-- created : 2026-11-14T10:54:11.185443+00:00
-- url     : https://prove2.me/submissions/5fa2ddc5-0d0b-4896-b5b1-05f7717f806f

import Mathlib
import Definitions.Def_ResultantVNP_Circuit

set_option autoImplicit false

namespace CircuitCoefficients

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


private def varCircuit {σ : Type} (x : σ) : Circuit σ where
  nodes := [.var x]
  nonempty := by simp
  wf := by intro k hk; simp at hk; subst k; trivial

private lemma varCircuit_value {σ : Type} (x : σ) :
    (varCircuit x : Circuit σ).value = MvPolynomial.X x := by
  simp [varCircuit, Circuit.value, Circuit.values, Node.eval]

private lemma varCircuit_size {σ : Type} (x : σ) :
    (varCircuit x : Circuit σ).size = 0 := by
  simp [varCircuit, Circuit.size, Node.isGate]

private lemma covered_zero {σ : Type} (C : Circuit σ) : Covered C 0 0 := by
  simpa using covered_const C 0 0

private lemma batch {σ : Type} (C : Circuit σ) (k b : ℕ)
    (p : ℕ → MvPolynomial σ ℂ)
    (hp : ∀ E : Circuit σ, Extends C E → ∀ i < k,
      ∃ D : Circuit σ, Extends E D ∧ D.size ≤ E.size + b ∧ Covered D 0 (p i)) :
    ∃ D : Circuit σ, Extends C D ∧ D.size ≤ C.size + k * b ∧
      ∀ i < k, Covered D 0 (p i) := by
  induction k with
  | zero => exact ⟨C, extends_refl C, by simp, by omega⟩
  | succ k ih =>
    obtain ⟨E, he, hs, hE⟩ := ih (fun E he i hi => hp E he i (by omega))
    obtain ⟨D, hd, hds, hD⟩ := hp E he k (by omega)
    refine ⟨D, extends_trans he hd, by nlinarith, ?_⟩
    intro i hi
    by_cases hik : i < k
    · exact covered_mono hd (hE i hik)
    · have : i = k := by omega
      simpa [this] using hD

private lemma sum_products {σ : Type} (C : Circuit σ) (k : ℕ)
    (a b : ℕ → MvPolynomial σ ℂ)
    (ha : ∀ i < k, Covered C 0 (a i)) (hb : ∀ i < k, Covered C 0 (b i)) :
    ∃ D : Circuit σ, Extends C D ∧ D.size ≤ C.size + 2 * k ∧
      Covered D 0 (∑ i ∈ Finset.range k, a i * b i) := by
  induction k with
  | zero => exact ⟨C, extends_refl C, by simp, by simpa using covered_zero C⟩
  | succ k ih =>
    obtain ⟨E, he, hs, hE⟩ := ih (fun i hi => ha i (by omega))
      (fun i hi => hb i (by omega))
    obtain ⟨F, hf, hfs, hF⟩ := combine E 0 true (a k) (b k)
      (covered_mono he (ha k (by omega))) (covered_mono he (hb k (by omega)))
    have hr : Covered F 0 (a k * b k) := by
      apply Or.inl
      simpa only [hF, binaryValue, ite_true] using realized_output F
    obtain ⟨D, hd, hds, hD⟩ := combine F 0 false _ _ (covered_mono hf hE) hr
    refine ⟨D, extends_trans (extends_trans he hf) hd, by omega, Or.inl ?_⟩
    simpa only [hD, binaryValue, Bool.false_eq_true, ite_false,
      Finset.sum_range_succ] using realized_output D

private lemma get_coeff_covered {σ τ : Type}
    (f : σ → Polynomial (MvPolynomial τ ℂ)) (C : Circuit τ)
    (vs : List (MvPolynomial σ ℂ)) (s : ℕ)
    (hvs : ∀ p ∈ vs, ∀ k ≤ s, Covered C 0 ((MvPolynomial.aeval f p).coeff k))
    (i k : ℕ) (hk : k ≤ s) :
    Covered C 0 ((MvPolynomial.aeval f (vs.getD i 0)).coeff k) := by
  by_cases h : i < vs.length
  · rw [List.getD_eq_getElem _ _ h]
    exact hvs _ (List.getElem_mem h) k hk
  · rw [List.getD_eq_default _ _ (by omega), map_zero, Polynomial.coeff_zero]
    exact covered_zero C

private lemma coefficient_step {σ τ : Type}
    (f : σ → Polynomial (MvPolynomial τ ℂ)) (s : ℕ)
    (hf : ∀ x k, ∃ D : Circuit τ, D.value = (f x).coeff k ∧ D.size = 0)
    (C : Circuit τ) (vs : List (MvPolynomial σ ℂ))
    (hvs : ∀ p ∈ vs, ∀ k ≤ s, Covered C 0 ((MvPolynomial.aeval f p).coeff k))
    (nd : Node σ) :
    ∃ D : Circuit τ, Extends C D ∧
      D.size ≤ C.size + (if nd.isGate then 2 * (s + 1)^2 else 0) ∧
      ∀ k ≤ s, Covered D 0 ((MvPolynomial.aeval f (nd.eval vs)).coeff k) := by
  cases nd with
  | var x =>
    refine ⟨C, extends_refl C, by simp [Node.isGate], ?_⟩
    intro k hk
    rw [Node.eval, MvPolynomial.aeval_X]
    obtain ⟨D, hv, hs⟩ := hf x k
    exact Or.inr ⟨D, hv, by omega⟩
  | const a =>
    refine ⟨C, extends_refl C, by simp [Node.isGate], ?_⟩
    intro k hk
    simp only [Node.eval, MvPolynomial.aeval_C, Polynomial.algebraMap_apply,
      MvPolynomial.algebraMap_eq]
    change Covered C 0 ((Polynomial.C (MvPolynomial.C a)).coeff k)
    rw [Polynomial.coeff_C]
    split_ifs
    · exact covered_const C 0 a
    · exact covered_zero C
  | add i j =>
    obtain ⟨D, he, hs, hD⟩ := batch C (s+1) 1
      (fun k => (MvPolynomial.aeval f (Node.eval vs (.add i j))).coeff k) (by
        intro E he k hk
        obtain ⟨D, hd, hds, hv⟩ := combine E 0 false _ _
          (covered_mono he (get_coeff_covered f C vs s hvs i k (by omega)))
          (covered_mono he (get_coeff_covered f C vs s hvs j k (by omega)))
        refine ⟨D, hd, by omega, Or.inl ?_⟩
        simpa only [hv, binaryValue, Bool.false_eq_true, ite_false,
          Node.eval, map_add, Polynomial.coeff_add] using realized_output D)
    exact ⟨D, he, by simp only [Node.isGate, ite_true]; nlinarith,
      fun k hk => hD k (by omega)⟩
  | mul i j =>
    obtain ⟨D, he, hs, hD⟩ := batch C (s+1) (2*(s+1))
      (fun k => (MvPolynomial.aeval f (Node.eval vs (.mul i j))).coeff k) (by
        intro E he k hk
        obtain ⟨D, hd, hds, hv⟩ := sum_products E (k+1)
          (fun l => (MvPolynomial.aeval f (vs.getD i 0)).coeff l)
          (fun l => (MvPolynomial.aeval f (vs.getD j 0)).coeff (k-l))
          (fun l hl => covered_mono he (get_coeff_covered f C vs s hvs i l (by omega)))
          (fun l hl => covered_mono he (get_coeff_covered f C vs s hvs j (k-l) (by omega)))
        refine ⟨D, hd, by omega, ?_⟩
        simpa only [Node.eval, map_mul, Polynomial.coeff_mul,
          Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk] using hv)
    exact ⟨D, he, by simp only [Node.isGate, ite_true]; nlinarith,
      fun k hk => hD k (by omega)⟩

private lemma coefficient_process {σ τ : Type}
    (f : σ → Polynomial (MvPolynomial τ ℂ)) (s : ℕ)
    (hf : ∀ x k, ∃ D : Circuit τ, D.value = (f x).coeff k ∧ D.size = 0)
    (ns : List (Node σ)) (vs : List (MvPolynomial σ ℂ))
    (C : Circuit τ)
    (hvs : ∀ p ∈ vs, ∀ k ≤ s, Covered C 0 ((MvPolynomial.aeval f p).coeff k)) :
    ∃ D : Circuit τ, D.size ≤ C.size + ns.countP Node.isGate * (2*(s+1)^2) ∧
      ∀ p ∈ run ns vs, ∀ k ≤ s, Covered D 0 ((MvPolynomial.aeval f p).coeff k) := by
  induction ns generalizing C vs with
  | nil => exact ⟨C, by simp, hvs⟩
  | cons nd ns ih =>
    obtain ⟨E, he, hs, hp⟩ := coefficient_step f s hf C vs hvs nd
    have hE : ∀ p ∈ vs ++ [nd.eval vs], ∀ k ≤ s,
        Covered E 0 ((MvPolynomial.aeval f p).coeff k) := by
      intro p h k hk
      rcases List.mem_append.mp h with h | h
      · exact covered_mono he (hvs p h k hk)
      · simpa only [List.mem_singleton.mp h] using hp k hk
    obtain ⟨D, hD, hcover⟩ := ih (vs ++ [nd.eval vs]) E hE
    refine ⟨D, ?_, hcover⟩
    cases nd <;> simp only [Node.isGate, Bool.false_eq_true, ite_false, ite_true,
      List.countP_cons] at hs ⊢ <;> nlinarith

theorem coefficient_bound {σ τ : Type} (C : Circuit σ)
    (f : σ → Polynomial (MvPolynomial τ ℂ)) (s : ℕ)
    (hf : ∀ x k, ∃ D : Circuit τ, D.value = (f x).coeff k ∧ D.size = 0) :
    ∃ D : Circuit τ, D.value = (MvPolynomial.aeval f C.value).coeff s ∧
      D.size ≤ 2*(s+1)^2*C.size+1 := by
  obtain ⟨E, hE, hcover⟩ := coefficient_process f s hf C.nodes [] (constCircuit 0)
    (by simp)
  have hE' : E.size ≤ C.size * (2*(s+1)^2) := by
    change E.size ≤ (constCircuit 0 : Circuit τ).size + C.size * (2*(s+1)^2) at hE
    simpa only [constCircuit_size, zero_add] using hE
  have hout : Covered E 0 ((MvPolynomial.aeval f C.value).coeff s) := by
    simpa only [getD_last, Circuit.value] using
      get_coeff_covered f E C.values s hcover (C.values.length-1) s (le_refl s)
  obtain ⟨D, _, hD, hv⟩ := combine E 0 false _ 0 hout (covered_zero E)
  refine ⟨D, by simpa [binaryValue] using hv, by nlinarith⟩

end CircuitCoefficients

theorem solution {σ : Type} (C : ResultantVNP.Circuit σ) (δ : σ → ℂ) (s : ℕ) :
    ∃ D : ResultantVNP.Circuit σ,
      D.value = (MvPolynomial.aeval (fun x =>
        Polynomial.C (MvPolynomial.C (δ x)) +
          Polynomial.X * Polynomial.C (MvPolynomial.X x)) C.value).coeff s ∧
      D.size ≤ 2 * (s+1)^2 * C.size + 1 := by
  apply CircuitCoefficients.coefficient_bound
  intro x k
  by_cases hk0 : k = 0
  · subst k
    exact ⟨CircuitCoefficients.constCircuit (δ x), by
      simp [CircuitCoefficients.constCircuit_value], CircuitCoefficients.constCircuit_size _⟩
  · by_cases hk1 : k = 1
    · subst k
      exact ⟨CircuitCoefficients.varCircuit x, by
        simp [CircuitCoefficients.varCircuit_value], CircuitCoefficients.varCircuit_size _⟩
    · exact ⟨CircuitCoefficients.constCircuit 0, by
        simp [CircuitCoefficients.constCircuit_value, Polynomial.coeff_C, Polynomial.coeff_X, hk0, Ne.symm hk1], CircuitCoefficients.constCircuit_size _⟩

#print axioms solution
