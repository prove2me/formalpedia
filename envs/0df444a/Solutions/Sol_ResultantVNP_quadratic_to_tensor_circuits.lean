-- Prove2me | solution 1 for ResultantVNP.quadratic_to_tensor_circuits
-- status  : ACCEPTED   (prove)
-- author  : @gjindal
-- created : 2026-11-14T09:01:30.467203+00:00
-- url     : https://prove2.me/submissions/99dc513d-08a0-493b-bf5a-69f71f6b70d7

import Mathlib
import Definitions.Def_ResultantVNP_quadRes
import Definitions.Def_ResultantVNP_tensorDet
import Definitions.Def_ResultantVNP_HasPolySizeCircuits
import Theorems.Thm_ResultantVNP_circuit_substitution_bound

set_option autoImplicit false

namespace TensorSpecialization

open ResultantVNP

private def leafNode {τ : Type} : Option τ → Node τ
  | none => .const 0
  | some x => .var x

private noncomputable def leafValue {τ : Type} : Option τ → MvPolynomial τ ℂ
  | none => 0
  | some x => MvPolynomial.X x

private lemma leaf_eval {τ : Type} (x : Option τ) (vs : List (MvPolynomial τ ℂ)) :
    (leafNode x).eval vs = leafValue x := by
  cases x <;> simp [leafNode, leafValue, Node.eval]

private def appendLeaf {τ : Type} (C : Circuit τ) (x : Option τ) : Circuit τ where
  nodes := C.nodes ++ [leafNode x, .add (C.nodes.length - 1) C.nodes.length]
  nonempty := by simp
  wf := by
    intro k hk
    by_cases h : k < C.nodes.length
    · simpa only [List.getElem_append_left h] using C.wf k h
    · have hk' : k = C.nodes.length ∨ k = C.nodes.length + 1 := by
        simp only [List.length_append, List.length_cons, List.length_nil] at hk
        omega
      rcases hk' with rfl | rfl
      · simp only [List.getElem_append_right (by omega : C.nodes.length ≤ C.nodes.length),
          Nat.sub_self, List.getElem_cons_zero]
        cases x <;> trivial
      · simp only [List.getElem_append_right (by omega : C.nodes.length ≤ C.nodes.length + 1),
          Nat.add_sub_cancel_left, List.getElem_cons_succ, List.getElem_cons_zero,
          Node.ReadsBelow]
        omega

private lemma eval_length {τ : Type} (nodes : List (Node τ))
    (vs : List (MvPolynomial τ ℂ)) :
    (nodes.foldl (fun vals nd => vals ++ [nd.eval vals]) vs).length =
      vs.length + nodes.length := by
  induction nodes generalizing vs with
  | nil => simp
  | cons nd nodes ih => simp [List.foldl_cons, ih, Nat.add_assoc, Nat.add_comm]

private lemma values_length {τ : Type} (C : Circuit τ) : C.values.length = C.nodes.length := by
  simpa [Circuit.values] using eval_length C.nodes []

private lemma getD_last {α : Type} (l : List α) (d : α) :
    l.getD (l.length - 1) d = l.getLastD d := by
  simp only [List.getD_eq_getElem?_getD, List.getLastD_eq_getLast?,
    List.getLast?_eq_getElem?]

private lemma appendLeaf_value {τ : Type} (C : Circuit τ) (x : Option τ) :
    (appendLeaf C x).value = C.value + leafValue x := by
  have hlen := values_length C
  have hpos : 0 < C.values.length := by
    rw [hlen]
    exact List.length_pos_iff_ne_nil.mpr C.nonempty
  have hleft : (C.values ++ [leafValue x]).getD (C.nodes.length - 1) 0 = C.value := by
    rw [List.getD_append _ _ _ _ (by omega), ← hlen, getD_last]
    rfl
  have hright : (C.values ++ [leafValue x]).getD C.nodes.length 0 = leafValue x := by
    rw [List.getD_append_right _ _ _ _ (by omega), ← hlen, Nat.sub_self]
    rfl
  change ((C.nodes ++ [leafNode x, .add (C.nodes.length - 1) C.nodes.length]).foldl
    (fun vs nd => vs ++ [nd.eval vs]) []).getLastD 0 = C.value + leafValue x
  rw [List.foldl_append]
  simp only [List.foldl_cons, List.foldl_nil]
  change (C.values ++ [(leafNode x).eval C.values] ++
    [Node.eval (C.values ++ [(leafNode x).eval C.values])
      (.add (C.nodes.length - 1) C.nodes.length)]).getLastD 0 = _
  rw [leaf_eval]
  change (C.values ++ [leafValue x] ++
    [(C.values ++ [leafValue x]).getD (C.nodes.length - 1) 0 +
      (C.values ++ [leafValue x]).getD C.nodes.length 0]).getLastD 0 = _
  rw [hleft, hright]
  simp

private lemma appendLeaf_size {τ : Type} (C : Circuit τ) (x : Option τ) :
    (appendLeaf C x).size = C.size + 1 := by
  cases x <;> simp [Circuit.size, appendLeaf, leafNode, Node.isGate]

private def zeroCircuit (τ : Type) : Circuit τ where
  nodes := [.const 0]
  nonempty := by simp
  wf := by intro k hk; simp at hk; subst k; trivial

private def sumCircuit {τ : Type} : List (Option τ) → Circuit τ
  | [] => zeroCircuit τ
  | x :: xs => appendLeaf (sumCircuit xs) x

private lemma sumCircuit_value {τ : Type} (xs : List (Option τ)) :
    (sumCircuit xs).value = (xs.map leafValue).sum := by
  induction xs with
  | nil => simp [sumCircuit, zeroCircuit, Circuit.value, Circuit.values, Node.eval]
  | cons x xs ih => simp [sumCircuit, appendLeaf_value, ih, add_comm]

private lemma sumCircuit_size {τ : Type} (xs : List (Option τ)) :
    (sumCircuit xs).size = xs.length := by
  induction xs with
  | nil => simp [sumCircuit, zeroCircuit, Circuit.size, Node.isGate]
  | cons x xs ih => simp [sumCircuit, appendLeaf_size, ih]

private noncomputable def tensorLeaf (n : ℕ) (i : Fin n)
    (e : Fin n →₀ ℕ) (jk : Fin n × Fin n) : Option (Fin n × Fin n × Fin n) := by
  classical
  exact if Finsupp.single jk.1 1 + Finsupp.single jk.2 1 = e then
    some (i, jk.1, jk.2) else none

private lemma tensorForm_coeff (n : ℕ) (i : Fin n) (e : Fin n →₀ ℕ) :
    MvPolynomial.map (Int.castRingHom ℂ) ((tensorForm n i).coeff e) =
      ∑ jk : Fin n × Fin n, leafValue (tensorLeaf n i e jk) := by
  classical
  simp only [tensorForm, MvPolynomial.coeff_sum, map_sum, Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro j hj
  apply Finset.sum_congr rfl
  intro k hk
  rw [mul_assoc, MvPolynomial.coeff_C_mul]
  have hx : ((MvPolynomial.X j * MvPolynomial.X k :
      MvPolynomial (Fin n) (MvPolynomial (Fin n × Fin n × Fin n) ℤ))).coeff e =
      if Finsupp.single j 1 + Finsupp.single k 1 = e then 1 else 0 := by
    simp only [MvPolynomial.X, MvPolynomial.monomial_mul, one_mul,
      MvPolynomial.coeff_monomial]
  rw [hx]
  by_cases h : Finsupp.single j 1 + Finsupp.single k 1 = e
  · simp [tensorLeaf, leafValue, h]
  · simp [tensorLeaf, leafValue, h]

private noncomputable def coefficientCircuit (n : ℕ) (i : Fin n) (e : Fin n →₀ ℕ) :
    Circuit (Fin n × Fin n × Fin n) :=
  sumCircuit ((Finset.univ : Finset (Fin n × Fin n)).toList.map (tensorLeaf n i e))

private lemma coefficientCircuit_value (n : ℕ) (i : Fin n) (e : Fin n →₀ ℕ) :
    (coefficientCircuit n i e).value =
      MvPolynomial.map (Int.castRingHom ℂ) ((tensorForm n i).coeff e) := by
  classical
  rw [coefficientCircuit, sumCircuit_value, tensorForm_coeff]
  simp [List.map_map]

private lemma coefficientCircuit_size (n : ℕ) (i : Fin n) (e : Fin n →₀ ℕ) :
    (coefficientCircuit n i e).size = n ^ 2 := by
  classical
  simp [coefficientCircuit, sumCircuit_size, pow_two]

private lemma specialization_identity (𝓡 : ResultantSystem) (n : ℕ) :
    MvPolynomial.aeval
      (fun v : CoeffVar (fun _ : Fin n => 2) =>
        MvPolynomial.map (Int.castRingHom ℂ) ((tensorForm n v.1).coeff v.2.1))
      (MvPolynomial.map (Int.castRingHom ℂ) (quadRes 𝓡 n)) =
        MvPolynomial.map (Int.castRingHom ℂ) (tensorDet 𝓡 n) := by
  exact (MvPolynomial.map_bind₁ (Int.castRingHom ℂ)
    (fun v : CoeffVar (fun _ : Fin n => 2) => (tensorForm n v.1).coeff v.2.1)
    (quadRes 𝓡 n)).symm

private lemma polynomial_bound (c n g : ℕ) (hn : 1 ≤ n)
    (hg : g ≤ c * n ^ c + c) :
    (2 * g + 1) * (n ^ 2 + 1) ≤ (8 * c + 4) * n ^ (8 * c + 4) + (8 * c + 4) := by
  have hp : 1 ≤ n ^ c := one_le_pow₀ hn
  have h2 : 1 ≤ n ^ 2 := one_le_pow₀ hn
  have hcg : c ≤ c * n ^ c := by nlinarith
  have ha : 2 * g + 1 ≤ (4 * c + 1) * n ^ c := by nlinarith
  have hb : n ^ 2 + 1 ≤ 2 * n ^ 2 := by omega
  have hm : n ^ (c + 2) ≤ n ^ (8 * c + 4) :=
    Nat.pow_le_pow_right hn (by omega)
  calc
    (2 * g + 1) * (n ^ 2 + 1) ≤ ((4 * c + 1) * n ^ c) * (2 * n ^ 2) :=
      Nat.mul_le_mul ha hb
    _ = (8 * c + 2) * n ^ (c + 2) := by rw [pow_add]; ring
    _ ≤ (8 * c + 2) * n ^ (8 * c + 4) := Nat.mul_le_mul_left _ hm
    _ ≤ (8 * c + 4) * n ^ (8 * c + 4) :=
      Nat.mul_le_mul_right _ (by omega)
    _ ≤ (8 * c + 4) * n ^ (8 * c + 4) + (8 * c + 4) := Nat.le_add_right _ _

end TensorSpecialization

/-!
Target: ResultantVNP.quadratic_to_tensor_circuits
UUID: b947833c-6954-4f04-aae2-7a7d0d985b32

This proof-sketch depends only on the generic circuit-substitution bound.
All tensor-coefficient circuits, the exact substitution identity, and the
polynomial-size estimate are proved above without open dependencies.
-/
theorem solution (𝓡 : ResultantVNP.ResultantSystem)
    (h : ResultantVNP.HasPolySizeCircuits
      (fun n => MvPolynomial.map (Int.castRingHom ℂ) (ResultantVNP.quadRes 𝓡 n))) :
    ResultantVNP.HasPolySizeCircuits
      (fun n => MvPolynomial.map (Int.castRingHom ℂ) (ResultantVNP.tensorDet 𝓡 n)) := by
  obtain ⟨c, hc⟩ := h
  refine ⟨8 * c + 4, ?_⟩
  intro n hn
  obtain ⟨C, hC, hsize⟩ := hc n hn
  let f : ResultantVNP.CoeffVar (fun _ : Fin n => 2) →
      MvPolynomial (Fin n × Fin n × Fin n) ℂ :=
    fun v => MvPolynomial.map (Int.castRingHom ℂ)
      ((ResultantVNP.tensorForm n v.1).coeff v.2.1)
  have hf : ∀ v, ∃ D : ResultantVNP.Circuit (Fin n × Fin n × Fin n),
      D.value = f v ∧ D.size ≤ n ^ 2 := by
    intro v
    exact ⟨TensorSpecialization.coefficientCircuit n v.1 v.2.1,
      TensorSpecialization.coefficientCircuit_value n v.1 v.2.1,
      (TensorSpecialization.coefficientCircuit_size n v.1 v.2.1).le⟩
  obtain ⟨D, hD, hbound⟩ := ResultantVNP.circuit_substitution_bound C f (n ^ 2) hf
  refine ⟨D, ?_, ?_⟩
  · rw [hD, hC]
    exact TensorSpecialization.specialization_identity 𝓡 n
  · exact hbound.trans (TensorSpecialization.polynomial_bound c n C.size hn hsize)

#print axioms solution
#print axioms TensorSpecialization.coefficientCircuit_value
#print axioms TensorSpecialization.coefficientCircuit_size
#print axioms TensorSpecialization.specialization_identity
#print axioms TensorSpecialization.polynomial_bound
