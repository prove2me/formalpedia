-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Support50.P30.hammingWeight_eigenvalues
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-24T14:10:52.702018+00:00
-- url     : https://prove2.me/submissions/cfc2f898-219b-417b-a2e9-689e8642e5fd

import Definitions.Def_QAlgorithms_Papers_Independent_Support50_P30

open Finset

namespace X8HW

open QAlgorithms QAlgorithms.Papers.Independent.Support50.P30

variable {α : Type*} [DecidableEq α]

def e (f : α → ℂ) (k : ℕ) (s : Finset α) : ℂ := ∑ t ∈ s.powersetCard k, ∏ j ∈ t, f j

lemma e_insert (f : α → ℂ) {a : α} {s : Finset α} (ha : a ∉ s) (k : ℕ) :
    e f (k + 1) (insert a s) = e f (k + 1) s + f a * e f k s := by
  unfold e
  rw [powersetCard_succ_insert ha, sum_union, sum_image, mul_sum]
  · congr 1
    apply sum_congr rfl
    intro t ht
    have : a ∉ t := fun h => ha ((mem_powersetCard.1 ht).1 h)
    rw [prod_insert this]
  · intro t ht u hu h
    have hta : a ∉ t := fun h' => ha ((mem_powersetCard.1 ht).1 h')
    have hua : a ∉ u := fun h' => ha ((mem_powersetCard.1 hu).1 h')
    have := congrArg (fun v => Finset.erase v a) h
    simpa [erase_insert hta, erase_insert hua] using this
  · rw [disjoint_left]
    intro t ht ht'
    obtain ⟨u, _, rfl⟩ := mem_image.1 ht'
    exact ha ((mem_powersetCard.1 ht).1 (mem_insert_self a u))

lemma e_zero (f : α → ℂ) (s : Finset α) : e f 0 s = 1 := by simp [e]

lemma e_one (f : α → ℂ) (s : Finset α) : e f 1 s = ∑ j ∈ s, f j := by
  induction s using Finset.induction_on with
  | empty => simp [e, powersetCard_eq_empty.2 (by simp : (∅ : Finset α).card < 1)]
  | insert a s ha ih =>
    rw [e_insert f ha, ih, e_zero, sum_insert ha]; ring

lemma e_two (f : α → ℂ) (s : Finset α) :
    e f 2 s = ((∑ j ∈ s, f j) ^ 2 - ∑ j ∈ s, f j ^ 2) / 2 := by
  induction s using Finset.induction_on with
  | empty => simp [e, powersetCard_eq_empty.2 (by simp : (∅ : Finset α).card < 2)]
  | insert a s ha ih =>
    rw [e_insert f ha, ih, e_one, sum_insert ha, sum_insert ha]; ring


def sg {n : ℕ} (z : Qubits n) (j : Fin n) : ℂ := if z j then -1 else 1

lemma ps_apply {n : ℕ} (s : Finset (Fin n)) (x y : Qubits n) :
    pauliString n pauliZ s x y = if x = y then ∏ j ∈ s, sg y j else 0 := by
  unfold pauliString
  split_ifs with h
  · subst h
    rw [← Finset.prod_filter_mul_prod_filter_not univ (fun j => j ∈ s)]
    have h1 : ∏ j ∈ univ.filter (fun j => j ∉ s),
        (if j ∈ s then pauliZ (x j) (x j) else if x j = x j then (1 : ℂ) else 0) = 1 := by
      apply prod_eq_one; intro j hj; simp at hj; simp [hj]
    rw [h1, mul_one, filter_mem_eq_inter, univ_inter]
    apply prod_congr rfl; intro j hj
    simp [hj, pauliZ, sg]
  · obtain ⟨j, hj⟩ : ∃ j, x j ≠ y j := by
      by_contra hc; push Not at hc; exact h (funext hc)
    apply prod_eq_zero (mem_univ j)
    split_ifs <;> simp_all [pauliZ]

lemma coll_apply {n : ℕ} (k : ℕ) (x y : Qubits n) :
    collective n pauliZ k x y = if x = y then e (sg y) k univ else 0 := by
  unfold collective e
  rw [Matrix.sum_apply]
  simp_rw [ps_apply]
  split_ifs <;> simp

lemma act_coll {n : ℕ} (k : ℕ) (z : Qubits n) :
    act (collective n pauliZ k) (ket z) = e (sg z) k univ • ket z := by
  ext x
  simp [act, ket, Matrix.mulVec, dotProduct, EuclideanSpace.single_apply, coll_apply]

lemma sum_sg {n : ℕ} (z : Qubits n) : ∑ j, sg z j = (n : ℂ) - 2 * (hammingWeight z : ℂ) := by
  unfold sg hammingWeight
  rw [Finset.sum_ite]
  simp
  have := Finset.card_filter_add_card_filter_not (s := (univ : Finset (Fin n))) (fun j => z j = true)
  simp at this
  have h2 : ((univ.filter (fun j => z j = false)).card : ℂ) = n - (univ.filter (fun j => z j = true)).card := by
    rw [eq_sub_iff_add_eq]; exact_mod_cast (by omega : _ = n)
  rw [h2]; ring

lemma sum_sg_sq {n : ℕ} (z : Qubits n) : ∑ j, sg z j ^ 2 = n := by
  unfold sg; simp [apply_ite (fun x : ℂ => x ^ 2)]

lemma prod_sg {n : ℕ} (z : Qubits n) : ∏ j, sg z j = (-1) ^ hammingWeight z := by
  unfold sg hammingWeight
  rw [Finset.prod_ite]; simp

theorem x8_main (n : ℕ) (z : Qubits n) :
    act (collective n pauliZ 1) (ket z) =
      (((n : ℂ) - 2 * (hammingWeight z : ℂ))) • ket z ∧
    act (collective n pauliZ 2) (ket z) =
      (((n : ℂ) ^ 2 - (n : ℂ) * (4 * (hammingWeight z : ℂ) + 1) +
        4 * (hammingWeight z : ℂ) ^ 2) / 2) • ket z ∧
    act (collective n pauliZ n) (ket z) =
      ((-1 : ℂ) ^ hammingWeight z) • ket z := by
  refine ⟨?_, ?_, ?_⟩
  · rw [act_coll, e_one, sum_sg]
  · rw [act_coll, e_two, sum_sg, sum_sg_sq]; congr 1; ring
  · rw [act_coll]; congr 1
    unfold e
    have : (univ : Finset (Fin n)).powersetCard n = {univ} := by
      simpa using powersetCard_self (univ : Finset (Fin n))
    rw [this, sum_singleton, prod_sg]

end X8HW

open QAlgorithms QAlgorithms.Papers.Independent.Support50.P30 in
theorem solution (n : ℕ) (z : Qubits n) :
    act (collective n pauliZ 1) (ket z) =
      (((n : ℂ) - 2 * (hammingWeight z : ℂ))) • ket z ∧
    act (collective n pauliZ 2) (ket z) =
      (((n : ℂ) ^ 2 - (n : ℂ) * (4 * (hammingWeight z : ℂ) + 1) +
        4 * (hammingWeight z : ℂ) ^ 2) / 2) • ket z ∧
    act (collective n pauliZ n) (ket z) =
      ((-1 : ℂ) ^ hammingWeight z) • ket z :=
  X8HW.x8_main n z
