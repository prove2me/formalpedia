-- Prove2me | solution 1 for QAlgorithms.GottesmanIntro.codeBounds
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-18T02:35:28.16959+00:00
-- url     : https://prove2.me/submissions/6d505324-0cea-4171-b2b3-bdb0341e0559
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_QAlgorithms_GottesmanIntro_quantumHamming_errorDimension
import Theorems.Thm_QAlgorithms_GottesmanIntro_quantumGV_exists
import Theorems.Thm_QAlgorithms_GottesmanIntro_codeBounds_asymptotic_of_hamming
import Mathlib.Data.Fintype.Powerset
set_option autoImplicit false
open QAlgorithms QAlgorithms.Stabilizer
open scoped Matrix
namespace CodeBoundsProof
private def supp {n : ℕ} (o : Fin n → Pauli) : Finset (Fin n) :=
  Finset.univ.filter (fun i => o i ≠ .I)

set_option maxHeartbeats 60000 in
private lemma pauli_weight_card (n j : ℕ) :
    Fintype.card {o : Fin n → Pauli // opsWeight o = j} = 3^j * n.choose j := by
  classical
  let D := Σ S : {S : Finset (Fin n) // S.card = j}, S.1 → {p : Pauli // p ≠ .I}
  let dec (z : D) : Fin n → Pauli :=
    fun i => if h : i ∈ z.1.1 then (z.2 ⟨i,h⟩).1 else .I
  have hs (z : D) : supp (dec z) = z.1.1 := by
    ext i
    by_cases hi : i ∈ z.1.1
    · simpa [supp,dec,hi] using (z.2 ⟨i,hi⟩).2
    · simp [supp,dec,hi]
  let f : D → {o : Fin n → Pauli // opsWeight o = j} :=
    fun z => ⟨dec z, by change (supp (dec z)).card = j; rw [hs]; exact z.1.2⟩
  have hf : Function.Bijective f := by
    constructor
    · rintro ⟨⟨S,hS⟩,u⟩ ⟨⟨T,hT⟩,v⟩ h
      have hd : dec ⟨⟨S,hS⟩,u⟩ = dec ⟨⟨T,hT⟩,v⟩ := congrArg Subtype.val h
      have hST : S=T := (hs ⟨⟨S,hS⟩,u⟩).symm.trans ((congrArg supp hd).trans (hs ⟨⟨T,hT⟩,v⟩))
      subst T
      have huv : u=v := by
        funext i
        apply Subtype.ext
        have hv := congrFun hd i.1
        simpa [dec,i.2] using hv
      subst v; rfl
    · intro o
      let S : {S : Finset (Fin n) // S.card = j} := ⟨supp o.1,o.2⟩
      let u : S.1 → {p : Pauli // p ≠ .I} :=
        fun i => ⟨o.1 i.1,(Finset.mem_filter.mp i.2).2⟩
      refine ⟨⟨S,u⟩,Subtype.ext (funext fun i => ?_)⟩
      by_cases hi : i ∈ supp o.1
      · simp [f,dec,S,u,hi]
      · have ho : o.1 i = .I := by simpa [supp] using hi
        simp [f,dec,S,u,hi,ho]
  have hcard : Fintype.card {p : Pauli // p ≠ .I} = 3 := by decide
  calc
    _ = Fintype.card D := (Fintype.card_congr (Equiv.ofBijective f hf)).symm
    _ = 3^j * n.choose j := by
      simp [D,Fintype.card_sigma,hcard,
        show ∀ S : {S : Finset (Fin n) // S.card = j}, S.1.card = j from fun S => S.2,
        Nat.mul_comm]

set_option maxHeartbeats 60000 in
private lemma pauli_ball_card (n t : ℕ) :
    Fintype.card {o : Fin n → Pauli // opsWeight o ≤ t} =
      ∑ j ∈ Finset.range (t+1), 3^j * n.choose j := by
  classical
  have h := Finset.sum_card_fiberwise_eq_card_filter
    (Finset.univ : Finset (Fin n → Pauli)) (Finset.range (t+1)) opsWeight
  simp only [Finset.mem_range,Nat.lt_succ_iff] at h
  rw [Fintype.subtype_card]
  rw [← h]
  apply Finset.sum_congr rfl
  intro j hj
  rw [← Fintype.subtype_card]
  exact pauli_weight_card n j

private theorem finite_hamming (n k d : ℕ)
    (C : Submodule ℂ (EuclideanSpace ℂ (Qubits n)))
    (hC : IsQCode n k d C) (hnd : IsNondegenerate C ((d-1)/2)) :
    (∑ j ∈ Finset.range ((d-1)/2+1), 3^j * n.choose j) * 2^k ≤ 2^n := by
  rw [← pauli_ball_card]
  exact QAlgorithms.GottesmanIntro.quantumHamming_errorDimension C hC hnd
end CodeBoundsProof

theorem solution :
    (∀ n k d : ℕ, 1 ≤ d →
      (∑ j ∈ Finset.range d, 3 ^ j * n.choose j) * 2 ^ k ≤ 2 ^ n →
      ∃ C : Submodule ℂ (EuclideanSpace ℂ (Qubits n)), IsQCode n k d C) ∧
    (∀ (n k d : ℕ) (C : Submodule ℂ (EuclideanSpace ℂ (Qubits n))), IsQCode n k d C →
      IsNondegenerate C ((d - 1) / 2) →
      (∑ j ∈ Finset.range ((d - 1) / 2 + 1), 3 ^ j * n.choose j) * 2 ^ k ≤ 2 ^ n) ∧
    ∀ p : ℝ, 0 < p → p < 1 / 2 → ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n ≥ N,
      (∀ (k d : ℕ) (C : Submodule ℂ (EuclideanSpace ℂ (Qubits n))), IsQCode n k d C →
        IsNondegenerate C ((d - 1) / 2) → 2 * p * n ≤ d →
        (k : ℝ) / n ≤ 1 - p * Real.logb 2 3 - binEntropy2 p + ε) ∧
      (0 < 1 - 2 * p * Real.logb 2 3 - binEntropy2 (2 * p) →
        ∃ (k d : ℕ) (C : Submodule ℂ (EuclideanSpace ℂ (Qubits n))), IsQCode n k d C ∧
          IsNondegenerate C ((d - 1) / 2) ∧ 2 * p * n ≤ d ∧
          1 - 2 * p * Real.logb 2 3 - binEntropy2 (2 * p) - ε ≤ (k : ℝ) / n) := by
  refine ⟨QAlgorithms.GottesmanIntro.quantumGV_exists, CodeBoundsProof.finite_hamming, ?_⟩
  exact QAlgorithms.GottesmanIntro.codeBounds_asymptotic_of_hamming CodeBoundsProof.finite_hamming
