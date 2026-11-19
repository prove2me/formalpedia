-- Prove2me | solution 1 for QuantumBipartiteTesting.Bipartiteness.lemma_2_9
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T12:47:39.28145+00:00
-- url     : https://prove2.me/submissions/7df63e4c-d256-4e0e-90d7-bc88c1b42be4

import Definitions.Def_QuantumBipartiteTesting_Bipartiteness_Reduction
import Theorems.Thm_QuantumBipartiteTesting_Bipartiteness_actual_acceptance_polynomial
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency.types false
namespace QuantumBipartiteTesting.Bipartiteness
open Finset
noncomputable section
attribute [local instance] Classical.propDecidable

private def mobiusCoeff {α : Type} [DecidableEq α] (f : Finset α → ℝ) (T : Finset α) : ℝ :=
  ∑ U ∈ T.powerset, (-1 : ℝ)^(T.card-U.card) * f U

private lemma mobius_insert {α : Type} [DecidableEq α] (f : Finset α → ℝ) (T : Finset α) (a : α) (ha : a ∉ T) :
    mobiusCoeff f (insert a T) = mobiusCoeff (fun U => f (insert a U)-f U) T := by
  unfold mobiusCoeff
  rw [sum_powerset_insert ha, ← sum_add_distrib]
  apply sum_congr rfl
  intro U hU
  have hUT := mem_powerset.mp hU
  have haU : a ∉ U := notMem_mono hUT ha
  have hc : U.card ≤ T.card := card_le_card hUT
  rw [card_insert_of_notMem ha, card_insert_of_notMem haU,
    show T.card+1-U.card = (T.card-U.card)+1 by omega,
    show T.card+1-(U.card+1) = T.card-U.card by omega, pow_succ]
  ring

private lemma mobius_reconstruct {α : Type} [DecidableEq α] (f : Finset α → ℝ) (T : Finset α) :
    ∑ U ∈ T.powerset, mobiusCoeff f U = f T := by
  induction T using Finset.induction_on generalizing f with
  | empty => simp [mobiusCoeff]
  | @insert a T ha ih =>
    rw [sum_powerset_insert ha, ih f]
    have hsum : (∑ U ∈ T.powerset, mobiusCoeff f (insert a U)) =
        ∑ U ∈ T.powerset, mobiusCoeff (fun V => f (insert a V)-f V) U := by
      apply sum_congr rfl
      intro U hU
      exact mobius_insert f U a (notMem_mono (mem_powerset.mp hU) ha)
    rw [hsum, ih]
    ring

private lemma mobius_cancel {α : Type} [DecidableEq α] (f : Finset α → ℝ) (T : Finset α)
    (a : α) (ha : a ∈ T)
    (hf : ∀ U ⊆ T.erase a, f (insert a U) = f U) : mobiusCoeff f T = 0 := by
  have he : T = insert a (T.erase a) := (insert_erase ha).symm
  rw [he, mobius_insert f _ a (notMem_erase _ _)]
  unfold mobiusCoeff
  apply sum_eq_zero
  intro U hU
  simp only [hf U (mem_powerset.mp hU), sub_self, mul_zero]

private lemma word_spec {I S : Type} [Fintype I] [Fintype S] [DecidableEq I] [DecidableEq S]
    (T : ResponseTable I S) (a : I) (z : S) :
    TableWord T.val a = some z ↔ (a,z) ∈ T.val := by
  by_cases h : ∃ y, (a,y) ∈ T.val
  · simp only [TableWord, dif_pos h, Option.some.injEq]
    constructor
    · intro hz
      exact hz ▸ h.choose_spec
    · intro hz
      exact T.property a h.choose z h.choose_spec hz
  · simp only [TableWord, dif_neg h, reduceCtorEq, false_iff]
    exact fun hz => h ⟨z,hz⟩

private def graphTable {I S : Type} [Fintype I] [Fintype S] [DecidableEq I] [DecidableEq S]
    (O : I → Option S) : ResponseTable I S :=
  ⟨univ.filter (fun az => O az.1 = some az.2), by
    intro a z z' hz hz'
    have he := (mem_filter.mp hz).2.symm.trans (mem_filter.mp hz').2
    exact Option.some.inj he⟩

private lemma graphTable_word {I S : Type} [Fintype I] [Fintype S] [DecidableEq I] [DecidableEq S]
    (O : I → Option S) : TableWord (graphTable O).val = O := by
  funext a
  cases h : O a with
  | none =>
    unfold TableWord
    have he : ¬∃ z, (a,z) ∈ (graphTable O).val := by simp [graphTable,h]
    rw [dif_neg he]
  | some z => exact (word_spec (graphTable O) a z).mpr (by simp [graphTable,h])

private lemma table_evaluation {I S : Type} [Fintype I] [Fintype S] [DecidableEq I] [DecidableEq S]
    (T : ResponseTable I S) (O : I → Option S) :
    MvPolynomial.eval (Indicators O) (TableMonomial T) =
      if T.val ⊆ (graphTable O).val then 1 else 0 := by
  simp only [TableMonomial, map_prod, MvPolynomial.eval_X]
  split_ifs with hT
  · apply prod_eq_one
    intro az haz
    have he := (mem_filter.mp (hT haz)).2
    simp only [Indicators, he, ite_true]
  · have hex : ∃ az ∈ T.val, O az.1 ≠ some az.2 := by
      obtain ⟨az,haz,hn⟩ := Finset.not_subset.mp hT
      exact ⟨az,haz,by simpa only [graphTable, mem_filter, mem_univ, true_and] using hn⟩
    obtain ⟨az,haz,he⟩ := hex
    apply prod_eq_zero haz
    simp only [Indicators, he, ite_false]

private lemma canonical_evaluation {I S : Type} [Fintype I] [Fintype S] [DecidableEq I] [DecidableEq S]
    {k w q : ℕ} (E : Encoding S k) (A : Algorithm I k w q)
    (out : (I × Bits k) × Fin w → Bool) (O : I → Option S) :
    MvPolynomial.eval (Indicators O) (CanonicalPolynomial E A out) = Accept E A out O := by
  unfold CanonicalPolynomial
  simp only [map_sum, map_mul, MvPolynomial.eval_C, table_evaluation, mul_ite, mul_one, mul_zero,
    ← sum_filter]
  calc
    _ = ∑ U ∈ (graphTable O).val.powerset,
        mobiusCoeff (fun V => Accept E A out (TableWord V)) U := by
      apply sum_bij (fun T _ => T.val)
      · intro T hT
        exact mem_powerset.mpr (mem_filter.mp hT).2
      · intro T hT U hU he
        exact Subtype.ext he
      · intro U hU
        have hsub := mem_powerset.mp hU
        let T : ResponseTable I S := ⟨U,fun a z z' hz hz' =>
          (graphTable O).property a z z' (hsub hz) (hsub hz')⟩
        exact ⟨T,mem_filter.mpr ⟨mem_univ _,hsub⟩,rfl⟩
      · intro T hT
        rfl
    _ = _ := by rw [mobius_reconstruct, graphTable_word]

private lemma subtable_indicator {I S : Type} [Fintype I] [Fintype S] [DecidableEq I] [DecidableEq S]
    (T : ResponseTable I S) (U : Finset (I × S)) (hUT : U ⊆ T.val) (az : I × S) :
    Indicators (TableWord U) az = if az ∈ U then 1 else 0 := by
  let R : ResponseTable I S := ⟨U,fun a z z' hz hz' => T.property a z z' (hUT hz) (hUT hz')⟩
  change (if TableWord R.val az.1 = some az.2 then (1 : ℝ) else 0) = _
  simp only [word_spec]
  rfl

private lemma monomial_mobius_zero {I S : Type} [Fintype I] [Fintype S] [DecidableEq I] [DecidableEq S]
    (T : ResponseTable I S) (d : (I × S) →₀ ℕ)
    (hd : (∑ az ∈ d.support, d az) < T.val.card) :
    mobiusCoeff (fun U => MvPolynomial.eval (Indicators (TableWord U))
      (MvPolynomial.monomial d (1 : ℝ))) T.val = 0 := by
  have hcard : d.support.card ≤ ∑ az ∈ d.support, d az := by
    calc
      _ = ∑ az ∈ d.support, 1 := by simp
      _ ≤ _ := sum_le_sum (fun az haz => Nat.one_le_iff_ne_zero.mpr (Finsupp.mem_support_iff.mp haz))
  have hnot : ¬ T.val ⊆ d.support := by intro hsub; have := card_le_card hsub; omega
  obtain ⟨a,ha,had⟩ := Finset.not_subset.mp hnot
  apply mobius_cancel _ T.val a ha
  intro U hU
  have hUT : U ⊆ T.val := hU.trans (erase_subset _ _)
  have hinsert : insert a U ⊆ T.val := insert_subset_iff.mpr ⟨ha,hUT⟩
  simp only [MvPolynomial.eval_monomial, one_mul, Finsupp.prod]
  apply prod_congr rfl
  intro az haz
  have hne : az ≠ a := by intro he; exact had (he ▸ haz)
  simp only [subtable_indicator T _ hinsert, subtable_indicator T _ hUT]
  simp only [mem_insert, hne, false_or]

private lemma mobius_sum {α β : Type} [DecidableEq α] (T : Finset α) (s : Finset β)
    (c : β → ℝ) (f : β → Finset α → ℝ) :
    mobiusCoeff (fun U => ∑ b ∈ s, c b * f b U) T = ∑ b ∈ s, c b * mobiusCoeff (f b) T := by
  unfold mobiusCoeff
  simp_rw [mul_sum]
  rw [sum_comm]
  apply sum_congr rfl
  intro b hb
  apply sum_congr rfl
  intro U hU
  ring

private lemma polynomial_mobius_zero {I S : Type} [Fintype I] [Fintype S] [DecidableEq I] [DecidableEq S]
    (T : ResponseTable I S) (P : MvPolynomial (I × S) ℝ) (hT : P.totalDegree < T.val.card) :
    mobiusCoeff (fun U => MvPolynomial.eval (Indicators (TableWord U)) P) T.val = 0 := by
  have he : ∀ U, MvPolynomial.eval (Indicators (TableWord U)) P =
      ∑ d ∈ P.support, P.coeff d * MvPolynomial.eval (Indicators (TableWord U))
        (MvPolynomial.monomial d (1 : ℝ)) := by
    intro U
    conv_lhs => rw [P.as_sum]
    simp only [map_sum, MvPolynomial.eval_monomial, one_mul]
  simp_rw [he]
  rw [mobius_sum]
  apply sum_eq_zero
  intro d hd
  rw [monomial_mobius_zero T d ?_, mul_zero]
  exact (MvPolynomial.le_totalDegree hd).trans_lt hT

private lemma table_degree {I S : Type} [Fintype I] [Fintype S] [DecidableEq I] [DecidableEq S]
    (T : ResponseTable I S) : (TableMonomial T).totalDegree ≤ T.val.card := by
  unfold TableMonomial
  apply (MvPolynomial.totalDegree_finsetProd _ _).trans_eq
  simp

private lemma table_multilinear {I S : Type} [Fintype I] [Fintype S] [DecidableEq I] [DecidableEq S]
    (T : ResponseTable I S) (az : I × S) : (TableMonomial T).degreeOf az ≤ 1 := by
  unfold TableMonomial
  apply (MvPolynomial.degreeOf_prod_le _ _ _).trans
  simp only [MvPolynomial.degreeOf_X]
  by_cases haz : az ∈ T.val
  · simp [haz, eq_comm]
  · simp [haz, eq_comm]

private lemma canonical_from_polynomial {I S : Type} [Fintype I] [Fintype S] [DecidableEq I] [DecidableEq S]
    {k w q r : ℕ} (E : Encoding S k) (A : Algorithm I k w q)
    (out : (I × Bits k) × Fin w → Bool)
    (P : MvPolynomial (I × S) ℝ) (hP : P.totalDegree ≤ r)
    (heval : ∀ O : I → Option S, MvPolynomial.eval (Indicators O) P = Accept E A out O) :
    (CanonicalPolynomial E A out).totalDegree ≤ r ∧
    (∀ az, (CanonicalPolynomial E A out).degreeOf az ≤ 1) ∧
    ∀ O : I → Option S,
      MvPolynomial.eval (Indicators O) (CanonicalPolynomial E A out) = Accept E A out O := by
  refine ⟨?_, ?_, canonical_evaluation E A out⟩
  · unfold CanonicalPolynomial
    apply (MvPolynomial.totalDegree_finsetSum _ _).trans
    apply Finset.sup_le
    intro T hT
    by_cases hsize : T.val.card ≤ r
    · apply (MvPolynomial.totalDegree_mul _ _).trans
      simpa only [MvPolynomial.totalDegree_C, zero_add] using (table_degree T).trans hsize
    · have hz : CanonicalCoeff E A out T = 0 := by
        change mobiusCoeff (fun U => Accept E A out (TableWord U)) T.val = 0
        simp_rw [← heval]
        exact polynomial_mobius_zero T P (hP.trans_lt (Nat.lt_of_not_ge hsize))
      rw [hz, map_zero, zero_mul, MvPolynomial.totalDegree_zero]
      exact Nat.zero_le _
  · intro az
    unfold CanonicalPolynomial
    apply (MvPolynomial.degreeOf_sum_le _ _ _).trans
    apply Finset.sup_le
    intro T hT
    exact (MvPolynomial.degreeOf_C_mul_le _ _ _).trans (table_multilinear T az)

end
end QuantumBipartiteTesting.Bipartiteness

open QuantumBipartiteTesting.Bipartiteness

theorem solution {I S : Type} [Fintype I] [Fintype S] [DecidableEq I] [DecidableEq S]
    {k w q : ℕ} (E : Encoding S k) (A : Algorithm I k w q)
    (out : (I × Bits k) × Fin w → Bool) :
    (CanonicalPolynomial E A out).totalDegree ≤ 2*q ∧
    (∀ az, (CanonicalPolynomial E A out).degreeOf az ≤ 1) ∧
    ∀ O : I → Option S,
      MvPolynomial.eval (Indicators O) (CanonicalPolynomial E A out) = Accept E A out O := by
  obtain ⟨P,hdegree,heval⟩ := actual_acceptance_polynomial E A out
  exact canonical_from_polynomial E A out P hdegree heval
