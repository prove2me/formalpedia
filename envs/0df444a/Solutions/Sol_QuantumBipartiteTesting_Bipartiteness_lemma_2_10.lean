-- Prove2me | solution 1 for QuantumBipartiteTesting.Bipartiteness.lemma_2_10
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T12:40:54.910964+00:00
-- url     : https://prove2.me/submissions/dc8d9b5c-0d2f-4ac9-9a1d-3fc5970b5ef7

import Definitions.Def_QuantumBipartiteTesting_Bipartiteness_Reduction
import Theorems.Thm_QuantumBipartiteTesting_Bipartiteness_lemma_2_9
set_option autoImplicit false
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency.types false
namespace QuantumBipartiteTesting.Bipartiteness
open Finset
noncomputable section

private lemma xor_star {I K : Type} [Fintype I] [Fintype K] [DecidableEq I] [DecidableEq K]
    [AddCommGroup K] (f : I → K) :
    star (QAlgorithms.xorOracle f) = QAlgorithms.xorOracle (-f) := by
  ext ⟨i,y⟩ ⟨j,z⟩
  by_cases h : i = j
  · subst j
    simp [QAlgorithms.xorOracle, Matrix.star_apply, eq_add_neg_iff_add_eq, eq_comm]
  · simp [QAlgorithms.xorOracle, Matrix.star_apply, h, Ne.symm h]

private lemma xor_unitary {I K : Type} [Fintype I] [Fintype K] [DecidableEq I] [DecidableEq K]
    [AddCommGroup K] (f : I → K) :
    QAlgorithms.xorOracle f ∈ Matrix.unitaryGroup (I × K) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff, xor_star]
  exact QAlgorithms.xorOracle_mul_neg f

private lemma final_norm {I : Type} [Fintype I] [DecidableEq I] {k w q : ℕ}
    (A : Algorithm I k w q) (O : Matrix (I × Bits k) (I × Bits k) ℂ)
    (hO : O ∈ Matrix.unitaryGroup (I × Bits k) ℂ) : ‖A.finalState O‖ = 1 := by
  have hK : Matrix.kronecker O (1 : Matrix (Fin w) (Fin w) ℂ) ∈
      Matrix.unitaryGroup ((I × Bits k) × Fin w) ℂ :=
    Matrix.kronecker_mem_unitary hO (one_mem _)
  have hstate : ∀ t, ‖A.stateAt O t‖ = 1 := by
    apply Fin.induction
    · change ‖QAlgorithms.act (A.U 0 : Matrix _ _ ℂ) A.start‖ = 1
      rw [QAlgorithms.act_norm_of_mem_unitaryGroup (A.U 0).property, A.start_unit]
    · intro i ih
      change ‖QAlgorithms.act (A.U i.succ : Matrix _ _ ℂ)
        (QAlgorithms.act (Matrix.kronecker O (1 : Matrix (Fin w) (Fin w) ℂ))
          (A.stateAt O i.castSucc))‖ = 1
      rw [QAlgorithms.act_norm_of_mem_unitaryGroup (A.U i.succ).property,
        QAlgorithms.act_norm_of_mem_unitaryGroup hK, ih]
  exact hstate _

private lemma accept_bounds {I S : Type} [Fintype I] [DecidableEq I] {k w q : ℕ}
    (E : Encoding S k) (A : Algorithm I k w q)
    (out : (I × Bits k) × Fin w → Bool) (O : I → Option S) :
    0 ≤ Accept E A out O ∧ Accept E A out O ≤ 1 := by
  have hnorm := final_norm A _ (xor_unitary (E.code ∘ O))
  constructor
  · exact sum_nonneg (fun _ _ => sq_nonneg _)
  · unfold Accept QAlgorithms.QueryAlg.outputProb QAlgorithms.probEvent
    calc
      _ ≤ ∑ z, QAlgorithms.prob (A.finalState (QAlgorithms.xorOracle (E.code ∘ O))) z := by
        apply sum_le_sum_of_subset_of_nonneg (filter_subset _ _)
        intro z hz hz'
        exact sq_nonneg _
      _ = ‖A.finalState (QAlgorithms.xorOracle (E.code ∘ O))‖^2 := by
        simp only [QAlgorithms.prob, QAlgorithms.ket, EuclideanSpace.inner_single_left,
          EuclideanSpace.norm_sq_eq, map_one, one_mul]
      _ = 1 := by rw [hnorm]; norm_num

private lemma coefficient_bound {I S : Type} [Fintype I] [Fintype S] [DecidableEq I] [DecidableEq S]
    {k w q : ℕ} (E : Encoding S k) (A : Algorithm I k w q)
    (out : (I × Bits k) × Fin w → Bool) (T : ResponseTable I S) :
    |CanonicalCoeff E A out T| ≤ (2 : ℝ)^T.val.card := by
  unfold CanonicalCoeff
  calc
    _ ≤ ∑ U ∈ T.val.powerset, |(-1 : ℝ)^(T.val.card-U.card) * Accept E A out (TableWord U)| :=
      abs_sum_le_sum_abs _ _
    _ ≤ ∑ U ∈ T.val.powerset, (1 : ℝ) := by
      apply sum_le_sum
      intro U hU
      rw [abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul,
        abs_of_nonneg (accept_bounds E A out _).1]
      exact (accept_bounds E A out _).2
    _ = _ := by simp

private def tableExponent {α : Type} [DecidableEq α] (s : Finset α) : α →₀ ℕ :=
  Finsupp.indicator s (fun _ _ => 1)

private lemma exponent_support {α : Type} [DecidableEq α] (s : Finset α) :
    (tableExponent s).support = s := by
  ext a
  simp [tableExponent, Finsupp.mem_support_iff, Finsupp.indicator_apply]

private lemma exponent_injective {α : Type} [DecidableEq α] :
    Function.Injective (tableExponent (α := α)) := by
  intro s t h
  simpa only [exponent_support] using congrArg Finsupp.support h

private lemma table_monomial {I S : Type} [Fintype I] [Fintype S] [DecidableEq I] [DecidableEq S]
    (T : ResponseTable I S) :
    TableMonomial T = MvPolynomial.monomial (tableExponent T.val) (1 : ℝ) := by
  simpa only [pow_one, TableMonomial, tableExponent] using
    (MvPolynomial.prod_X_pow (R := ℝ) (fun _ : I × S => 1) T.val)

private lemma canonical_coefficient {I S : Type} [Fintype I] [Fintype S] [DecidableEq I] [DecidableEq S]
    {k w q : ℕ} (E : Encoding S k) (A : Algorithm I k w q)
    (out : (I × Bits k) × Fin w → Bool) (T : ResponseTable I S) :
    (CanonicalPolynomial E A out).coeff (tableExponent T.val) = CanonicalCoeff E A out T := by
  unfold CanonicalPolynomial
  rw [MvPolynomial.coeff_sum]
  rw [sum_eq_single T]
  · simp [table_monomial]
  · intro U hU hUT
    have he : tableExponent U.val ≠ tableExponent T.val := by
      intro h
      exact hUT (Subtype.ext (exponent_injective h))
    simp [table_monomial, he]
  · simp

private lemma coefficient_zero {I S : Type} [Fintype I] [Fintype S] [DecidableEq I] [DecidableEq S]
    {k w q : ℕ} (E : Encoding S k) (A : Algorithm I k w q)
    (out : (I × Bits k) × Fin w → Bool) (T : ResponseTable I S) (hT : 2*q < T.val.card) :
    CanonicalCoeff E A out T = 0 := by
  have hdegree := (lemma_2_9 E A out).1
  rw [← canonical_coefficient E A out T]
  apply MvPolynomial.coeff_eq_zero_of_totalDegree_lt
  rw [exponent_support]
  have hsum : (∑ a ∈ T.val, tableExponent T.val a) = T.val.card := by
    simp [tableExponent, Finsupp.indicator_apply]
  rw [hsum]
  exact hdegree.trans_lt hT

private lemma finset_code_subset {α : Type} [DecidableEq α] {s t : Finset α} {r : ℕ}
    (hs : s.card ≤ r) (h : (fun i : Fin r => s.toList[i.val]?) = (fun i : Fin r => t.toList[i.val]?)) :
    s ⊆ t := by
  intro a ha
  obtain ⟨i,hi,hai⟩ := List.getElem_of_mem (show a ∈ s.toList by simpa using ha)
  have hi' : i < s.card := by simpa only [length_toList] using hi
  have hir : i < r := hi'.trans_le hs
  have he := congrFun h ⟨i,hir⟩
  have hs' : s.toList[i]? = some a := by rw [List.getElem?_eq_getElem hi, hai]
  have ht' : t.toList[i]? = some a := he.symm.trans hs'
  simpa only [mem_toList] using List.mem_of_getElem? ht'

private lemma small_tables_count {I S : Type} [Fintype I] [Fintype S] [DecidableEq I] [DecidableEq S]
    (r : ℕ) :
    ((univ : Finset (ResponseTable I S)).filter (fun T => T.val.card ≤ r)).card ≤
      (Fintype.card I * Fintype.card S + 1)^r := by
  classical
  let code := fun (T : ResponseTable I S) (i : Fin r) => T.val.toList[i.val]?
  calc
    _ ≤ (univ : Finset (Fin r → Option (I × S))).card := by
      apply card_le_card_of_injOn code
      · intro T hT
        exact mem_univ _
      · intro T hT U hU heq
        apply Subtype.ext
        exact Subset.antisymm
          (finset_code_subset (mem_filter.mp hT).2 heq)
          (finset_code_subset (mem_filter.mp hU).2 heq.symm)
    _ = _ := by simp

private lemma total_coefficient_bound {I S : Type} [Fintype I] [Fintype S] [DecidableEq I] [DecidableEq S]
    {k w q : ℕ} (E : Encoding S k) (A : Algorithm I k w q)
    (out : (I × Bits k) × Fin w → Bool) :
    (∑ T : ResponseTable I S, |CanonicalCoeff E A out T|) ≤
      (2*(Fintype.card I*Fintype.card S+1) : ℝ)^(2*q) := by
  classical
  let s := (univ : Finset (ResponseTable I S)).filter (fun T => T.val.card ≤ 2*q)
  have hcount : (s.card : ℝ) ≤ ((Fintype.card I * Fintype.card S + 1 : ℕ) : ℝ)^(2*q) := by
    exact_mod_cast small_tables_count (I := I) (S := S) (2*q)
  calc
    _ = ∑ T ∈ s, |CanonicalCoeff E A out T| := by
      symm
      apply sum_subset (filter_subset _ _)
      intro T hT hTs
      have hsize : 2*q < T.val.card := by simpa only [s, mem_filter, mem_univ, true_and, not_le] using hTs
      rw [coefficient_zero E A out T hsize, abs_zero]
    _ ≤ ∑ T ∈ s, (2 : ℝ)^(2*q) := by
      apply sum_le_sum
      intro T hT
      exact (coefficient_bound E A out T).trans
        (pow_le_pow_right₀ (by norm_num) (mem_filter.mp hT).2)
    _ = (s.card : ℝ) * (2 : ℝ)^(2*q) := by simp
    _ ≤ (((Fintype.card I * Fintype.card S + 1 : ℕ) : ℝ)^(2*q)) * (2 : ℝ)^(2*q) :=
      mul_le_mul_of_nonneg_right hcount (by positivity)
    _ = _ := by push_cast; rw [← mul_pow]; congr 1; ring

end
end QuantumBipartiteTesting.Bipartiteness

open QuantumBipartiteTesting.Bipartiteness Finset

theorem solution :
    (∀ (I S : Type) [Fintype I] [Fintype S] [DecidableEq I] [DecidableEq S],
      ∀ k w q : ℕ, ∀ E : Encoding S k, ∀ A : Algorithm I k w q,
      ∀ out : (I × Bits k) × Fin w → Bool, ∀ T : ResponseTable I S,
        |CanonicalCoeff E A out T| ≤ (2 : ℝ) ^ T.val.card) ∧
    (∀ a b : ℕ, ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ, 2 ≤ N →
      ∀ (I S : Type) [Fintype I] [Fintype S] [DecidableEq I] [DecidableEq S],
      Fintype.card I ≤ a*N → Fintype.card S ≤ b*N →
      ∀ k w q : ℕ, ∀ E : Encoding S k, ∀ A : Algorithm I k w q,
      ∀ out : (I × Bits k) × Fin w → Bool,
        (∑ T : ResponseTable I S, |CanonicalCoeff E A out T|) ≤ Real.exp (C*q*Real.log N)) := by
  constructor
  · intro I S _ _ _ _ k w q E A out T
    exact coefficient_bound E A out T
  · intro a b
    let D : ℝ := 2*((a : ℝ)*b+1)
    have hD : 0 < D := by dsimp [D]; positivity
    refine ⟨4*D+4,by positivity,?_⟩
    intro N hN I S _ _ _ _ hI hS k w q E A out
    have hNr : (1 : ℝ) < N := by exact_mod_cast hN
    have hlog : (1/2 : ℝ) ≤ Real.log N := by
      have h2N : (2 : ℝ) ≤ N := by exact_mod_cast hN
      have := Real.log_le_log (by norm_num : (0 : ℝ) < 2) h2N
      linarith [Real.log_two_gt_d9]
    have hK : ((Fintype.card I * Fintype.card S : ℕ) : ℝ) ≤ (a : ℝ)*b*(N : ℝ)^2 := by
      have hn := Nat.mul_le_mul hI hS
      have hnat : (a*N)*(b*N) = a*b*N^2 := by ring
      rw [hnat] at hn
      exact_mod_cast hn
    have hbase : (2*(Fintype.card I*Fintype.card S+1) : ℝ) ≤ D*(N : ℝ)^2 := by
      dsimp [D]
      push_cast at hK ⊢
      nlinarith
    have hDexp : D ≤ Real.exp (2*D*Real.log N) := by
      calc
        _ ≤ Real.exp D := by linarith [Real.add_one_le_exp D]
        _ ≤ _ := Real.exp_le_exp.mpr (by nlinarith)
    have hbaseexp : (2*(Fintype.card I*Fintype.card S+1) : ℝ) ≤
        Real.exp ((2*D+2)*Real.log N) := by
      calc
        _ ≤ D*(N : ℝ)^2 := hbase
        _ ≤ Real.exp (2*D*Real.log N) * (N : ℝ)^2 := mul_le_mul_of_nonneg_right hDexp (sq_nonneg _)
        _ = _ := by
          rw [show (N : ℝ)^2 = Real.exp ((2 : ℕ)*Real.log N) by
            rw [Real.exp_nat_mul, Real.exp_log (by linarith : (0 : ℝ) < N)], ← Real.exp_add]
          congr 1
          ring
    apply (total_coefficient_bound E A out).trans
    calc
      _ ≤ (Real.exp ((2*D+2)*Real.log N))^(2*q) :=
        pow_le_pow_left₀ (by positivity) hbaseexp _
      _ = _ := by
        rw [← Real.exp_nat_mul]
        congr 1
        push_cast
        ring
