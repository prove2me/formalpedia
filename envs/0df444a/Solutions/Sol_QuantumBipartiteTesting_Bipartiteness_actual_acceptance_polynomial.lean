-- Prove2me | solution 1 for QuantumBipartiteTesting.Bipartiteness.actual_acceptance_polynomial
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T12:52:57.712667+00:00
-- url     : https://prove2.me/submissions/63689c17-f73c-4913-831c-3faa147c1e43

import Definitions.Def_QuantumBipartiteTesting_Bipartiteness_Query
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency.types false
namespace QuantumBipartiteTesting.Bipartiteness
open Finset MvPolynomial
noncomputable section

private def complexIndicators {I S : Type} [DecidableEq S] (O : I → Option S) (az : I × S) : ℂ :=
  (Indicators O az : ℂ)

private def responsePoly {I S : Type} [Fintype S] (a : I) (f : Option S → ℂ) : MvPolynomial (I × S) ℂ :=
  C (f none) + ∑ z : S, C (f (some z)-f none) * X (a,z)

private lemma response_degree {I S : Type} [Fintype S] (a : I) (f : Option S → ℂ) :
    (responsePoly a f).totalDegree ≤ 1 := by
  unfold responsePoly
  apply (totalDegree_add _ _).trans
  apply max_le
  · simp
  · apply (totalDegree_finsetSum _ _).trans
    apply Finset.sup_le
    intro z hz
    apply (totalDegree_mul _ _).trans
    simp only [totalDegree_C, totalDegree_X]
    norm_num

private lemma response_eval {I S : Type} [Fintype S] [DecidableEq S]
    (a : I) (f : Option S → ℂ) (O : I → Option S) :
    MvPolynomial.eval (complexIndicators O) (responsePoly a f) = f (O a) := by
  classical
  cases h : O a with
  | none => simp [responsePoly, complexIndicators, Indicators, h]
  | some z =>
    have hi (s : S) : complexIndicators O (a,s) = if z = s then (1 : ℂ) else 0 := by
      by_cases hs : z = s
      · subst s
        simp [complexIndicators, Indicators, h]
      · simp [complexIndicators, Indicators, h, hs]
    simp only [responsePoly, map_add, map_sum, map_mul, eval_C, eval_X]
    simp_rw [hi]
    simp [mul_ite, eq_comm]

private def partPoly {σ : Type} (f : ℂ → ℝ) (P : MvPolynomial σ ℂ) : MvPolynomial σ ℝ :=
  ∑ d ∈ P.support, monomial d (f (P.coeff d))

private lemma part_degree {σ : Type} (f : ℂ → ℝ) (P : MvPolynomial σ ℂ) :
    (partPoly f P).totalDegree ≤ P.totalDegree := by
  unfold partPoly
  apply (totalDegree_finsetSum _ _).trans
  apply Finset.sup_le
  intro d hd
  exact (totalDegree_monomial_le _ _).trans (le_totalDegree hd)

private lemma real_monomial_product {σ : Type} (d : σ →₀ ℕ) (x : σ → ℝ) :
    (∏ i ∈ d.support, (x i : ℂ)^d i) = ((∏ i ∈ d.support, x i ^ d i : ℝ) : ℂ) := by
  classical
  push_cast
  rfl

private lemma real_part_eval {σ : Type} (P : MvPolynomial σ ℂ) (x : σ → ℝ) :
    MvPolynomial.eval x (partPoly Complex.re P) =
      (MvPolynomial.eval (fun i => (x i : ℂ)) P).re := by
  classical
  conv_rhs => rw [MvPolynomial.eval_eq]
  simp only [partPoly, map_sum, eval_monomial, Finsupp.prod, Complex.re_sum, real_monomial_product,
    Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]

private lemma imag_part_eval {σ : Type} (P : MvPolynomial σ ℂ) (x : σ → ℝ) :
    MvPolynomial.eval x (partPoly Complex.im P) =
      (MvPolynomial.eval (fun i => (x i : ℂ)) P).im := by
  classical
  conv_rhs => rw [MvPolynomial.eval_eq]
  simp only [partPoly, map_sum, eval_monomial, Finsupp.prod, Complex.im_sum, real_monomial_product,
    Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, mul_zero, zero_add]

private abbrev QueryBasis (I : Type) (k w : ℕ) := (I × Bits k) × Fin w

private def fixedPoly {B σ : Type} [Fintype B] (U : Matrix B B ℂ)
    (P : B → MvPolynomial σ ℂ) (z : B) : MvPolynomial σ ℂ :=
  ∑ r, C (U z r) * P r

private lemma fixed_degree {B σ : Type} [Fintype B] (U : Matrix B B ℂ)
    (P : B → MvPolynomial σ ℂ) (r : ℕ) (hP : ∀ z, (P z).totalDegree ≤ r) (z : B) :
    (fixedPoly U P z).totalDegree ≤ r := by
  unfold fixedPoly
  apply (totalDegree_finsetSum _ _).trans
  apply Finset.sup_le
  intro y hy
  apply (totalDegree_mul _ _).trans
  simpa only [totalDegree_C, zero_add] using hP y

private lemma fixed_eval {B σ : Type} [Fintype B] (U : Matrix B B ℂ)
    (P : B → MvPolynomial σ ℂ) (x : σ → ℂ) (z : B) :
    MvPolynomial.eval x (fixedPoly U P z) = (U.mulVec (fun r => MvPolynomial.eval x (P r))) z := by
  simp only [fixedPoly, map_sum, map_mul, eval_C, Matrix.mulVec, dotProduct]

private def queryPoly {I S : Type} [Fintype I] [Fintype S] [DecidableEq I] [DecidableEq S]
    {k w : ℕ} (E : Encoding S k) (z r : QueryBasis I k w) : MvPolynomial (I × S) ℂ :=
  responsePoly r.1.1 (fun s => QAlgorithms.xorOracle (fun _ : I => E.code s) z.1 r.1 *
    (1 : Matrix (Fin w) (Fin w) ℂ) z.2 r.2)

private lemma query_eval {I S : Type} [Fintype I] [Fintype S] [DecidableEq I] [DecidableEq S]
    {k w : ℕ} (E : Encoding S k) (O : I → Option S) (z r : QueryBasis I k w) :
    MvPolynomial.eval (complexIndicators O) (queryPoly E z r) =
      Matrix.kronecker (QAlgorithms.xorOracle (E.code ∘ O)) (1 : Matrix (Fin w) (Fin w) ℂ) z r := by
  rw [queryPoly, response_eval]
  rfl

private def oraclePolyState {I S : Type} [Fintype I] [Fintype S] [DecidableEq I] [DecidableEq S]
    {k w : ℕ} (E : Encoding S k) (P : QueryBasis I k w → MvPolynomial (I × S) ℂ)
    (z : QueryBasis I k w) : MvPolynomial (I × S) ℂ :=
  ∑ r, queryPoly E z r * P r

private lemma oracle_degree {I S : Type} [Fintype I] [Fintype S] [DecidableEq I] [DecidableEq S]
    {k w : ℕ} (E : Encoding S k) (P : QueryBasis I k w → MvPolynomial (I × S) ℂ)
    (r : ℕ) (hP : ∀ z, (P z).totalDegree ≤ r) (z : QueryBasis I k w) :
    (oraclePolyState E P z).totalDegree ≤ r+1 := by
  unfold oraclePolyState
  apply (totalDegree_finsetSum _ _).trans
  apply Finset.sup_le
  intro y hy
  apply (totalDegree_mul _ _).trans
  have hq : (queryPoly E z y).totalDegree ≤ 1 := response_degree _ _
  have hp := hP y
  omega

private lemma oracle_eval {I S : Type} [Fintype I] [Fintype S] [DecidableEq I] [DecidableEq S]
    {k w : ℕ} (E : Encoding S k) (P : QueryBasis I k w → MvPolynomial (I × S) ℂ)
    (O : I → Option S) (z : QueryBasis I k w) :
    MvPolynomial.eval (complexIndicators O) (oraclePolyState E P z) =
      (Matrix.kronecker (QAlgorithms.xorOracle (E.code ∘ O)) (1 : Matrix (Fin w) (Fin w) ℂ)).mulVec
        (fun r => MvPolynomial.eval (complexIndicators O) (P r)) z := by
  simp only [oraclePolyState, map_sum, map_mul, query_eval, Matrix.mulVec, dotProduct]

private def statePoly {I S : Type} [Fintype I] [Fintype S] [DecidableEq I] [DecidableEq S]
    {k w q : ℕ} (E : Encoding S k) (A : Algorithm I k w q) :
    Fin (q+1) → QueryBasis I k w → MvPolynomial (I × S) ℂ :=
  Fin.induction (fixedPoly (A.U 0 : Matrix _ _ ℂ) (fun z => C (A.start z)))
    (fun i P => fixedPoly (A.U i.succ : Matrix _ _ ℂ) (oraclePolyState E P))

private lemma state_degree {I S : Type} [Fintype I] [Fintype S] [DecidableEq I] [DecidableEq S]
    {k w q : ℕ} (E : Encoding S k) (A : Algorithm I k w q) :
    ∀ t, ∀ z, (statePoly E A t z).totalDegree ≤ t.val := by
  apply Fin.induction
  · intro z
    change (fixedPoly (A.U 0 : Matrix _ _ ℂ) (fun z => C (A.start z)) z).totalDegree ≤ 0
    exact fixed_degree _ _ 0 (fun _ => by simp) z
  · intro i ih z
    change (fixedPoly (A.U i.succ : Matrix _ _ ℂ)
      (oraclePolyState E (statePoly E A i.castSucc)) z).totalDegree ≤ i.val+1
    exact fixed_degree _ _ (i.val+1) (oracle_degree E _ i.val ih) z

private lemma state_eval {I S : Type} [Fintype I] [Fintype S] [DecidableEq I] [DecidableEq S]
    {k w q : ℕ} (E : Encoding S k) (A : Algorithm I k w q) (O : I → Option S) :
    ∀ t, ∀ z, MvPolynomial.eval (complexIndicators O) (statePoly E A t z) =
      A.stateAt (QAlgorithms.xorOracle (E.code ∘ O)) t z := by
  apply Fin.induction
  · intro z
    change MvPolynomial.eval (complexIndicators O)
      (fixedPoly (A.U 0 : Matrix _ _ ℂ) (fun z => C (A.start z)) z) = _
    rw [fixed_eval]
    simp only [eval_C]
    rfl
  · intro i ih z
    change MvPolynomial.eval (complexIndicators O) (fixedPoly (A.U i.succ : Matrix _ _ ℂ)
      (oraclePolyState E (statePoly E A i.castSucc)) z) = _
    rw [fixed_eval]
    simp_rw [oracle_eval, ih]
    rfl

private def acceptancePoly {I S : Type} [Fintype I] [Fintype S] [DecidableEq I] [DecidableEq S]
    {k w q : ℕ} (E : Encoding S k) (A : Algorithm I k w q)
    (out : QueryBasis I k w → Bool) : MvPolynomial (I × S) ℝ :=
  ∑ z ∈ univ.filter (fun z => out z = true),
    ((partPoly Complex.re (statePoly E A (Fin.last q) z))^2 +
      (partPoly Complex.im (statePoly E A (Fin.last q) z))^2)

private lemma acceptance_degree {I S : Type} [Fintype I] [Fintype S] [DecidableEq I] [DecidableEq S]
    {k w q : ℕ} (E : Encoding S k) (A : Algorithm I k w q)
    (out : QueryBasis I k w → Bool) : (acceptancePoly E A out).totalDegree ≤ 2*q := by
  unfold acceptancePoly
  apply (totalDegree_finsetSum _ _).trans
  apply Finset.sup_le
  intro z hz
  apply (totalDegree_add _ _).trans
  apply max_le
  · apply (totalDegree_pow _ _).trans
    exact Nat.mul_le_mul_left 2 ((part_degree Complex.re _).trans (state_degree E A (Fin.last q) z))
  · apply (totalDegree_pow _ _).trans
    exact Nat.mul_le_mul_left 2 ((part_degree Complex.im _).trans (state_degree E A (Fin.last q) z))

private lemma acceptance_eval {I S : Type} [Fintype I] [Fintype S] [DecidableEq I] [DecidableEq S]
    {k w q : ℕ} (E : Encoding S k) (A : Algorithm I k w q)
    (out : QueryBasis I k w → Bool) (O : I → Option S) :
    MvPolynomial.eval (Indicators O) (acceptancePoly E A out) = Accept E A out O := by
  simp only [acceptancePoly, map_sum, map_add, map_pow, real_part_eval, imag_part_eval]
  change (∑ z ∈ univ.filter (fun z => out z = true),
    ((MvPolynomial.eval (complexIndicators O) (statePoly E A (Fin.last q) z)).re^2 +
      (MvPolynomial.eval (complexIndicators O) (statePoly E A (Fin.last q) z)).im^2)) = _
  simp_rw [state_eval]
  unfold Accept QAlgorithms.QueryAlg.outputProb QAlgorithms.probEvent
  apply sum_congr rfl
  intro z hz
  simp only [QAlgorithms.prob, QAlgorithms.ket, EuclideanSpace.inner_single_left,
    map_one, one_mul, QAlgorithms.QueryAlg.finalState, Complex.sq_norm, Complex.normSq_apply]
  ring

end
end QuantumBipartiteTesting.Bipartiteness

open QuantumBipartiteTesting.Bipartiteness

theorem solution {I S : Type} [Fintype I] [Fintype S] [DecidableEq I] [DecidableEq S]
    {k w q : ℕ} (E : Encoding S k) (A : Algorithm I k w q)
    (out : (I × Bits k) × Fin w → Bool) :
    ∃ P : MvPolynomial (I × S) ℝ, P.totalDegree ≤ 2*q ∧
      ∀ O : I → Option S, MvPolynomial.eval (Indicators O) P = Accept E A out O := by
  exact ⟨acceptancePoly E A out, acceptance_degree E A out, acceptance_eval E A out⟩
