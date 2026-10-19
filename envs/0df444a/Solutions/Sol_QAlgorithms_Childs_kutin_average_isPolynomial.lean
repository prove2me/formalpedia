-- Prove2me | solution 1 for QAlgorithms.Childs.kutin_average_isPolynomial
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-17T21:18:23.87081+00:00
-- url     : https://prove2.me/submissions/d5f7a3c4-cca8-4815-b2a9-b15f017a9745

import Theorems.Thm_QAlgorithms_Childs_kutin_monomial_count

open Finset MvPolynomial
open QAlgorithms

set_option maxRecDepth 2000
set_option maxHeartbeats 1200000

private lemma degree_sum {ι : Type*} (S : Finset ι)
    (f : ι → MvPolynomial (Fin 3) ℝ) (D : ℕ)
    (h : ∀ i ∈ S, (f i).totalDegree ≤ D) : (∑ i ∈ S, f i).totalDegree ≤ D :=
  totalDegree_finsetSum_le h

private lemma degree_prod {ι : Type*} (S : Finset ι)
    (f : ι → MvPolynomial (Fin 3) ℝ) (d : ι → ℕ)
    (h : ∀ i ∈ S, (f i).totalDegree ≤ d i) :
    (∏ i ∈ S, f i).totalDegree ≤ ∑ i ∈ S, d i :=
  (totalDegree_finsetProd S f).trans (sum_le_sum h)

private lemma degree_sub (P Q : MvPolynomial (Fin 3) ℝ) (d : ℕ)
    (hP : P.totalDegree ≤ d) (hQ : Q.totalDegree ≤ d) : (P - Q).totalDegree ≤ d := by
  simpa only [sub_eq_add_neg, totalDegree_neg] using
    (totalDegree_add P (-Q)).trans (max_le hP (by simpa using hQ))

private noncomputable def blockPoly (M A : MvPolynomial (Fin 3) ℝ)
    {ι : Type*} (U : Finset ι) (c : ι → ℕ) : MvPolynomial (Fin 3) ℝ :=
  (∏ q ∈ range U.card, (M - C (q : ℝ) * A)) *
    ∏ j ∈ U, ∏ q ∈ range (c j - 1), (A - C ((q : ℝ) + 1))

private lemma block_degree {ι : Type*} (U : Finset ι) (c : ι → ℕ)
    (hc : ∀ j ∈ U, 0 < c j) (M A : MvPolynomial (Fin 3) ℝ)
    (hM : M.totalDegree ≤ 1) (hA : A.totalDegree ≤ 1) :
    (blockPoly M A U c).totalDegree ≤ ∑ j ∈ U, c j := by
  have h1 : (∏ q ∈ range U.card, (M - C (q : ℝ) * A)).totalDegree ≤ U.card := by
    simpa using degree_prod (range U.card) _ (fun _ => 1) (fun q _ =>
      degree_sub _ _ 1 hM ((totalDegree_mul (C (q : ℝ)) A).trans (by rw [totalDegree_C, zero_add]; exact hA)))
  have h2 : (∏ j ∈ U, ∏ q ∈ range (c j - 1), (A - C ((q : ℝ) + 1))).totalDegree
      ≤ ∑ j ∈ U, (c j - 1) := by
    apply degree_prod
    intro j _
    simpa using degree_prod (range (c j - 1)) _ (fun _ => 1)
      (fun q _ => degree_sub A (C ((q : ℝ) + 1)) 1 hA (by rw [totalDegree_C]; omega))
  have hcard : U.card + ∑ j ∈ U, (c j - 1) = ∑ j ∈ U, c j := by
    rw [card_eq_sum_ones, ← sum_add_distrib]
    apply sum_congr rfl
    intro j hj
    have := hc j hj
    omega
  exact (totalDegree_mul _ _).trans ((Nat.add_le_add h1 h2).trans_eq hcard)

private lemma cancel_block {ι : Type*} (U : Finset ι) (c : ι → ℕ)
    (hc : ∀ j ∈ U, 0 < c j) (M A : ℝ) (hA : A ≠ 0) :
    (∏ q ∈ range U.card, (M / A - q)) *
      (∏ j ∈ U, ∏ q ∈ range (c j), (A - q)) =
    (∏ q ∈ range U.card, (M - (q : ℝ) * A)) *
      ∏ j ∈ U, ∏ q ∈ range (c j - 1), (A - ((q : ℝ) + 1)) := by
  have hf : ∀ j ∈ U, (∏ q ∈ range (c j), (A - q)) =
      A * ∏ q ∈ range (c j - 1), (A - ((q : ℝ) + 1)) := by
    intro j hj
    have hd : c j = (c j - 1) + 1 := by have := hc j hj; omega
    rw [hd, prod_range_succ']
    simp only [Nat.cast_zero, sub_zero, Nat.add_sub_cancel, Nat.cast_add, Nat.cast_one]
    ring
  rw [prod_congr rfl hf, prod_mul_distrib, prod_const]
  calc
    _ = ((∏ q ∈ range U.card, (M / A - q)) * A ^ U.card) *
        ∏ j ∈ U, ∏ q ∈ range (c j - 1), (A - ((q : ℝ) + 1)) := by ring
    _ = _ := by
      congr 1
      rw [show A ^ U.card = ∏ _q ∈ range U.card, A by simp, ← prod_mul_distrib]
      apply prod_congr rfl
      intro q _
      field_simp

private noncomputable def patternPoly {n : ℕ} (E : Finset (Fin n × Fin n)) :
    MvPolynomial (Fin 3) ℝ :=
  let J := E.image Prod.snd
  let c := fun j => (E.filter (fun e => e.2 = j)).card
  C (((n.descFactorial E.card : ℝ) * (n.descFactorial J.card : ℝ))⁻¹) *
    ∑ U ∈ J.powerset,
      blockPoly (X 0) (X 1) U c * blockPoly (C (n : ℝ) - X 0) (X 2) (J \ U) c

private lemma pattern_degree {n : ℕ} (E : Finset (Fin n × Fin n)) :
    (patternPoly E).totalDegree ≤ E.card := by
  let J := E.image Prod.snd
  let c := fun j => (E.filter (fun e => e.2 = j)).card
  have hc : ∀ j ∈ J, 0 < c j := by
    intro j hj
    obtain ⟨e, he, rfl⟩ := mem_image.mp hj
    exact card_pos.mpr ⟨e, mem_filter.mpr ⟨he, rfl⟩⟩
  have hsum : ∑ j ∈ J, c j = E.card := by
    simpa [J, c] using (card_eq_sum_card_image Prod.snd E).symm
  apply (totalDegree_mul _ _).trans
  simp only [totalDegree_C, zero_add]
  apply degree_sum
  intro U hU
  have hsub : U ⊆ J := mem_powerset.mp hU
  have h1 := block_degree U c (fun j hj => hc j (hsub hj)) (X 0) (X 1) (by simp) (by simp)
  have h2 := block_degree (J \ U) c (fun j hj => hc j (mem_sdiff.mp hj).1)
    (C (n : ℝ) - X 0) (X 2) (degree_sub _ _ 1 (by rw [totalDegree_C]; omega) (by simp)) (by simp)
  exact (totalDegree_mul _ _).trans ((Nat.add_le_add h1 h2).trans_eq
    (by rw [add_comm, sum_sdiff hsub, hsum]))

private lemma pattern_eval {n m a b : ℕ} (h : ValidKutinTriple n m a b)
    (E : Finset (Fin n × Fin n))
    (hE : ∀ e ∈ E, ∀ f ∈ E, e.1 = f.1 → e.2 = f.2) :
    eval ![(m : ℝ), (a : ℝ), (b : ℝ)] (patternPoly E) =
      (((n.factorial : ℝ) ^ 2)⁻¹ * ∑ σ : Equiv.Perm (Fin n),
        ∑ τ : Equiv.Perm (Fin n), ∏ e ∈ E, kutinDelta n m a b σ τ e) := by
  let J := E.image Prod.snd
  let c := fun j => (E.filter (fun e => e.2 = j)).card
  have hc : ∀ j ∈ J, 0 < c j := by
    intro j hj
    obtain ⟨e, he, rfl⟩ := mem_image.mp hj
    exact card_pos.mpr ⟨e, mem_filter.mpr ⟨he, rfl⟩⟩
  have ha : (a : ℝ) ≠ 0 := by have := h.2.1; exact_mod_cast (by omega : a ≠ 0)
  have hb : (b : ℝ) ≠ 0 := by have := h.2.2.1; exact_mod_cast (by omega : b ≠ 0)
  rw [QAlgorithms.Childs.kutin_monomial_count n m a b h E hE]
  simp only [patternPoly, map_mul, map_sum, map_prod, eval_C, eval_X, map_sub,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, blockPoly]
  congr 1
  apply sum_congr rfl
  intro U hU
  have hsub : U ⊆ J := mem_powerset.mp hU
  have h1 := cancel_block U c (fun j hj => hc j (hsub hj)) (m : ℝ) (a : ℝ) ha
  have h2 := cancel_block (J \ U) c (fun j hj => hc j (mem_sdiff.mp hj).1)
    ((n : ℝ) - m) (b : ℝ) hb
  change _ = _
  rw [show _ * _ * _ * _ =
    ((∏ q ∈ range U.card, ((m : ℝ) / a - q)) *
      (∏ j ∈ U, ∏ q ∈ range (c j), ((a : ℝ) - q))) *
    ((∏ q ∈ range (J \ U).card, (((n : ℝ) - m) / b - q)) *
      (∏ j ∈ J \ U, ∏ q ∈ range (c j), ((b : ℝ) - q))) by ring]
  rw [h1, h2]
  simp [J, c]

private lemma delta_power {n m a b : ℕ} (σ τ : Equiv.Perm (Fin n))
    (e : Fin n × Fin n) {d : ℕ} (hd : d ≠ 0) :
    kutinDelta n m a b σ τ e ^ d = kutinDelta n m a b σ τ e := by
  unfold kutinDelta
  split_ifs <;> simp [hd]

private lemma conflict_zero {n m a b : ℕ} (E : Finset (Fin n × Fin n))
    (hE : ¬ ∀ e ∈ E, ∀ f ∈ E, e.1 = f.1 → e.2 = f.2)
    (σ τ : Equiv.Perm (Fin n)) : (∏ e ∈ E, kutinDelta n m a b σ τ e) = 0 := by
  classical
  push Not at hE
  obtain ⟨e, he, f, hf, hef, hne⟩ := hE
  by_cases hval : τ (kutinInput n m a b (σ e.1)) = e.2
  · apply prod_eq_zero hf
    have hvalf : τ (kutinInput n m a b (σ f.1)) ≠ f.2 := by
      rw [← hef, hval]
      exact hne
    simp [kutinDelta, hvalf]
  · apply prod_eq_zero he
    simp [kutinDelta, hval]

private lemma monomial_polynomial {n : ℕ} (d : (Fin n × Fin n) →₀ ℕ) :
    ∃ Q : MvPolynomial (Fin 3) ℝ, Q.totalDegree ≤ d.sum (fun _ k => k) ∧
      ∀ m a b : ℕ, ValidKutinTriple n m a b →
        eval ![(m : ℝ), (a : ℝ), (b : ℝ)] Q =
          kutinAverage (monomial d 1) m a b := by
  classical
  have hcard : d.support.card ≤ d.sum (fun _ k => k) := by
    change d.support.card ≤ ∑ e ∈ d.support, d e
    rw [card_eq_sum_ones]
    apply sum_le_sum
    intro e he
    have := Finsupp.mem_support_iff.mp he
    omega
  have heval : ∀ m a b (σ τ : Equiv.Perm (Fin n)),
      eval (kutinDelta n m a b σ τ) (monomial d (1 : ℝ)) =
        ∏ e ∈ d.support, kutinDelta n m a b σ τ e := by
    intro m a b σ τ
    rw [eval_monomial, one_mul]
    apply prod_congr rfl
    intro e he
    exact delta_power σ τ e (Finsupp.mem_support_iff.mp he)
  by_cases hE : ∀ e ∈ d.support, ∀ f ∈ d.support, e.1 = f.1 → e.2 = f.2
  · refine ⟨patternPoly d.support, (pattern_degree _).trans hcard, ?_⟩
    intro m a b h
    simpa only [kutinAverage, heval] using pattern_eval h d.support hE
  · refine ⟨0, by simp, ?_⟩
    intro m a b _
    simp only [map_zero, kutinAverage, heval, conflict_zero _ hE, sum_const_zero, mul_zero]

private lemma average_expansion {n : ℕ} (p : MvPolynomial (Fin n × Fin n) ℝ)
    (m a b : ℕ) :
    kutinAverage p m a b = ∑ d ∈ p.support, coeff d p *
      kutinAverage (monomial d 1) m a b := by
  classical
  unfold kutinAverage
  conv_lhs => arg 2; arg 2; ext σ; arg 2; ext τ; rw [← support_sum_monomial_coeff p]
  simp only [map_sum, eval_monomial, one_mul]
  have hs : (∑ σ : Equiv.Perm (Fin n), ∑ τ : Equiv.Perm (Fin n),
      ∑ d ∈ p.support, coeff d p * d.prod (fun e k => kutinDelta n m a b σ τ e ^ k)) =
      ∑ d ∈ p.support, ∑ σ : Equiv.Perm (Fin n), ∑ τ : Equiv.Perm (Fin n),
        coeff d p * d.prod (fun e k => kutinDelta n m a b σ τ e ^ k) := by
    calc
      _ = ∑ σ : Equiv.Perm (Fin n), ∑ d ∈ p.support, ∑ τ : Equiv.Perm (Fin n),
          coeff d p * d.prod (fun e k => kutinDelta n m a b σ τ e ^ k) := by
        apply sum_congr rfl
        intro σ _
        exact sum_comm
      _ = _ := sum_comm
  rw [hs, mul_sum]
  apply sum_congr rfl
  intro d _
  simp only [mul_sum, mul_left_comm]

theorem solution (n : ℕ) (p : MvPolynomial (Fin n × Fin n) ℝ) :
    ∃ Q : MvPolynomial (Fin 3) ℝ, Q.totalDegree ≤ p.totalDegree ∧
      ∀ m a b : ℕ, ValidKutinTriple n m a b →
        eval ![(m : ℝ), (a : ℝ), (b : ℝ)] Q = kutinAverage p m a b := by
  classical
  choose Q hdegree heval using fun d : (Fin n × Fin n) →₀ ℕ => monomial_polynomial d
  refine ⟨∑ d ∈ p.support, C (coeff d p) * Q d, ?_, ?_⟩
  · apply degree_sum
    intro d hd
    exact (totalDegree_mul _ _).trans (by
      rw [totalDegree_C, zero_add]
      exact (hdegree d).trans (le_totalDegree hd))
  · intro m a b h
    rw [average_expansion p m a b]
    simp only [map_sum, map_mul, eval_C]
    apply sum_congr rfl
    intro d _
    rw [heval d m a b h]
