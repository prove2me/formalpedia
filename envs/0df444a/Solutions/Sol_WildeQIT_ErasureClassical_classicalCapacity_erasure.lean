-- Prove2me | solution 1 for WildeQIT.ErasureClassical.classicalCapacity_erasure
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-11-13T11:46:42.116102+00:00
-- url     : https://prove2.me/submissions/95df2683-5592-43fe-b466-a88c8539b553

import Mathlib
import Definitions.Def_WildeQIT_ErasureClassical_classicalCapacity
import Definitions.Def_WildeQIT_ErasureClassical_erasureChannel

set_option autoImplicit false

namespace ErasureLib
open Matrix
open scoped ComplexOrder

variable {n : Type} [Fintype n] [DecidableEq n]

/-- `Tr(A X) ≤ Tr A · Tr X` for positive semidefinite `A`, `X` (spectral decomposition of `X`). -/
lemma tr_mul_le (A X : Matrix n n ℂ) (hA : A.PosSemidef) (hX : X.PosSemidef) :
    (A * X).trace.re ≤ A.trace.re * X.trace.re := by
  have hspec : X = (hX.1.eigenvectorUnitary : Matrix n n ℂ) *
      Matrix.diagonal (RCLike.ofReal ∘ hX.1.eigenvalues) * star (hX.1.eigenvectorUnitary : Matrix n n ℂ) := by
    have h := hX.1.spectral_theorem
    rw [Unitary.conjStarAlgAut_apply] at h
    exact h
  set U : Matrix n n ℂ := (hX.1.eigenvectorUnitary : Matrix n n ℂ) with hU
  set lam := hX.1.eigenvalues with hlam
  have hUU : star U * U = 1 := by
    simp [hU]
  have hUU' : U * star U = 1 := by
    simp [hU]
  set B : Matrix n n ℂ := star U * A * U with hB
  have hBpsd : B.PosSemidef := by
    have := hA.conjTranspose_mul_mul_same U
    simpa [hB, Matrix.star_eq_conjTranspose] using this
  have htrB : B.trace = A.trace := by
    rw [hB, Matrix.mul_assoc, Matrix.trace_mul_comm, Matrix.mul_assoc, hUU', Matrix.mul_one]
  have hXtr : X.trace.re = ∑ i, lam i := by
    rw [hX.1.trace_eq_sum_eigenvalues]
    simp [hlam]
  have hAX : (A * X).trace = ∑ i, B i i * (lam i : ℂ) := by
    have e1 : (A * X).trace = (B * Matrix.diagonal (RCLike.ofReal ∘ lam)).trace := by
      rw [hspec]
      calc (A * (U * Matrix.diagonal (RCLike.ofReal ∘ lam) * star U)).trace
          = ((A * U * Matrix.diagonal (RCLike.ofReal ∘ lam)) * star U).trace := by
            simp only [Matrix.mul_assoc]
        _ = (star U * (A * U * Matrix.diagonal (RCLike.ofReal ∘ lam))).trace :=
            Matrix.trace_mul_comm _ _
        _ = (B * Matrix.diagonal (RCLike.ofReal ∘ lam)).trace := by
            simp only [hB, Matrix.mul_assoc]
    rw [e1]
    simp [Matrix.trace, Matrix.mul_apply, Matrix.diagonal_apply]
  have hdiag : ∀ i, 0 ≤ (B i i).re := fun i => (Complex.nonneg_iff.mp (hBpsd.diag_nonneg)).1
  have hdiag_le : ∀ i, (B i i).re ≤ A.trace.re := by
    intro i
    rw [← htrB, Matrix.trace, Complex.re_sum]
    exact Finset.single_le_sum (f := fun j => (B j j).re) (fun j _ => hdiag j) (Finset.mem_univ i)
  have hlam0 : ∀ i, 0 ≤ lam i := fun i => hX.eigenvalues_nonneg i
  rw [hAX, Complex.re_sum, hXtr, Finset.mul_sum]
  refine Finset.sum_le_sum fun i _ => ?_
  have : (B i i * (lam i : ℂ)).re = (B i i).re * lam i := by simp
  rw [this]
  exact mul_le_mul_of_nonneg_right (hdiag_le i) (hlam0 i)


/-- Binomial variance, from Mathlib's Bernstein-polynomial variance. -/
lemma binom_var (n : ℕ) (p : ℝ) :
    ∑ k ∈ Finset.range (n + 1), ((n : ℝ) * p - k) ^ 2 * ((n.choose k : ℝ) * p ^ k * (1 - p) ^ (n - k))
      = n * p * (1 - p) := by
  have h := congrArg (Polynomial.eval p) (bernsteinPolynomial.variance ℝ n)
  simpa [Polynomial.eval_finsetSum, bernsteinPolynomial, nsmul_eq_mul, mul_assoc] using h

/-- Chebyshev tail bound for the binomial distribution. -/
lemma binom_tail (n : ℕ) (hn : 0 < n) (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (η : ℝ) (hη : 0 < η) :
    ∑ k ∈ (Finset.range (n + 1)).filter (fun k : ℕ => (n : ℝ) * η ≤ |(k : ℝ) - n * p|),
      (n.choose k : ℝ) * p ^ k * (1 - p) ^ (n - k) ≤ 1 / (n * η ^ 2) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hc : (0 : ℝ) < (n * η) ^ 2 := by positivity
  have hterm : ∀ k ∈ Finset.range (n + 1), 0 ≤ (n.choose k : ℝ) * p ^ k * (1 - p) ^ (n - k) := by
    intro k _
    have : 0 ≤ 1 - p := by linarith
    positivity
  calc ∑ k ∈ (Finset.range (n + 1)).filter (fun k : ℕ => (n : ℝ) * η ≤ |(k : ℝ) - n * p|),
        (n.choose k : ℝ) * p ^ k * (1 - p) ^ (n - k)
      ≤ ∑ k ∈ (Finset.range (n + 1)).filter (fun k : ℕ => (n : ℝ) * η ≤ |(k : ℝ) - n * p|),
        ((n : ℝ) * p - k) ^ 2 / (n * η) ^ 2 * ((n.choose k : ℝ) * p ^ k * (1 - p) ^ (n - k)) := by
        refine Finset.sum_le_sum fun k hk => ?_
        rw [Finset.mem_filter] at hk
        have h1 : 1 ≤ ((n : ℝ) * p - k) ^ 2 / (n * η) ^ 2 := by
          rw [le_div_iff₀ hc, one_mul]
          have h2 : (n * η) ^ 2 ≤ |(k : ℝ) - n * p| ^ 2 :=
            pow_le_pow_left₀ (by positivity) hk.2 2
          rw [sq_abs] at h2
          nlinarith [h2]
        nlinarith [hterm k hk.1]
    _ ≤ ∑ k ∈ Finset.range (n + 1),
        ((n : ℝ) * p - k) ^ 2 / (n * η) ^ 2 * ((n.choose k : ℝ) * p ^ k * (1 - p) ^ (n - k)) := by
        refine Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) fun k hk _ => ?_
        have := hterm k hk
        positivity
    _ = (n * p * (1 - p)) / (n * η) ^ 2 := by
        rw [← binom_var n p, Finset.sum_div]
        refine Finset.sum_congr rfl fun k _ => ?_
        ring
    _ ≤ 1 / (n * η ^ 2) := by
        rw [div_le_div_iff₀ hc (by positivity)]
        have : p * (1 - p) ≤ 1 := by nlinarith
        have h3 : n * p * (1 - p) * (n * η ^ 2) = (p * (1 - p)) * (n * η) ^ 2 := by ring
        rw [h3]
        nlinarith [hc]

end ErasureLib

namespace ErasureBlocks
open Matrix WildeQIT WildeQIT.ErasureClassical WildeQIT.Degradable

/-- Unerased positions of an output string. -/
def patY {n d : ℕ} (y : Fin n → Option (Fin d)) : Finset (Fin n) :=
  Finset.univ.filter (fun k => y k ≠ none)

/-- Positions where a Kraus string uses the "no erasure" Kraus operator. -/
def patF {n d : ℕ} (f : Fin n → Option (Fin d)) : Finset (Fin n) :=
  Finset.univ.filter (fun k => f k = none)

variable {d : ℕ} {ε : ℝ} {h0 : 0 ≤ ε} {h1 : ε ≤ 1}

lemma ec_K_none (y : Option (Fin d)) (x : Fin d) :
    (erasureChannel d ε h0 h1).K none y x = if y = some x then ((Real.sqrt (1 - ε) : ℝ) : ℂ) else 0 := rfl

lemma ec_K_some (i : Fin d) (y : Option (Fin d)) (x : Fin d) :
    (erasureChannel d ε h0 h1).K (some i) y x = if y = none ∧ x = i then ((Real.sqrt ε : ℝ) : ℂ) else 0 := rfl

lemma tp_K (n : ℕ) (f : Fin n → Option (Fin d)) (y : Fin n → Option (Fin d)) (x : Fin n → Fin d) :
    (tensorPower (erasureChannel d ε h0 h1) n).K f y x = ∏ k, (erasureChannel d ε h0 h1).K (f k) (y k) (x k) :=
  rfl

lemma tp_K_zero (n : ℕ) (f : Fin n → Option (Fin d)) (y : Fin n → Option (Fin d)) (x : Fin n → Fin d)
    (h : patF f ≠ patY y) : (tensorPower (erasureChannel d ε h0 h1) n).K f y x = 0 := by
  rw [tp_K]
  have : ∃ k, ¬ (f k = none ↔ y k ≠ none) := by
    by_contra hc
    push Not at hc
    apply h
    ext k
    simp only [patF, patY, Finset.mem_filter, Finset.mem_univ, true_and]
    exact hc k
  obtain ⟨k, hk⟩ := this
  apply Finset.prod_eq_zero (Finset.mem_univ k)
  by_cases hfn : f k = none
  · have hy : y k = none := by
      by_contra hy'
      exact hk ⟨fun _ => hy', fun _ => hfn⟩
    rw [hfn, ec_K_none, hy]
    simp
  · obtain ⟨i, hi⟩ := Option.ne_none_iff_exists'.mp hfn
    have hy : y k ≠ none := by
      intro hy'
      exact hk ⟨fun h' => absurd h' hfn, fun h' => absurd hy' h'⟩
    rw [hi, ec_K_some]
    simp [hy]

/-- Allowed Kraus letters at position `k` for erasure pattern `S`. -/
def allowed {n : ℕ} (d : ℕ) (S : Finset (Fin n)) (k : Fin n) : Finset (Option (Fin d)) :=
  if k ∈ S then {none} else Finset.univ.map Function.Embedding.some

lemma filter_patF_eq {n : ℕ} (S : Finset (Fin n)) :
    Finset.univ.filter (fun f : Fin n → Option (Fin d) => patF f = S) = Fintype.piFinset (allowed d S) := by
  ext f
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Fintype.mem_piFinset, allowed]
  constructor
  · rintro rfl k
    by_cases hk : f k = none
    · simp [patF, hk]
    · obtain ⟨i, hi⟩ := Option.ne_none_iff_exists'.mp hk
      simp [patF, hk, hi]
  · intro hf
    ext k
    have := hf k
    by_cases hk : k ∈ S
    · simp only [hk, if_true, Finset.mem_singleton] at this
      simp [patF, this, hk]
    · simp only [hk, if_false, Finset.mem_map, Finset.mem_univ, true_and,
        Function.Embedding.some_apply] at this
      obtain ⟨i, hi⟩ := this
      simp [patF, ← hi, hk]

lemma sum_KhK (n : ℕ) (S : Finset (Fin n)) :
    ∑ f ∈ Finset.univ.filter (fun f : Fin n → Option (Fin d) => patF f = S),
      ((tensorPower (erasureChannel d ε h0 h1) n).K f)ᴴ * (tensorPower (erasureChannel d ε h0 h1) n).K f
      = (∏ k, (if k ∈ S then (((1 - ε : ℝ)) : ℂ) else ((ε : ℝ) : ℂ))) • (1 : Matrix (Fin n → Fin d) (Fin n → Fin d) ℂ) := by
  have hs1 : ((Real.sqrt (1 - ε) : ℝ) : ℂ) * ((Real.sqrt (1 - ε) : ℝ) : ℂ) = ((1 - ε : ℝ) : ℂ) := by
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt (by linarith)]
  have hs2 : ((Real.sqrt ε : ℝ) : ℂ) * ((Real.sqrt ε : ℝ) : ℂ) = ((ε : ℝ) : ℂ) := by
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt h0]
  rw [filter_patF_eq]
  ext x x'
  rw [Matrix.sum_apply]
  have key : ∀ f : Fin n → Option (Fin d),
      (((tensorPower (erasureChannel d ε h0 h1) n).K f)ᴴ * (tensorPower (erasureChannel d ε h0 h1) n).K f) x x'
        = ∏ k, ∑ w, star ((erasureChannel d ε h0 h1).K (f k) w (x k)) *
            (erasureChannel d ε h0 h1).K (f k) w (x' k) := by
    intro f
    rw [Fintype.prod_sum]
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, tp_K, star_prod, ← Finset.prod_mul_distrib]
  have perk : ∀ k, ∑ o ∈ allowed d S k, ∑ w, star ((erasureChannel d ε h0 h1).K o w (x k)) *
      (erasureChannel d ε h0 h1).K o w (x' k)
        = (if k ∈ S then (((1 - ε : ℝ)) : ℂ) else ((ε : ℝ) : ℂ)) * (if x k = x' k then 1 else 0) := by
    intro k
    by_cases hk : k ∈ S
    · simp only [allowed, hk, if_true, Finset.sum_singleton, ec_K_none, Fintype.sum_option]
      by_cases hx : x k = x' k
      · simp [← hx, apply_ite star, hs1]
      · simp [hx, apply_ite star, ite_mul, mul_ite, Finset.sum_ite_eq']
        intro h
        exact absurd h.symm hx
    · simp only [allowed, hk, if_false, Finset.sum_map, Function.Embedding.some_apply, ec_K_some,
        Fintype.sum_option]
      by_cases hx : x k = x' k
      · simp [← hx, apply_ite star, hs2, Finset.sum_ite_eq, Finset.sum_ite_eq']
      · simp [hx, apply_ite star, ite_mul, mul_ite, Finset.sum_ite_eq, Finset.sum_ite_eq']
  have hone : (1 : Matrix (Fin n → Fin d) (Fin n → Fin d) ℂ) x x' = ∏ k, (if x k = x' k then (1 : ℂ) else 0) := by
    by_cases hx : x = x'
    · subst hx; simp
    · obtain ⟨k, hk⟩ := Function.ne_iff.mp hx
      rw [Matrix.one_apply_ne hx]
      exact (Finset.prod_eq_zero (Finset.mem_univ k) (by simp [hk])).symm
  calc ∑ f ∈ Fintype.piFinset (allowed d S),
        (((tensorPower (erasureChannel d ε h0 h1) n).K f)ᴴ * (tensorPower (erasureChannel d ε h0 h1) n).K f) x x'
      = ∑ f ∈ Fintype.piFinset (allowed d S), ∏ k, ∑ w, star ((erasureChannel d ε h0 h1).K (f k) w (x k)) *
            (erasureChannel d ε h0 h1).K (f k) w (x' k) := Finset.sum_congr rfl fun f _ => key f
    _ = ∏ k, ∑ o ∈ allowed d S k, ∑ w, star ((erasureChannel d ε h0 h1).K o w (x k)) *
            (erasureChannel d ε h0 h1).K o w (x' k) :=
        (Finset.prod_univ_sum (κ := fun _ => Option (Fin d)) (allowed d S)
          (fun k o => ∑ w, star ((erasureChannel d ε h0 h1).K o w (x k)) *
            (erasureChannel d ε h0 h1).K o w (x' k))).symm
    _ = ∏ k, ((if k ∈ S then (((1 - ε : ℝ)) : ℂ) else ((ε : ℝ) : ℂ)) * (if x k = x' k then 1 else 0)) :=
        Finset.prod_congr rfl fun k _ => perk k
    _ = _ := by
        rw [Finset.prod_mul_distrib, Matrix.smul_apply, smul_eq_mul, hone]

end ErasureBlocks

namespace ErasureConv
open Matrix WildeQIT WildeQIT.ErasureClassical WildeQIT.Degradable ErasureBlocks
open scoped ComplexOrder

/-- `0 ≤ Tr(A X)` for positive semidefinite `A`, `X`. -/
lemma tr_nonneg' {m : Type} [Fintype m] [DecidableEq m] (A X : Matrix m m ℂ) (hA : A.PosSemidef)
    (hX : X.PosSemidef) : 0 ≤ (A * X).trace.re := by
  have hspec : X = (hX.1.eigenvectorUnitary : Matrix m m ℂ) *
      Matrix.diagonal (RCLike.ofReal ∘ hX.1.eigenvalues) * star (hX.1.eigenvectorUnitary : Matrix m m ℂ) := by
    have h := hX.1.spectral_theorem
    rw [Unitary.conjStarAlgAut_apply] at h
    exact h
  set U : Matrix m m ℂ := (hX.1.eigenvectorUnitary : Matrix m m ℂ) with hU
  set lam := hX.1.eigenvalues with hlam
  set B : Matrix m m ℂ := star U * A * U with hB
  have hBpsd : B.PosSemidef := by
    have := hA.conjTranspose_mul_mul_same U
    simpa [hB, Matrix.star_eq_conjTranspose] using this
  have hAX : (A * X).trace = ∑ i, B i i * (lam i : ℂ) := by
    have e1 : (A * X).trace = (B * Matrix.diagonal (RCLike.ofReal ∘ lam)).trace := by
      rw [hspec]
      calc (A * (U * Matrix.diagonal (RCLike.ofReal ∘ lam) * star U)).trace
          = ((A * U * Matrix.diagonal (RCLike.ofReal ∘ lam)) * star U).trace := by
            simp only [Matrix.mul_assoc]
        _ = (star U * (A * U * Matrix.diagonal (RCLike.ofReal ∘ lam))).trace :=
            Matrix.trace_mul_comm _ _
        _ = (B * Matrix.diagonal (RCLike.ofReal ∘ lam)).trace := by
            simp only [hB, Matrix.mul_assoc]
    rw [e1]
    simp [Matrix.trace, Matrix.mul_apply, Matrix.diagonal_apply]
  have hdiag : ∀ i, 0 ≤ (B i i).re := fun i => (Complex.nonneg_iff.mp (hBpsd.diag_nonneg)).1
  have hlam0 : ∀ i, 0 ≤ lam i := fun i => hX.eigenvalues_nonneg i
  rw [hAX, Complex.re_sum]
  refine Finset.sum_nonneg fun i _ => ?_
  have : (B i i * (lam i : ℂ)).re = (B i i).re * lam i := by simp
  rw [this]
  exact mul_nonneg (hdiag i) (hlam0 i)

lemma QChannel_trace {a b : Type} [Fintype a] [Fintype b] [DecidableEq a] (N : QChannel a b)
    (ρ : Matrix a a ℂ) : (N.apply ρ).trace = ρ.trace := by
  unfold QChannel.apply
  rw [Matrix.trace_sum]
  have e : ∀ i, (N.K i * ρ * (N.K i)ᴴ).trace = ((N.K i)ᴴ * N.K i * ρ).trace := by
    intro i; rw [Matrix.trace_mul_comm, ← Matrix.mul_assoc]
  simp only [e]
  rw [← Matrix.trace_sum, ← Matrix.sum_mul, N.complete, Matrix.one_mul]

/-- Block projector onto the outputs whose unerased set is `S`. -/
noncomputable def P {n : ℕ} (d : ℕ) (S : Finset (Fin n)) :
    Matrix (Fin n → Option (Fin d)) (Fin n → Option (Fin d)) ℂ :=
  Matrix.diagonal fun y => if patY y = S then 1 else 0

/-- Probability of the erasure pattern with unerased set `S`. -/
noncomputable def pS {n : ℕ} (ε : ℝ) (S : Finset (Fin n)) : ℝ :=
  ∏ k, if k ∈ S then 1 - ε else ε

lemma pS_eq {n : ℕ} (ε : ℝ) (S : Finset (Fin n)) : pS ε S = (1 - ε) ^ S.card * ε ^ (n - S.card) := by
  unfold pS
  rw [← Finset.prod_mul_prod_compl S, Finset.prod_ite_of_true (fun k (hk : k ∈ S) => hk),
    Finset.prod_ite_of_false (fun k (hk : k ∈ Sᶜ) => Finset.mem_compl.mp hk), Finset.prod_const,
    Finset.prod_const, Finset.card_compl, Fintype.card_fin]

lemma pS_nonneg {n : ℕ} {ε : ℝ} (h0 : 0 ≤ ε) (h1 : ε ≤ 1) (S : Finset (Fin n)) : 0 ≤ pS ε S :=
  Finset.prod_nonneg fun k _ => by split_ifs <;> linarith

variable {d : ℕ} {ε : ℝ} {h0 : 0 ≤ ε} {h1 : ε ≤ 1}

lemma P_herm {n : ℕ} (S : Finset (Fin n)) : (P d S)ᴴ = P d S := by
  unfold P
  rw [Matrix.diagonal_conjTranspose]
  congr 1
  funext y
  by_cases h : patY y = S <;> simp [h]

lemma P_mul_P {n : ℕ} (S : Finset (Fin n)) : P d S * P d S = P d S := by
  unfold P
  rw [Matrix.diagonal_mul_diagonal]
  congr 1
  funext y
  by_cases h : patY y = S <;> simp [h]

lemma P_mul_K {n : ℕ} (S : Finset (Fin n)) (f : Fin n → Option (Fin d)) (hf : patF f = S) :
    P d S * (tensorPower (erasureChannel d ε h0 h1) n).K f = (tensorPower (erasureChannel d ε h0 h1) n).K f := by
  ext y x
  rw [P, Matrix.diagonal_mul]
  by_cases h : patY y = S
  · simp [h]
  · simp only [h, if_false, zero_mul]
    exact (tp_K_zero n f y x (fun e => h (e.symm.trans hf))).symm

lemma filter_patY_eq {n : ℕ} (S : Finset (Fin n)) :
    Finset.univ.filter (fun y : Fin n → Option (Fin d) => patY y = S) =
      Fintype.piFinset (fun k => if k ∈ S then Finset.univ.map Function.Embedding.some else {none}) := by
  ext y
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Fintype.mem_piFinset]
  constructor
  · rintro rfl k
    by_cases hk : y k = none
    · simp [patY, hk]
    · obtain ⟨i, hi⟩ := Option.ne_none_iff_exists'.mp hk
      simp [patY, hi]
  · intro hy
    ext k
    have := hy k
    by_cases hk : k ∈ S
    · simp only [hk, if_true, Finset.mem_map, Finset.mem_univ, true_and,
        Function.Embedding.some_apply] at this
      obtain ⟨i, hi⟩ := this
      simp [patY, ← hi, hk]
    · simp only [hk, if_false, Finset.mem_singleton] at this
      simp [patY, this, hk]

lemma card_patY {n : ℕ} (S : Finset (Fin n)) :
    (Finset.univ.filter (fun y : Fin n → Option (Fin d) => patY y = S)).card = d ^ S.card := by
  rw [filter_patY_eq, Fintype.card_piFinset]
  have : ∀ k, ((if k ∈ S then Finset.univ.map Function.Embedding.some else {none} :
      Finset (Option (Fin d)))).card = if k ∈ S then d else 1 := by
    intro k; split_ifs <;> simp
  simp only [this]
  rw [← Finset.prod_mul_prod_compl S, Finset.prod_ite_of_true (fun k (hk : k ∈ S) => hk),
    Finset.prod_ite_of_false (fun k (hk : k ∈ Sᶜ) => Finset.mem_compl.mp hk), Finset.prod_const,
    Finset.prod_const, one_pow, mul_one]

lemma P_trace {n : ℕ} (S : Finset (Fin n)) : (P d S).trace = (((d : ℝ) ^ S.card : ℝ) : ℂ) := by
  rw [P, Matrix.trace_diagonal, Finset.sum_boole, card_patY]
  push_cast
  ring

/-- The part of the `n`-fold channel output with unerased set `S`. -/
noncomputable def NS {n : ℕ} (d : ℕ) (ε : ℝ) (h0 : 0 ≤ ε) (h1 : ε ≤ 1) (S : Finset (Fin n))
    (ρ : Matrix (Fin n → Fin d) (Fin n → Fin d) ℂ) : Matrix (Fin n → Option (Fin d)) (Fin n → Option (Fin d)) ℂ :=
  ∑ f ∈ Finset.univ.filter (fun f : Fin n → Option (Fin d) => patF f = S),
    (tensorPower (erasureChannel d ε h0 h1) n).K f * ρ * ((tensorPower (erasureChannel d ε h0 h1) n).K f)ᴴ

lemma apply_eq {n : ℕ} (ρ : Matrix (Fin n → Fin d) (Fin n → Fin d) ℂ) :
    (tensorPower (erasureChannel d ε h0 h1) n).apply ρ = ∑ S, NS d ε h0 h1 S ρ := by
  unfold NS QChannel.apply
  exact (Finset.sum_fiberwise Finset.univ patF _).symm

lemma P_NS {n : ℕ} (S : Finset (Fin n)) (ρ : Matrix (Fin n → Fin d) (Fin n → Fin d) ℂ) :
    P d S * NS d ε h0 h1 S ρ = NS d ε h0 h1 S ρ := by
  unfold NS
  rw [Matrix.mul_sum]
  refine Finset.sum_congr rfl fun f hf => ?_
  rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, P_mul_K S f (Finset.mem_filter.mp hf).2]

lemma NS_P {n : ℕ} (S : Finset (Fin n)) (ρ : Matrix (Fin n → Fin d) (Fin n → Fin d) ℂ) :
    NS d ε h0 h1 S ρ * P d S = NS d ε h0 h1 S ρ := by
  unfold NS
  rw [Matrix.sum_mul]
  refine Finset.sum_congr rfl fun f hf => ?_
  rw [Matrix.mul_assoc, ← P_herm S, ← Matrix.conjTranspose_mul, P_mul_K S f (Finset.mem_filter.mp hf).2]

lemma NS_psd {n : ℕ} (S : Finset (Fin n)) {ρ : Matrix (Fin n → Fin d) (Fin n → Fin d) ℂ}
    (hρ : ρ.PosSemidef) : (NS d ε h0 h1 S ρ).PosSemidef := by
  unfold NS
  exact Matrix.posSemidef_sum _ fun f _ => hρ.mul_mul_conjTranspose_same _

lemma NS_trace {n : ℕ} (S : Finset (Fin n)) (ρ : Matrix (Fin n → Fin d) (Fin n → Fin d) ℂ) :
    (NS d ε h0 h1 S ρ).trace = ((pS ε S : ℝ) : ℂ) * ρ.trace := by
  have h := sum_KhK (d := d) (ε := ε) (h0 := h0) (h1 := h1) n S
  have h2 := congrArg (fun X => (X * ρ).trace) h
  rw [Matrix.sum_mul, Matrix.trace_sum] at h2
  unfold NS
  rw [Matrix.trace_sum]
  refine (Finset.sum_congr rfl fun f _ => ?_).trans (h2.trans ?_)
  · rw [Matrix.trace_mul_comm, ← Matrix.mul_assoc]
  rw [Matrix.smul_mul, Matrix.one_mul, Matrix.trace_smul, smul_eq_mul]
  congr 1
  unfold pS
  rw [Complex.ofReal_prod]
  refine Finset.prod_congr rfl fun k _ => ?_
  split_ifs <;> rfl

/-- One-shot converse for the erasure channel. -/
theorem one_shot (n M : ℕ) (c : ClassicalCode (Fin d) (Option (Fin d)) n M) :
    ∑ m, (1 - errorProb (erasureChannel d ε h0 h1) c m)
      ≤ ∑ S : Finset (Fin n), (1 - ε) ^ S.card * ε ^ (n - S.card) * min (M : ℝ) ((d : ℝ) ^ S.card) := by
  have hsucc : ∀ m, 1 - errorProb (erasureChannel d ε h0 h1) c m
      = ∑ S, ((c.dec m) * NS d ε h0 h1 S (c.enc m)).trace.re := by
    intro m
    unfold errorProb
    rw [Matrix.sub_mul, Matrix.one_mul, Matrix.trace_sub, Complex.sub_re, QChannel_trace,
      (c.enc_density m).2, apply_eq, Matrix.mul_sum, Matrix.trace_sum, Complex.re_sum]
    simp
  simp only [hsucc]
  rw [Finset.sum_comm]
  refine Finset.sum_le_sum fun S _ => ?_
  have hp := pS_nonneg h0 h1 S
  have htrN : ∀ m, (NS d ε h0 h1 S (c.enc m)).trace.re = pS ε S := by
    intro m
    rw [NS_trace, (c.enc_density m).2, mul_one, Complex.ofReal_re]
  have hI : ∀ m, ((c.dec m) * NS d ε h0 h1 S (c.enc m)).trace.re
      ≤ (P d S * c.dec m * P d S).trace.re * pS ε S := by
    intro m
    have hN : NS d ε h0 h1 S (c.enc m) = P d S * NS d ε h0 h1 S (c.enc m) * P d S := by
      rw [P_NS, NS_P]
    have hPLP : (P d S * c.dec m * P d S).PosSemidef := by
      have := (c.dec_psd m).conjTranspose_mul_mul_same (P d S)
      rwa [P_herm] at this
    have e : ((c.dec m) * NS d ε h0 h1 S (c.enc m)).trace
        = (P d S * c.dec m * P d S * NS d ε h0 h1 S (c.enc m)).trace := by
      conv_lhs => rw [hN]
      rw [← Matrix.mul_assoc, Matrix.trace_mul_comm]
      simp only [Matrix.mul_assoc]
    rw [e, ← htrN m]
    exact ErasureLib.tr_mul_le _ _ hPLP (NS_psd S (c.enc_density m).1)
  have hII : ∀ m, ((c.dec m) * NS d ε h0 h1 S (c.enc m)).trace.re ≤ pS ε S := by
    intro m
    have h1m : (1 - c.dec m) = ∑ m' ∈ Finset.univ.erase m, c.dec m' := by
      rw [← c.dec_sum, ← Finset.add_sum_erase _ _ (Finset.mem_univ m), add_sub_cancel_left]
    have hpsd : (1 - c.dec m).PosSemidef := by
      rw [h1m]
      exact Matrix.posSemidef_sum _ fun m' _ => c.dec_psd m'
    have := tr_nonneg' _ _ hpsd (NS_psd (h0 := h0) (h1 := h1) S (c.enc_density m).1)
    rw [Matrix.sub_mul, Matrix.one_mul, Matrix.trace_sub, Complex.sub_re, htrN m] at this
    linarith
  have hsumP : ∑ m, (P d S * c.dec m * P d S).trace.re = (d : ℝ) ^ S.card := by
    have : ∑ m, (P d S * c.dec m * P d S).trace.re = (P d S * (∑ m, c.dec m) * P d S).trace.re := by
      rw [Matrix.mul_sum, Matrix.sum_mul, Matrix.trace_sum, Complex.re_sum]
    rw [this, c.dec_sum, Matrix.mul_one, P_mul_P, P_trace, Complex.ofReal_re]
  calc ∑ m, ((c.dec m) * NS d ε h0 h1 S (c.enc m)).trace.re
      ≤ ∑ m, min ((P d S * c.dec m * P d S).trace.re * pS ε S) (pS ε S) :=
        Finset.sum_le_sum fun m _ => le_min (hI m) (hII m)
    _ ≤ min (∑ m, (P d S * c.dec m * P d S).trace.re * pS ε S) (∑ _m : Fin M, pS ε S) :=
        le_min (Finset.sum_le_sum fun m _ => min_le_left _ _)
          (Finset.sum_le_sum fun m _ => min_le_right _ _)
    _ = (1 - ε) ^ S.card * ε ^ (n - S.card) * min (M : ℝ) ((d : ℝ) ^ S.card) := by
        rw [← Finset.sum_mul, hsumP, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
          nsmul_eq_mul, ← min_mul_of_nonneg _ _ hp, min_comm, pS_eq]
        ring

end ErasureConv

namespace ErasureConv
open WildeQIT WildeQIT.ErasureClassical

lemma sum_card_choose (n : ℕ) (g : ℕ → ℝ) :
    ∑ S : Finset (Fin n), g S.card = ∑ k ∈ Finset.range (n + 1), (n.choose k : ℝ) * g k := by
  have h := Finset.sum_powerset_apply_card (f := g) (x := (Finset.univ : Finset (Fin n)))
  rw [Finset.powerset_univ, Finset.card_univ, Fintype.card_fin] at h
  rw [h]
  simp [nsmul_eq_mul]

lemma sum_pS (n : ℕ) (ε : ℝ) : ∑ S : Finset (Fin n), (1 - ε) ^ S.card * ε ^ (n - S.card) = 1 := by
  have h := Finset.prod_add (fun _ : Fin n => 1 - ε) (fun _ => ε) Finset.univ
  simp only [Finset.prod_const, sub_add_cancel, one_pow, Finset.powerset_univ] at h
  refine Eq.trans ?_ h.symm
  refine Finset.sum_congr rfl fun t _ => ?_
  simp [Finset.card_univ_diff, Finset.card_compl]

/-- Converse part of Wilde Thm 20.4.2: no rate above `(1 - ε) log d` is achievable. -/
theorem conv (d : ℕ) (hd : 0 < d) (ε : ℝ) (h0 : 0 ≤ ε) (h1 : ε ≤ 1) :
    ∀ R : ℝ, IsAchievableRate (erasureChannel d ε h0 h1) R → R ≤ (1 - ε) * Real.logb 2 d := by
  intro R hR
  by_contra hlt
  push Not at hlt
  set L := Real.logb 2 d with hL
  have hL0 : 0 ≤ L := Real.logb_nonneg one_lt_two (by exact_mod_cast hd)
  set g := R - (1 - ε) * L with hg
  have hg0 : 0 < g := by linarith
  set η := g / (3 * (L + 1)) with hη
  have hη0 : 0 < η := by positivity
  have hηL : η * L ≤ g / 3 := by
    rw [hη, div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith
  obtain ⟨N0, hN0⟩ := Filter.eventually_atTop.mp
    (hR (g / 3) (by positivity) (1 / 2) (by norm_num) (by norm_num))
  set n := N0 + ⌈6 / g⌉₊ + ⌈8 / η ^ 2⌉₊ + 1 with hn
  obtain ⟨M, c, hM, hrate, herr⟩ := hN0 n (by omega)
  have hnpos : 0 < n := by omega
  have hnR : (0 : ℝ) < n := by exact_mod_cast hnpos
  have hn6 : 6 ≤ (n : ℝ) * g := by
    have h6 := Nat.le_ceil (6 / g)
    have : (⌈6 / g⌉₊ : ℝ) ≤ n := by exact_mod_cast (by omega : ⌈6 / g⌉₊ ≤ n)
    exact (div_le_iff₀ hg0).mp (by linarith)
  have hn8 : 8 ≤ (n : ℝ) * η ^ 2 := by
    have h8 := Nat.le_ceil (8 / η ^ 2)
    have : (⌈8 / η ^ 2⌉₊ : ℝ) ≤ n := by exact_mod_cast (by omega : ⌈8 / η ^ 2⌉₊ ≤ n)
    exact (div_le_iff₀ (by positivity)).mp (by linarith)
  have hMR : (0 : ℝ) < M := by exact_mod_cast hM
  have hMbig : (2 : ℝ) ^ ((n : ℝ) * (R - g / 3)) ≤ M := by
    have h2 : (n : ℝ) * (R - g / 3) ≤ Real.logb 2 M := by
      have := hrate
      rw [le_div_iff₀ hnR] at this
      linarith
    calc (2 : ℝ) ^ ((n : ℝ) * (R - g / 3)) ≤ 2 ^ (Real.logb 2 M) :=
          Real.rpow_le_rpow_of_exponent_le (by norm_num) h2
      _ = M := Real.rpow_logb (by norm_num) (by norm_num) hMR
  set q : ℝ := (2 : ℝ) ^ (-((n : ℝ) * (g / 3))) with hq
  have hq0 : 0 ≤ q := by positivity
  have hpt : ∀ k : ℕ, min (M : ℝ) ((d : ℝ) ^ k)
      ≤ M * q + M * (if (n : ℝ) * η ≤ |(k : ℝ) - n * (1 - ε)| then 1 else 0) := by
    intro k
    split_ifs with hk
    · have : 0 ≤ (M : ℝ) * q := by positivity
      linarith [min_le_left (M : ℝ) ((d : ℝ) ^ k)]
    · push Not at hk
      have hk' : (k : ℝ) ≤ n * (1 - ε + η) := by
        have := (abs_lt.mp hk).2
        nlinarith
      have hdk : (2 : ℝ) ^ (L * k) = (d : ℝ) ^ k := by
        rw [Real.rpow_mul_natCast (by norm_num), hL,
          Real.rpow_logb (by norm_num) (by norm_num) (by exact_mod_cast hd)]
      have h1' : L * k ≤ L * (n * (1 - ε + η)) := mul_le_mul_of_nonneg_left hk' hL0
      have h2' : (n : ℝ) * (η * L) ≤ n * (g / 3) := mul_le_mul_of_nonneg_left hηL hnR.le
      have h3 : (n : ℝ) * g = n * R - n * ((1 - ε) * L) := by rw [hg]; ring
      calc min (M : ℝ) ((d : ℝ) ^ k) ≤ (d : ℝ) ^ k := min_le_right _ _
        _ = (2 : ℝ) ^ (L * k) := hdk.symm
        _ ≤ (2 : ℝ) ^ ((n : ℝ) * (R - g / 3) + -((n : ℝ) * (g / 3))) := by
            apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
            linarith
        _ = (2 : ℝ) ^ ((n : ℝ) * (R - g / 3)) * q := Real.rpow_add (by norm_num) _ _
        _ ≤ M * q := mul_le_mul_of_nonneg_right hMbig hq0
        _ ≤ _ := by simp
  have htail := ErasureLib.binom_tail n hnpos (1 - ε) (by linarith) (by linarith) η hη0
  rw [sub_sub_cancel, Finset.sum_filter] at htail
  have hw : ∀ k : ℕ, 0 ≤ (1 - ε) ^ k * ε ^ (n - k) :=
    fun k => mul_nonneg (pow_nonneg (by linarith) _) (pow_nonneg h0 _)
  have hind := sum_card_choose n
    (fun k => (1 - ε) ^ k * ε ^ (n - k) * (if (n : ℝ) * η ≤ |(k : ℝ) - n * (1 - ε)| then 1 else 0))
  have hlow : (M : ℝ) * (1 / 2) ≤ ∑ m, (1 - errorProb (erasureChannel d ε h0 h1) c m) := by
    calc (M : ℝ) * (1 / 2) = ∑ _m : Fin M, (1 / 2 : ℝ) := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      _ ≤ _ := Finset.sum_le_sum fun m _ => by linarith [herr m]
  have hupper : ∑ m, (1 - errorProb (erasureChannel d ε h0 h1) c m)
      ≤ M * q + M * (1 / (n * η ^ 2)) := by
    refine (one_shot (h0 := h0) (h1 := h1) n M c).trans ?_
    calc ∑ S : Finset (Fin n), (1 - ε) ^ S.card * ε ^ (n - S.card) * min (M : ℝ) ((d : ℝ) ^ S.card)
        ≤ ∑ S : Finset (Fin n), (1 - ε) ^ S.card * ε ^ (n - S.card) *
            (M * q + M * (if (n : ℝ) * η ≤ |(S.card : ℝ) - n * (1 - ε)| then 1 else 0)) :=
          Finset.sum_le_sum fun S _ => mul_le_mul_of_nonneg_left (hpt S.card) (hw S.card)
      _ = M * q * (∑ S : Finset (Fin n), (1 - ε) ^ S.card * ε ^ (n - S.card)) +
            M * ∑ S : Finset (Fin n), (1 - ε) ^ S.card * ε ^ (n - S.card) *
              (if (n : ℝ) * η ≤ |(S.card : ℝ) - n * (1 - ε)| then 1 else 0) := by
          rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
          exact Finset.sum_congr rfl fun S _ => by ring
      _ ≤ M * q + M * (1 / (n * η ^ 2)) := by
          rw [sum_pS, mul_one, hind]
          gcongr
          refine le_trans (le_of_eq ?_) htail
          refine Finset.sum_congr rfl fun k _ => ?_
          split_ifs <;> ring
  have hq4 : q ≤ 1 / 4 := by
    calc q ≤ (2 : ℝ) ^ (-2 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
      _ = 1 / 4 := by rw [Real.rpow_neg (by norm_num)]; norm_num
  have hi8 : 1 / ((n : ℝ) * η ^ 2) ≤ 1 / 8 := by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    linarith
  have := hlow.trans hupper
  have e1 : (M : ℝ) * q ≤ M * (1 / 4) := mul_le_mul_of_nonneg_left hq4 hMR.le
  have e2 : (M : ℝ) * (1 / (n * η ^ 2)) ≤ M * (1 / 8) := mul_le_mul_of_nonneg_left hi8 hMR.le
  nlinarith

end ErasureConv

namespace WildeQIT.ErasureClassical

/-- Assembly: the capacity is the supremum of achievable rates, so a greatest achievable rate is it. -/
theorem assemble (d : ℕ) (ε : ℝ) (h0 : 0 ≤ ε) (h1 : ε ≤ 1)
    (hconv : ∀ R, IsAchievableRate (erasureChannel d ε h0 h1) R → R ≤ (1 - ε) * Real.logb 2 d)
    (hach : IsAchievableRate (erasureChannel d ε h0 h1) ((1 - ε) * Real.logb 2 d)) :
    classicalCapacity (erasureChannel d ε h0 h1) = (((1 - ε) * Real.logb 2 d : ℝ) : EReal) := by
  unfold classicalCapacity
  apply le_antisymm
  · exact iSup₂_le fun R hR => EReal.coe_le_coe_iff.mpr (hconv R hR)
  · exact le_iSup₂_of_le (f := fun (R : ℝ) (_ : IsAchievableRate (erasureChannel d ε h0 h1) R) =>
      (R : EReal)) _ hach le_rfl

end WildeQIT.ErasureClassical

namespace ErasureAch
open Matrix WildeQIT WildeQIT.ErasureClassical WildeQIT.Degradable ErasureBlocks ErasureConv
open scoped ComplexOrder

/-- Output string when the unerased set is `S` and the input is `u`. -/
def mask {n d : ℕ} (S : Finset (Fin n)) (u : Fin n → Fin d) : Fin n → Option (Fin d) :=
  fun k => if k ∈ S then some (u k) else none

/-- Codeword `u` is consistent with the output `y`. -/
def cons {n d : ℕ} (u : Fin n → Fin d) (y : Fin n → Option (Fin d)) : Prop :=
  ∀ k, y k ≠ none → y k = some (u k)

lemma cons_mask {n d : ℕ} (S : Finset (Fin n)) (u v : Fin n → Fin d) :
    cons u (mask S v) ↔ ∀ k ∈ S, u k = v k := by
  unfold cons mask
  constructor
  · intro h k hk
    have := h k (by simp [hk])
    simp only [hk, if_true, Option.some.injEq] at this
    exact this.symm
  · intro h k hk
    by_cases hkS : k ∈ S
    · simp only [hkS, if_true, Option.some.injEq]
      exact (h k hkS).symm
    · simp [hkS] at hk

open Classical in
/-- Decoder: a message whose codeword is consistent with `y` (message `0` if there is none). -/
noncomputable def dcd {n d M : ℕ} (hM : 0 < M) (x : Fin M → Fin n → Fin d)
    (y : Fin n → Option (Fin d)) : Fin M :=
  if h : ∃ m, cons (x m) y then Classical.choose h else ⟨0, hM⟩

lemma dcd_spec {n d M : ℕ} (hM : 0 < M) (x : Fin M → Fin n → Fin d) (y : Fin n → Option (Fin d))
    (h : ∃ m, cons (x m) y) : cons (x (dcd hM x y)) y := by
  unfold dcd
  rw [dif_pos h]
  exact Classical.choose_spec h

/-- The pure state `|u⟩⟨u|`. -/
noncomputable def ket {n d : ℕ} (u : Fin n → Fin d) : Matrix (Fin n → Fin d) (Fin n → Fin d) ℂ :=
  Matrix.diagonal fun v => if v = u then 1 else 0

/-- The classical code with codebook `x` and the consistency decoder. -/
noncomputable def code {n d M : ℕ} (hM : 0 < M) (x : Fin M → Fin n → Fin d) :
    ClassicalCode (Fin d) (Option (Fin d)) n M where
  enc m := ket (x m)
  enc_density m := by
    unfold IsDensityOperator
    refine ⟨Matrix.posSemidef_diagonal_iff.mpr fun v => ?_, ?_⟩
    · split_ifs <;> simp
    · simp [ket, Matrix.trace_diagonal]
  dec m := Matrix.diagonal fun y => if dcd hM x y = m then 1 else 0
  dec_psd m := Matrix.posSemidef_diagonal_iff.mpr fun y => by split_ifs <;> simp
  dec_sum := by
    ext y y'
    rw [Matrix.sum_apply]
    by_cases hy : y = y'
    · subst hy
      simp [Matrix.diagonal_apply_eq]
    · simp [Matrix.diagonal_apply_ne _ hy, Matrix.one_apply_ne hy]

/-- Confusability of codeword `m` with the others on the large unerased sets `|S| ≥ k0`. -/
noncomputable def psi {n M d : ℕ} (ε : ℝ) (k0 : ℕ) (x : Fin M → Fin n → Fin d) (m : Fin M) : ℝ :=
  ∑ S : Finset (Fin n), (pS ε S * (if k0 ≤ S.card then 1 else 0)) *
    ∑ m' ∈ Finset.univ.erase m, (if ∀ k ∈ S, x m' k = x m k then (1 : ℝ) else 0)

lemma count_agree {n d : ℕ} (S : Finset (Fin n)) (w : Fin n → Fin d) :
    (∑ v : Fin n → Fin d, (if ∀ k ∈ S, v k = w k then (1 : ℝ) else 0)) = (d : ℝ) ^ (n - S.card) := by
  rw [Finset.sum_boole]
  have : Finset.univ.filter (fun v : Fin n → Fin d => ∀ k ∈ S, v k = w k)
      = Fintype.piFinset (fun k => if k ∈ S then {w k} else Finset.univ) := by
    ext v
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Fintype.mem_piFinset]
    constructor
    · intro h k
      by_cases hk : k ∈ S
      · simp [hk, h k hk]
      · simp [hk]
    · intro h k hk
      simpa [hk] using h k
  rw [this, Fintype.card_piFinset]
  have hc : ∀ k, ((if k ∈ S then {w k} else Finset.univ : Finset (Fin d))).card
      = if k ∈ S then 1 else d := by
    intro k; split_ifs <;> simp
  simp only [hc]
  rw [← Finset.prod_mul_prod_compl S, Finset.prod_ite_of_true (fun k (hk : k ∈ S) => hk),
    Finset.prod_ite_of_false (fun k (hk : k ∈ Sᶜ) => Finset.mem_compl.mp hk), Finset.prod_const,
    Finset.prod_const, one_pow, one_mul, Finset.card_compl, Fintype.card_fin]
  push_cast
  ring

lemma sum_pair {α : Type} [Fintype α] {M : ℕ} (m m' : Fin M) (hmm : m ≠ m')
    (h : α → α → ℝ) (c : ℝ) (hc : ∀ w, ∑ v, h v w = c) :
    ∑ x : Fin M → α, h (x m') (x m) = (Fintype.card ({j // j ≠ m'} → α) : ℝ) * c := by
  refine (Fintype.sum_equiv (Equiv.funSplitAt m' α) _ (fun p => h p.1 (p.2 ⟨m, hmm⟩))
    (fun x => rfl)).trans ?_
  rw [Fintype.sum_prod_type, Finset.sum_comm]
  simp only [hc, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]

lemma pair_bound {n M d : ℕ} (hd : 0 < d) (k0 : ℕ) (S : Finset (Fin n)) (hS : k0 ≤ S.card)
    (m m' : Fin M) (hmm : m ≠ m') :
    ∑ x : Fin M → Fin n → Fin d, (if ∀ k ∈ S, x m' k = x m k then (1 : ℝ) else 0)
      ≤ (∑ _x : Fin M → Fin n → Fin d, (1 : ℝ)) * (1 / (d : ℝ) ^ k0) := by
  have hA : ∑ x : Fin M → Fin n → Fin d, (if ∀ k ∈ S, x m' k = x m k then (1 : ℝ) else 0)
      = (Fintype.card ({j // j ≠ m'} → Fin n → Fin d) : ℝ) * (d : ℝ) ^ (n - S.card) :=
    sum_pair m m' hmm (fun v w : Fin n → Fin d => if ∀ k ∈ S, v k = w k then (1 : ℝ) else 0) _
      (count_agree S)
  have h1 : ∑ _x : Fin M → Fin n → Fin d, (1 : ℝ)
      = (Fintype.card ({j // j ≠ m'} → Fin n → Fin d) : ℝ) * (d : ℝ) ^ n :=
    sum_pair m m' hmm (fun _ _ : Fin n → Fin d => (1 : ℝ)) _ (fun w => by simp)
  rw [hA, h1]
  have hdR : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hSn : S.card ≤ n := by simpa using S.card_le_univ
  rw [mul_assoc]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  rw [mul_one_div, le_div_iff₀ (by positivity)]
  calc (d : ℝ) ^ (n - S.card) * (d : ℝ) ^ k0 ≤ (d : ℝ) ^ (n - S.card) * (d : ℝ) ^ S.card :=
        mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hdR hS) (by positivity)
    _ = (d : ℝ) ^ n := by rw [← pow_add, Nat.sub_add_cancel hSn]

lemma avg {n M d : ℕ} (hd : 0 < d) (ε : ℝ) (h0 : 0 ≤ ε) (h1 : ε ≤ 1) (k0 : ℕ) :
    ∑ x : Fin M → Fin n → Fin d, ∑ m, psi ε k0 x m
      ≤ ∑ _x : Fin M → Fin n → Fin d, ((M : ℝ) * M * (1 / (d : ℝ) ^ k0)) := by
  set X := ∑ _x : Fin M → Fin n → Fin d, (1 : ℝ) with hX
  set θ := 1 / (d : ℝ) ^ k0 with hθ
  have hθ0 : 0 ≤ θ := by positivity
  have hX0 : 0 ≤ X := Finset.sum_nonneg fun _ _ => zero_le_one
  have hR : ∑ _x : Fin M → Fin n → Fin d, ((M : ℝ) * M * θ) = X * (M * M * θ) := by
    rw [hX, Finset.sum_mul]
    simp only [one_mul]
  rw [Finset.sum_comm]
  calc ∑ m : Fin M, ∑ x : Fin M → Fin n → Fin d, psi ε k0 x m
      ≤ ∑ m : Fin M, ∑ S : Finset (Fin n), pS ε S * (M * (X * θ)) := by
        refine Finset.sum_le_sum fun m _ => ?_
        unfold psi
        rw [Finset.sum_comm]
        refine Finset.sum_le_sum fun S _ => ?_
        rw [← Finset.mul_sum, Finset.sum_comm]
        by_cases hS : k0 ≤ S.card
        · rw [if_pos hS, mul_one]
          refine mul_le_mul_of_nonneg_left ?_ (pS_nonneg h0 h1 S)
          calc ∑ m' ∈ Finset.univ.erase m, ∑ x : Fin M → Fin n → Fin d,
                (if ∀ k ∈ S, x m' k = x m k then (1 : ℝ) else 0)
              ≤ ∑ m' ∈ Finset.univ.erase m, X * θ :=
                Finset.sum_le_sum fun m' hm' =>
                  pair_bound hd k0 S hS m m' (Finset.ne_of_mem_erase hm').symm
            _ ≤ ∑ _m' : Fin M, X * θ :=
                Finset.sum_le_sum_of_subset_of_nonneg (Finset.erase_subset _ _)
                  fun _ _ _ => by positivity
            _ = M * (X * θ) := by simp
        · rw [if_neg hS, mul_zero, zero_mul]
          exact mul_nonneg (pS_nonneg h0 h1 S) (by positivity)
    _ = ∑ _m : Fin M, ((M : ℝ) * (X * θ)) := Finset.sum_congr rfl fun m _ => by
          rw [← Finset.sum_mul]
          simp only [pS_eq, sum_pS, one_mul]
    _ = _ := by
          rw [hR, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
          ring

lemma psi_nonneg {n M d : ℕ} {ε : ℝ} (h0 : 0 ≤ ε) (h1 : ε ≤ 1) (k0 : ℕ) (x : Fin M → Fin n → Fin d)
    (m : Fin M) : 0 ≤ psi ε k0 x m :=
  Finset.sum_nonneg fun S _ =>
    mul_nonneg (mul_nonneg (pS_nonneg h0 h1 S) (by split_ifs <;> norm_num))
      (Finset.sum_nonneg fun _ _ => by split_ifs <;> norm_num)

lemma psi_sub {n M M2 d : ℕ} {ε : ℝ} (h0 : 0 ≤ ε) (h1 : ε ≤ 1) (k0 : ℕ) (x : Fin M → Fin n → Fin d)
    (e : Fin M2 → Fin M) (he : Function.Injective e) (m : Fin M2) :
    psi ε k0 (x ∘ e) m ≤ psi ε k0 x (e m) := by
  unfold psi
  refine Finset.sum_le_sum fun S _ => ?_
  refine mul_le_mul_of_nonneg_left ?_ (mul_nonneg (pS_nonneg h0 h1 S) (by split_ifs <;> norm_num))
  calc ∑ m' ∈ Finset.univ.erase m, (if ∀ k ∈ S, (x ∘ e) m' k = (x ∘ e) m k then (1 : ℝ) else 0)
      = ∑ a ∈ (Finset.univ.erase m).image e, (if ∀ k ∈ S, x a k = x (e m) k then (1 : ℝ) else 0) :=
        (Finset.sum_image (f := fun a => if ∀ k ∈ S, x a k = x (e m) k then (1 : ℝ) else 0)
          (s := Finset.univ.erase m) (g := e) (by intro a _ b _ h; exact he h)).symm
    _ ≤ _ := by
        refine Finset.sum_le_sum_of_subset_of_nonneg ?_ fun _ _ _ => by split_ifs <;> norm_num
        intro a ha
        obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp ha
        exact Finset.mem_erase.mpr ⟨fun h => (Finset.mem_erase.mp hb).1 (he h), Finset.mem_univ _⟩

lemma expurgate {n M d : ℕ} (hd : 0 < d) (hM : 0 < M) (ε : ℝ) (h0 : 0 ≤ ε) (h1 : ε ≤ 1) (k0 : ℕ) :
    ∃ M2 : ℕ, ∃ x : Fin M2 → Fin n → Fin d, 0 < M2 ∧ (M : ℝ) ≤ 2 * M2 ∧
      ∀ m, psi ε k0 x m ≤ 2 * M * (1 / (d : ℝ) ^ k0) := by
  set θ := 1 / (d : ℝ) ^ k0 with hθ
  have hθ0 : 0 < θ := by positivity
  have : Nonempty (Fin M → Fin n → Fin d) := ⟨fun _ _ => ⟨0, hd⟩⟩
  obtain ⟨x, -, hx⟩ := Finset.exists_le_of_sum_le Finset.univ_nonempty
    (avg (n := n) (M := M) hd ε h0 h1 k0)
  set G := Finset.univ.filter (fun m => psi ε k0 x m ≤ 2 * M * θ) with hG
  set B := Finset.univ.filter (fun m => ¬ psi ε k0 x m ≤ 2 * M * θ) with hB
  have hGB : G.card + B.card = M := by
    rw [hG, hB, Finset.card_filter_add_card_filter_not, Finset.card_univ, Fintype.card_fin]
  have hBle : (B.card : ℝ) * (2 * M * θ) ≤ M * M * θ := by
    calc (B.card : ℝ) * (2 * M * θ) = ∑ _m ∈ B, 2 * M * θ := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ ∑ m ∈ B, psi ε k0 x m :=
          Finset.sum_le_sum fun m hm => le_of_lt (not_le.mp (Finset.mem_filter.mp hm).2)
      _ ≤ ∑ m, psi ε k0 x m :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
            fun m _ _ => psi_nonneg h0 h1 k0 x m
      _ ≤ M * M * θ := hx
  have hMR : (0 : ℝ) < M := by exact_mod_cast hM
  have hB2 : (B.card : ℝ) * 2 ≤ M := by
    have e1 : (B.card : ℝ) * 2 * (M * θ) ≤ M * (M * θ) := by
      have e2 : (B.card : ℝ) * 2 * (M * θ) = B.card * (2 * M * θ) := by ring
      have e3 : (M : ℝ) * (M * θ) = M * M * θ := by ring
      rw [e2, e3]
      exact hBle
    exact le_of_mul_le_mul_right e1 (by positivity)
  have hGR : (G.card : ℝ) + B.card = M := by exact_mod_cast hGB
  have hG2 : (M : ℝ) ≤ 2 * G.card := by linarith
  have hGpos : 0 < G.card := by
    have : (0 : ℝ) < G.card := by linarith
    exact_mod_cast this
  refine ⟨G.card, x ∘ (G.orderEmbOfFin rfl), hGpos, hG2, fun m => ?_⟩
  refine (psi_sub h0 h1 k0 x _ (G.orderEmbOfFin rfl).injective m).trans ?_
  exact (Finset.mem_filter.mp (G.orderEmbOfFin_mem rfl m)).2

variable {d : ℕ} {ε : ℝ} {h0 : 0 ≤ ε} {h1 : ε ≤ 1}

lemma letter (yk : Option (Fin d)) (uk : Fin d) :
    ∑ o : Option (Fin d), (erasureChannel d ε h0 h1).K o yk uk * star ((erasureChannel d ε h0 h1).K o yk uk)
      = ((1 - ε : ℝ) : ℂ) * (if yk = some uk then 1 else 0)
        + ((ε : ℝ) : ℂ) * (if yk = none then 1 else 0) := by
  have hs1 : ((Real.sqrt (1 - ε) : ℝ) : ℂ) * ((Real.sqrt (1 - ε) : ℝ) : ℂ) = ((1 - ε : ℝ) : ℂ) := by
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt (by linarith)]
  have hs2 : ((Real.sqrt ε : ℝ) : ℂ) * ((Real.sqrt ε : ℝ) : ℂ) = ((ε : ℝ) : ℂ) := by
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt h0]
  rw [Fintype.sum_option]
  simp only [ec_K_none, ec_K_some]
  rcases yk with _ | j
  · simp [apply_ite star, ite_mul, mul_ite, hs2, Finset.sum_ite_eq, Finset.sum_ite_eq']
  · by_cases hj : j = uk
    · subst hj
      simp [hs1]
    · simp [hj]

lemma prod_split {n : ℕ} (S : Finset (Fin n)) (u : Fin n → Fin d) (y : Fin n → Option (Fin d)) :
    (∏ k ∈ S, ((1 - ε : ℝ) : ℂ) * (if y k = some (u k) then 1 else 0)) *
      ∏ k ∈ Sᶜ, ((ε : ℝ) : ℂ) * (if y k = none then 1 else 0)
      = ((pS ε S : ℝ) : ℂ) * (if y = mask S u then 1 else 0) := by
  by_cases hy : y = mask S u
  · subst hy
    rw [if_pos rfl, mul_one]
    have e1 : ∀ k ∈ S, ((1 - ε : ℝ) : ℂ) * (if mask S u k = some (u k) then 1 else 0)
        = ((1 - ε : ℝ) : ℂ) := by
      intro k hk; simp [mask, hk]
    have e2 : ∀ k ∈ Sᶜ, ((ε : ℝ) : ℂ) * (if mask S u k = none then 1 else 0) = ((ε : ℝ) : ℂ) := by
      intro k hk; simp [mask, Finset.mem_compl.mp hk]
    rw [Finset.prod_congr rfl e1, Finset.prod_congr rfl e2, pS, Complex.ofReal_prod,
      ← Finset.prod_mul_prod_compl S]
    congr 1
    · exact Finset.prod_congr rfl fun k hk => by simp [hk]
    · exact Finset.prod_congr rfl fun k hk => by simp [Finset.mem_compl.mp hk]
  · rw [if_neg hy, mul_zero]
    obtain ⟨k, hk⟩ := Function.ne_iff.mp hy
    by_cases hkS : k ∈ S
    · have : y k ≠ some (u k) := by simpa [mask, hkS] using hk
      rw [Finset.prod_eq_zero hkS (by simp [this]), zero_mul]
    · have : y k ≠ none := by simpa [mask, hkS] using hk
      rw [Finset.prod_eq_zero (Finset.mem_compl.mpr hkS) (by simp [this]), mul_zero]

lemma out_diag {n : ℕ} (u : Fin n → Fin d) (y : Fin n → Option (Fin d)) :
    ((tensorPower (erasureChannel d ε h0 h1) n).apply (ket u)) y y
      = ∑ S : Finset (Fin n), ((pS ε S : ℝ) : ℂ) * (if y = mask S u then 1 else 0) := by
  have key : ∀ f : Fin n → Option (Fin d),
      ((tensorPower (erasureChannel d ε h0 h1) n).K f * ket u *
        ((tensorPower (erasureChannel d ε h0 h1) n).K f)ᴴ) y y
        = ∏ k, ((erasureChannel d ε h0 h1).K (f k) (y k) (u k) *
            star ((erasureChannel d ε h0 h1).K (f k) (y k) (u k))) := by
    intro f
    rw [Matrix.mul_apply]
    simp only [ket, Matrix.mul_diagonal, Matrix.conjTranspose_apply, mul_ite, ite_mul, mul_one,
      mul_zero, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true, tp_K, star_prod,
      ← Finset.prod_mul_distrib]
  unfold QChannel.apply
  rw [Matrix.sum_apply]
  refine (Finset.sum_congr rfl fun f _ => key f).trans ?_
  refine (Fintype.prod_sum (κ := fun _ => Option (Fin d))
    (fun k (o : Option (Fin d)) => (erasureChannel d ε h0 h1).K o (y k) (u k) *
      star ((erasureChannel d ε h0 h1).K o (y k) (u k)))).symm.trans ?_
  simp only [letter]
  rw [Finset.prod_add, Finset.powerset_univ]
  refine Finset.sum_congr rfl fun S _ => ?_
  rw [← Finset.compl_eq_univ_sdiff]
  exact prod_split S u y

lemma err_eq {n M : ℕ} (hM : 0 < M) (x : Fin M → Fin n → Fin d) (m : Fin M) :
    errorProb (erasureChannel d ε h0 h1) (code hM x) m
      = ∑ S : Finset (Fin n), pS ε S * (if dcd hM x (mask S (x m)) = m then 0 else 1) := by
  have h1D : (1 : Matrix (Fin n → Option (Fin d)) (Fin n → Option (Fin d)) ℂ) - (code hM x).dec m
      = Matrix.diagonal fun y => if dcd hM x y = m then 0 else 1 := by
    ext y y'
    by_cases hy : y = y'
    · subst hy
      by_cases h : dcd hM x y = m <;> simp [code, h]
    · simp [code, Matrix.one_apply_ne hy, Matrix.diagonal_apply_ne _ hy]
  unfold errorProb
  rw [h1D]
  show (Matrix.diagonal _ * (tensorPower (erasureChannel d ε h0 h1) n).apply (ket (x m))).trace.re = _
  rw [Matrix.trace]
  simp only [Matrix.diag_apply, Matrix.diagonal_mul, out_diag, Finset.mul_sum]
  rw [Finset.sum_comm, Complex.re_sum]
  refine Finset.sum_congr rfl fun S _ => ?_
  rw [Finset.sum_eq_single (mask S (x m))]
  · by_cases h : dcd hM x (mask S (x m)) = m <;> simp [h]
  · intro y _ hy
    simp [hy]
  · intro h
    exact absurd (Finset.mem_univ _) h

lemma err_bound {n M : ℕ} (hM : 0 < M) (k0 : ℕ) (x : Fin M → Fin n → Fin d) (m : Fin M) :
    errorProb (erasureChannel d ε h0 h1) (code hM x) m
      ≤ (∑ S : Finset (Fin n), pS ε S * (if S.card < k0 then 1 else 0)) + psi ε k0 x m := by
  rw [err_eq, psi, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun S _ => ?_
  have hp := pS_nonneg h0 h1 S
  have hsum0 : 0 ≤ ∑ m' ∈ Finset.univ.erase m, (if ∀ k ∈ S, x m' k = x m k then (1 : ℝ) else 0) :=
    Finset.sum_nonneg fun _ _ => by split_ifs <;> norm_num
  by_cases hdm : dcd hM x (mask S (x m)) = m
  · rw [if_pos hdm, mul_zero]
    have : 0 ≤ pS ε S * (if S.card < k0 then 1 else 0) := mul_nonneg hp (by split_ifs <;> norm_num)
    have : 0 ≤ pS ε S * (if k0 ≤ S.card then 1 else 0) := mul_nonneg hp (by split_ifs <;> norm_num)
    nlinarith
  · rw [if_neg hdm, mul_one]
    by_cases hk : S.card < k0
    · rw [if_pos hk, if_neg (by omega), mul_one, mul_zero, zero_mul, add_zero]
    · rw [if_neg hk, if_pos (by omega), mul_zero, zero_add, mul_one]
      have hc := dcd_spec hM x (mask S (x m)) ⟨m, (cons_mask S _ _).mpr fun k _ => rfl⟩
      rw [cons_mask] at hc
      have hmem : dcd hM x (mask S (x m)) ∈ Finset.univ.erase m :=
        Finset.mem_erase.mpr ⟨hdm, Finset.mem_univ _⟩
      have h1le : (1 : ℝ) ≤ ∑ m' ∈ Finset.univ.erase m,
          (if ∀ k ∈ S, x m' k = x m k then (1 : ℝ) else 0) := by
        calc (1 : ℝ) = (if ∀ k ∈ S, x (dcd hM x (mask S (x m))) k = x m k then (1 : ℝ) else 0) := by
              rw [if_pos hc]
          _ ≤ _ := Finset.single_le_sum (f := fun m' => (if ∀ k ∈ S, x m' k = x m k then (1 : ℝ) else 0))
              (fun _ _ => by split_ifs <;> norm_num) hmem
      nlinarith

end ErasureAch

namespace ErasureAch
open WildeQIT WildeQIT.ErasureClassical ErasureConv

/-- Direct part of Wilde Thm 20.4.2: the rate `(1 - ε) log d` is achievable. -/
theorem ach (d : ℕ) (hd : 0 < d) (ε : ℝ) (h0 : 0 ≤ ε) (h1 : ε ≤ 1) :
    IsAchievableRate (erasureChannel d ε h0 h1) ((1 - ε) * Real.logb 2 d) := by
  unfold IsAchievableRate
  intro δ hδ ε' hε'0 hε'1
  set L := Real.logb 2 d with hL
  have hL0 : 0 ≤ L := Real.logb_nonneg one_lt_two (by exact_mod_cast hd)
  set R := (1 - ε) * L with hR
  by_cases hRδ : R - δ ≤ 0
  · refine Filter.Eventually.of_forall fun n =>
      ⟨1, code one_pos (fun _ _ => (⟨0, hd⟩ : Fin d)), one_pos, ?_, fun m => ?_⟩
    · simp only [Nat.cast_one, Real.logb_one, zero_div]
      exact hRδ
    · rw [err_eq]
      have hm : ∀ y, dcd (n := n) one_pos (fun _ _ => (⟨0, hd⟩ : Fin d)) y = m :=
        fun y => Subsingleton.elim _ _
      simp only [hm, eq_self_iff_true, if_true, mul_zero, Finset.sum_const_zero]
      exact hε'0.le
  push Not at hRδ
  set η := δ / (4 * (L + 1)) with hη
  have hη0 : 0 < η := by positivity
  have hηL : L * η ≤ δ / 4 := by
    rw [hη, mul_div_assoc', div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith
  refine Filter.eventually_atTop.mpr
    ⟨⌈2 / δ⌉₊ + ⌈2 / (ε' * η ^ 2)⌉₊ + ⌈4 * Real.logb 2 (8 / ε') / δ⌉₊ + 1, fun n hn => ?_⟩
  have hnpos : 0 < n := by omega
  have hnR : (0 : ℝ) < n := by exact_mod_cast hnpos
  have hn1 : 2 ≤ (n : ℝ) * δ := by
    have h6 := Nat.le_ceil (2 / δ)
    have : (⌈2 / δ⌉₊ : ℝ) ≤ n := by exact_mod_cast (by omega : ⌈2 / δ⌉₊ ≤ n)
    exact (div_le_iff₀ hδ).mp (by linarith)
  have hn2 : 2 ≤ (n : ℝ) * (ε' * η ^ 2) := by
    have h6 := Nat.le_ceil (2 / (ε' * η ^ 2))
    have : (⌈2 / (ε' * η ^ 2)⌉₊ : ℝ) ≤ n := by
      exact_mod_cast (by omega : ⌈2 / (ε' * η ^ 2)⌉₊ ≤ n)
    exact (div_le_iff₀ (by positivity)).mp (by linarith)
  have hn3 : 4 * Real.logb 2 (8 / ε') ≤ (n : ℝ) * δ := by
    have h6 := Nat.le_ceil (4 * Real.logb 2 (8 / ε') / δ)
    have : (⌈4 * Real.logb 2 (8 / ε') / δ⌉₊ : ℝ) ≤ n := by
      exact_mod_cast (by omega : ⌈4 * Real.logb 2 (8 / ε') / δ⌉₊ ≤ n)
    exact (div_le_iff₀ hδ).mp (by linarith)
  set P : ℝ := (2 : ℝ) ^ ((n : ℝ) * (R - δ / 2)) with hP
  have hP1 : 1 ≤ P := Real.one_le_rpow (by norm_num) (mul_nonneg hnR.le (by linarith))
  set M := ⌈P⌉₊ with hMdef
  have hMpos : 0 < M := Nat.ceil_pos.mpr (by linarith)
  have hPM : P ≤ M := Nat.le_ceil P
  have hMP : (M : ℝ) ≤ 2 * P := by linarith [Nat.ceil_lt_add_one (show 0 ≤ P by linarith)]
  set k0 := ⌈(n : ℝ) * (1 - ε - η)⌉₊ with hk0def
  have hk0 : (n : ℝ) * (1 - ε - η) ≤ k0 := Nat.le_ceil _
  obtain ⟨M2, x, hM2, hMM2, hpsi⟩ := expurgate (n := n) hd hMpos ε h0 h1 k0
  refine ⟨M2, code hM2 x, hM2, ?_, fun m => ?_⟩
  · rw [le_div_iff₀ hnR]
    have hM2R : P / 2 ≤ (M2 : ℝ) := by linarith
    have hlog : Real.logb 2 (P / 2) = n * (R - δ / 2) - 1 := by
      rw [Real.logb_div (ne_of_gt (by linarith)) (by norm_num), hP,
        Real.logb_rpow (by norm_num) (by norm_num), Real.logb_self_eq_one one_lt_two]
    have := Real.logb_le_logb_of_le one_lt_two (by linarith) hM2R
    nlinarith
  · have hT : (∑ S : Finset (Fin n), pS ε S * (if S.card < k0 then 1 else 0)) ≤ 1 / (n * η ^ 2) := by
      have htail := ErasureLib.binom_tail n hnpos (1 - ε) (by linarith) (by linarith) η hη0
      rw [sub_sub_cancel, Finset.sum_filter] at htail
      have hind := sum_card_choose n
        (fun k => (1 - ε) ^ k * ε ^ (n - k) * (if (n : ℝ) * η ≤ |(k : ℝ) - n * (1 - ε)| then 1 else 0))
      calc (∑ S : Finset (Fin n), pS ε S * (if S.card < k0 then 1 else 0))
          ≤ ∑ S : Finset (Fin n), (1 - ε) ^ S.card * ε ^ (n - S.card) *
              (if (n : ℝ) * η ≤ |(S.card : ℝ) - n * (1 - ε)| then 1 else 0) := by
            refine Finset.sum_le_sum fun S _ => ?_
            rw [pS_eq]
            refine mul_le_mul_of_nonneg_left ?_
              (mul_nonneg (pow_nonneg (by linarith) _) (pow_nonneg h0 _))
            by_cases ha : S.card < k0
            · have hlt := Nat.lt_ceil.mp ha
              rw [if_pos ha, if_pos (le_abs.mpr (Or.inr (by linarith)))]
            · rw [if_neg ha]
              split_ifs <;> norm_num
        _ = _ := hind
        _ ≤ 1 / (n * η ^ 2) := by
            refine le_trans (le_of_eq ?_) htail
            refine Finset.sum_congr rfl fun k _ => ?_
            try dsimp only
            split_ifs <;> ring
    have hdk : (d : ℝ) ^ k0 = (2 : ℝ) ^ (L * k0) := by
      rw [Real.rpow_mul_natCast (by norm_num), hL,
        Real.rpow_logb (by norm_num) (by norm_num) (by exact_mod_cast hd)]
    have hθb : 2 * (M : ℝ) * (1 / (d : ℝ) ^ k0) ≤ 4 * (2 : ℝ) ^ (-((n : ℝ) * δ / 4)) := by
      rw [hdk, one_div, ← Real.rpow_neg (by norm_num)]
      have hexp : (n : ℝ) * (R - δ / 2) + -(L * k0) ≤ -((n : ℝ) * δ / 4) := by
        have e1 : L * (n * (1 - ε - η)) ≤ L * k0 := mul_le_mul_of_nonneg_left hk0 hL0
        have e2 : (n : ℝ) * (L * η) ≤ n * (δ / 4) := mul_le_mul_of_nonneg_left hηL hnR.le
        have e3 : (n : ℝ) * R = n * L - n * ε * L := by rw [hR]; ring
        linarith
      calc 2 * (M : ℝ) * (2 : ℝ) ^ (-(L * k0)) ≤ 2 * (2 * P) * (2 : ℝ) ^ (-(L * k0)) :=
            mul_le_mul_of_nonneg_right (by linarith) (by positivity)
        _ = 4 * (2 : ℝ) ^ ((n : ℝ) * (R - δ / 2) + -(L * k0)) := by
            rw [Real.rpow_add (by norm_num), hP]; ring
        _ ≤ 4 * (2 : ℝ) ^ (-((n : ℝ) * δ / 4)) :=
            mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le (by norm_num) hexp)
              (by norm_num)
    have hsmall : (2 : ℝ) ^ (-((n : ℝ) * δ / 4)) ≤ ε' / 8 := by
      calc (2 : ℝ) ^ (-((n : ℝ) * δ / 4)) ≤ (2 : ℝ) ^ (-(Real.logb 2 (8 / ε'))) :=
            Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
        _ = ε' / 8 := by
            rw [Real.rpow_neg (by norm_num),
              Real.rpow_logb (by norm_num) (by norm_num) (by positivity), inv_div]
    have hi : 1 / ((n : ℝ) * η ^ 2) ≤ ε' / 2 := by
      rw [div_le_div_iff₀ (by positivity) (by norm_num)]
      nlinarith
    calc errorProb (erasureChannel d ε h0 h1) (code hM2 x) m
        ≤ (∑ S : Finset (Fin n), pS ε S * (if S.card < k0 then 1 else 0)) + psi ε k0 x m :=
          err_bound hM2 k0 x m
      _ ≤ 1 / (n * η ^ 2) + 4 * (2 : ℝ) ^ (-((n : ℝ) * δ / 4)) :=
          add_le_add hT ((hpsi m).trans hθb)
      _ ≤ ε' := by linarith

end ErasureAch

open WildeQIT.ErasureClassical in
theorem solution (d : ℕ) (hd : 0 < d) (ε : ℝ) (h0 : 0 ≤ ε) (h1 : ε ≤ 1) :
    classicalCapacity (erasureChannel d ε h0 h1) = (((1 - ε) * Real.logb 2 d : ℝ) : EReal) := by
  exact assemble d ε h0 h1 (ErasureConv.conv d hd ε h0 h1) (ErasureAch.ach d hd ε h0 h1)
