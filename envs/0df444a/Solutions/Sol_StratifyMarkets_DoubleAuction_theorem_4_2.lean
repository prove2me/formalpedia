-- Prove2me | solution 1 for StratifyMarkets.DoubleAuction.theorem_4_2
-- status  : ACCEPTED   (prove)
-- author  : @a142857a
-- created : 2026-11-14T06:37:53.429741+00:00
-- url     : https://prove2.me/submissions/263a5037-40a2-4292-accd-64b035d2ab54

import Mathlib

set_option autoImplicit false

-- Solutions.StratifyMarketsBinomialMedian
section
/-! The common-probability, integer-mean case used in the Jogdeo–Samuels proof.
This file collects accepted public Prove2Me sources, each attributed at its declaration.
The argument follows the waiting-time proof of Alan Siegel. -/

/- Shuze Chen · https://prove2.me/theorems/b3ad9246-4bd8-4d51-a960-33630adc8208 -/

section




/-!
Basic objects for exact matrix completion by nuclear-norm minimization.

This file is intentionally statement-level infrastructure: it contains only the
optimization objective, the fixed-cardinality observation model, and the success
predicate for the convex program.
-/

namespace MatrixCompletion

open scoped Classical BigOperators
open Finset

/-- Real matrices with concrete finite row and column types. -/
abbrev RealMatrix (n1 n2 : Nat) := Matrix (Fin n1) (Fin n2) Real

/-- Nuclear norm `||X||_*`, defined as the sum of the singular values of the
associated Euclidean linear map. -/
noncomputable def nuclearNorm {n1 n2 : Nat} (X : RealMatrix n1 n2) : Real :=
  (Matrix.toEuclideanLin X).singularValues.sum (fun _ x => x)

/-- `X` agrees with `M` on the observed entry set. -/
def AgreesOn {n1 n2 : Nat} (Omega : Finset (Fin n1 × Fin n2))
    (X M : RealMatrix n1 n2) : Prop :=
  ∀ p ∈ Omega, X p.1 p.2 = M p.1 p.2

/-- `M` is the unique feasible minimizer of the nuclear-norm completion program. -/
def IsUniqueMinimizer {n1 n2 : Nat} (Omega : Finset (Fin n1 × Fin n2))
    (M : RealMatrix n1 n2) : Prop :=
  ∀ X : RealMatrix n1 n2,
    AgreesOn Omega X M → X ≠ M → nuclearNorm M < nuclearNorm X

/-- Uniform probability, over all size-`m` observation sets, that the completion
program recovers `M` uniquely. -/
noncomputable def successProb {n1 n2 : Nat} (m : Nat) (M : RealMatrix n1 n2) :
    Real :=
  let sampleSpace := Finset.powersetCard m (Finset.univ : Finset (Fin n1 × Fin n2))
  ((sampleSpace.filter (fun Omega => IsUniqueMinimizer Omega M)).card : Real) /
    sampleSpace.card

end MatrixCompletion


end

/- Shuze Chen · https://prove2.me/theorems/7ff7527a-092f-466a-aeeb-948c0275b507 -/

section




/-!
SVD data and coherence assumptions from Candes-Recht Theorem 1.3.
-/

namespace MatrixCompletion

open scoped Classical BigOperators

/-- Explicit rank-`r` SVD data for a matrix.  We carry the singular vectors as
plain coordinate functions so the theorem statement does not depend on extracting
an SVD from Mathlib. -/
structure SVD {n1 n2 : Nat} (M : RealMatrix n1 n2) (r : Nat) where
  sigma : Fin r → Real
  u : Fin r → (Fin n1 → Real)
  v : Fin r → (Fin n2 → Real)
  sigma_pos : ∀ k, 0 < sigma k
  u_orthonormal : ∀ k l, ∑ i, u k i * u l i = if k = l then 1 else 0
  v_orthonormal : ∀ k l, ∑ j, v k j * v l j = if k = l then 1 else 0
  decomp : M = ∑ k, sigma k • Matrix.vecMulVec (u k) (v k)

/-- Sign matrix `E = sum_k u_k v_k^T` associated to an SVD. -/
noncomputable def signMatrix {n1 n2 r : Nat} {M : RealMatrix n1 n2}
    (S : SVD M r) : RealMatrix n1 n2 :=
  ∑ k, Matrix.vecMulVec (S.u k) (S.v k)

/-- Coherence of the span of an orthonormal family, in the coordinate form used
by Definition 1.2. -/
noncomputable def coherence (N r : Nat) (u : Fin r → (Fin N → Real)) : Real :=
  (N : Real) / r * ⨆ i : Fin N, ∑ k, (u k i) ^ 2

/-- Assumption A0: both column and row spaces have coherence at most `mu0`. -/
def A0 {n1 n2 r : Nat} {M : RealMatrix n1 n2} (S : SVD M r)
    (mu0 : Real) : Prop :=
  coherence n1 r S.u ≤ mu0 ∧ coherence n2 r S.v ≤ mu0

/-- Assumption A1: the sign matrix has uniformly bounded entries. -/
def A1 {n1 n2 r : Nat} {M : RealMatrix n1 n2} (S : SVD M r)
    (mu1 : Real) : Prop :=
  ∀ i j,
    |signMatrix S i j| ≤
      mu1 * Real.sqrt ((r : Real) / ((n1 : Real) * (n2 : Real)))

/-- The crude A1 parameter forced by A0 via Cauchy-Schwarz in the paper. -/
noncomputable def defaultA1Parameter (mu0 : Real) (r : Nat) : Real :=
  mu0 * Real.sqrt (r : Real)

end MatrixCompletion


end

/- Shuze Chen · https://prove2.me/theorems/47499e78-f2da-4639-9bba-cbcd748bb2e4 -/

section




/-!
Bernoulli observation model for matrix completion.

The paper proves the probabilistic estimates first for independent Bernoulli
sampling with inclusion probability `p = m / (n1 * n2)`, then transfers the
failure estimate to the fixed-cardinality uniform model.
-/

namespace MatrixCompletion

open scoped Classical BigOperators

/-- Probability weight of a particular observation set in the independent
Bernoulli model with inclusion probability `p`. -/
noncomputable def bernoulliObservationWeight {n1 n2 : Nat} (p : Real)
    (Omega : Finset (Fin n1 × Fin n2)) : Real :=
  p ^ Omega.card *
    (1 - p) ^ (Fintype.card (Fin n1 × Fin n2) - Omega.card)

/-- Bernoulli-model probability that nuclear-norm minimization uniquely
recovers `M`. -/
noncomputable def bernoulliEventProb {n1 n2 : Nat} (p : Real)
    (Event : Finset (Fin n1 × Fin n2) → Prop) : Real :=
  ∑ Omega : Finset (Fin n1 × Fin n2),
    if Event Omega then bernoulliObservationWeight p Omega else 0

/-- Expectation of a real-valued statistic of the Bernoulli observation set. -/
noncomputable def bernoulliExpectation {n1 n2 : Nat} (p : Real)
    (F : Finset (Fin n1 × Fin n2) → Real) : Real :=
  ∑ Omega : Finset (Fin n1 × Fin n2),
    bernoulliObservationWeight p Omega * F Omega

/-- Expectation over two independent Bernoulli observation sets with the same
inclusion probability. -/
noncomputable def bernoulliPairExpectation {n1 n2 : Nat} (p : Real)
    (F : Finset (Fin n1 × Fin n2) →
      Finset (Fin n1 × Fin n2) → Real) : Real :=
  ∑ Omega : Finset (Fin n1 × Fin n2),
    ∑ Omega' : Finset (Fin n1 × Fin n2),
      bernoulliObservationWeight p Omega *
        bernoulliObservationWeight p Omega' * F Omega Omega'

/-- Bernoulli-model probability that nuclear-norm minimization uniquely
recovers `M`. -/
noncomputable def bernoulliSuccessProb {n1 n2 : Nat} (p : Real)
    (M : RealMatrix n1 n2) : Real :=
  bernoulliEventProb p (fun Omega => IsUniqueMinimizer Omega M)

end MatrixCompletion


end

/- Shuze Chen · https://prove2.me/theorems/7dc69b8d-7b0d-42c1-acf7-501d8460762d -/

section




/-!
Generic fixed-cardinality event probabilities and binomial-cardinality weights.

These are reusable probability interfaces for the Bernoulli-to-uniform transfer
in Section 4.1.  The matrix-completion success probability in
`Def_matrix_completion_basic` is a specialization of `fixedCardinalityEventProb`.
-/

namespace MatrixCompletion

open scoped Classical BigOperators
open Finset

/-- Uniform probability of an event over all observation sets of cardinality
`m`. -/
noncomputable def fixedCardinalityEventProb {n1 n2 : Nat} (m : Nat)
    (Event : Finset (Fin n1 × Fin n2) → Prop) : Real :=
  let sampleSpace := Finset.powersetCard m (Finset.univ : Finset (Fin n1 × Fin n2))
  ((sampleSpace.filter Event).card : Real) / sampleSpace.card

/-- Binomial probability of selecting exactly `k` elements out of `N` under
independent Bernoulli sampling with inclusion probability `p`. -/
noncomputable def binomialCardinalityProb (N k : Nat) (p : Real) : Real :=
  (Nat.choose N k : Real) * p ^ k * (1 - p) ^ (N - k)

/-- Binomial lower tail up to and including `m`. -/
noncomputable def binomialLowerTailProb (N m : Nat) (p : Real) : Real :=
  ∑ k ∈ Finset.range (m + 1), binomialCardinalityProb N k p

end MatrixCompletion


end

/- Grace · https://prove2.me/theorems/e36c52b6-06fb-4904-86f7-1129abeab6c4 · accepted submission e2754e50-35eb-4ef1-8522-f6c1cd75c991 -/

namespace Waiting

section


set_option autoImplicit false

open scoped BigOperators
open Finset


/-- One binomial-tail term, as a function of `p`. -/
noncomputable def wt_binTerm (N k : ℕ) (p : ℝ) : ℝ :=
  (Nat.choose N k : ℝ) * p ^ k * (1 - p) ^ (N - k)

/-- `wt_Aterm k(x) = N·C(N-1,k-1)·x^{k-1}·(1-x)^{N-k}` (Siegel §2.1.1 telescoping term). -/
noncomputable def wt_Aterm (N k : ℕ) (x : ℝ) : ℝ :=
  (N : ℝ) * (Nat.choose (N-1) (k-1) : ℝ) * x ^ (k-1) * (1 - x) ^ (N - k)
noncomputable def wt_Bterm (N k : ℕ) (x : ℝ) : ℝ :=
  (N : ℝ) * (Nat.choose (N-1) k : ℝ) * x ^ k * (1 - x) ^ (N - 1 - k)

theorem wt_term_deriv (N k : ℕ) (hk1 : 1 ≤ k) (hkN : k ≤ N) (x : ℝ) :
    HasDerivAt (fun p : ℝ => (Nat.choose N k : ℝ) * p ^ k * (1 - p) ^ (N - k))
      (wt_Aterm N k x - wt_Bterm N k x) x := by
  have h1 : HasDerivAt (fun p : ℝ => p ^ k) ((k : ℝ) * x ^ (k-1)) x := by
    simpa using hasDerivAt_pow k x
  have h2 : HasDerivAt (fun p : ℝ => (1 - p) ^ (N-k)) (-(((N-k : ℕ) : ℝ) * (1-x)^(N-k-1))) x := by
    have hb : HasDerivAt (fun p : ℝ => (1 - p)) (-1) x := by
      simpa using (hasDerivAt_id x).const_sub 1
    have := (hasDerivAt_pow (N-k) (1 - x)).comp x hb
    exact this.congr_deriv (by ring)
  have hmul : HasDerivAt (fun p : ℝ => p ^ k * (1 - p) ^ (N-k))
      ((k : ℝ) * x ^ (k-1) * (1-x)^(N-k) + x^k * (-(((N-k:ℕ):ℝ) * (1-x)^(N-k-1)))) x := h1.mul h2
  have hp := hmul.const_mul (Nat.choose N k : ℝ)
  have hfun : (fun p : ℝ => (Nat.choose N k : ℝ) * (p ^ k * (1 - p) ^ (N - k)))
      = (fun p : ℝ => (Nat.choose N k : ℝ) * p ^ k * (1 - p) ^ (N - k)) := by
    funext p; ring
  rw [hfun] at hp
  refine hp.congr_deriv ?_
  have e1 : (N : ℝ) * (Nat.choose (N-1) (k-1) : ℝ) = (Nat.choose N k : ℝ) * (k : ℝ) := by
    have := Nat.add_one_mul_choose_eq (N-1) (k-1)
    have hk : (k-1)+1 = k := by omega
    have hN' : (N-1)+1 = N := by omega
    rw [hk, hN'] at this
    have := congrArg (Nat.cast : ℕ → ℝ) this
    push_cast at this
    linarith [this]
  have e2 : (N : ℝ) * (Nat.choose (N-1) k : ℝ) = (Nat.choose N k : ℝ) * ((N - k : ℕ) : ℝ) := by
    have := Nat.choose_mul_succ_eq (N-1) k
    have hN' : (N-1)+1 = N := by omega
    rw [hN'] at this
    have := congrArg (Nat.cast : ℕ → ℝ) this
    push_cast at this
    linarith [this]
  have he : N - 1 - k = N - k - 1 := by omega
  simp only [wt_Aterm, wt_Bterm, he]
  rw [e1, e2]
  ring

theorem wt_Bterm_eq_Aterm_succ (N k : ℕ) (x : ℝ) : wt_Bterm N k x = wt_Aterm N (k+1) x := by
  unfold wt_Aterm wt_Bterm
  have h1 : k + 1 - 1 = k := by omega
  rw [h1]; congr 2; omega

theorem wt_Aterm_top_zero (N : ℕ) (hN : 1 ≤ N) (x : ℝ) : wt_Aterm N (N+1) x = 0 := by
  unfold wt_Aterm
  have hz : Nat.choose (N-1) (N+1-1) = 0 := by
    apply Nat.choose_eq_zero_of_lt; omega
  rw [hz]; simp

/-- Derivative of the binomial UPPER tail in `p`: telescopes to a single term. -/
theorem wt_tail_deriv (N m : ℕ) (h : m < N) (x : ℝ) :
    HasDerivAt (fun p : ℝ => ∑ k ∈ Finset.Ico (m+1) (N+1),
        (Nat.choose N k : ℝ) * p ^ k * (1 - p) ^ (N - k))
      ((N : ℝ) * (Nat.choose (N-1) m : ℝ) * x ^ m * (1 - x) ^ (N - 1 - m)) x := by
  have hsum : HasDerivAt (fun p : ℝ => ∑ k ∈ Finset.Ico (m+1) (N+1),
        (Nat.choose N k : ℝ) * p ^ k * (1 - p) ^ (N - k))
      (∑ k ∈ Finset.Ico (m+1) (N+1), (wt_Aterm N k x - wt_Bterm N k x)) x := by
    have hh := HasDerivAt.sum (u := Finset.Ico (m+1) (N+1))
      (A := fun k => fun p : ℝ => (Nat.choose N k : ℝ) * p ^ k * (1 - p) ^ (N - k))
      (A' := fun k => wt_Aterm N k x - wt_Bterm N k x) (x := x)
      (fun k hk => by rw [Finset.mem_Ico] at hk; exact wt_term_deriv N k (by omega) (by omega) x)
    have hfe : (fun p : ℝ => ∑ k ∈ Finset.Ico (m+1) (N+1),
        (Nat.choose N k : ℝ) * p ^ k * (1 - p) ^ (N - k))
        = (∑ k ∈ Finset.Ico (m+1) (N+1), fun p : ℝ =>
            (Nat.choose N k : ℝ) * p ^ k * (1 - p) ^ (N - k)) := by
      funext p; simp only [Finset.sum_apply]
    rw [hfe]; exact hh
  have htel : (∑ k ∈ Finset.Ico (m+1) (N+1), (wt_Aterm N k x - wt_Bterm N k x))
      = (N : ℝ) * (Nat.choose (N-1) m : ℝ) * x ^ m * (1 - x) ^ (N - 1 - m) := by
    have hstep : (∑ k ∈ Finset.Ico (m+1) (N+1), (wt_Aterm N k x - wt_Bterm N k x))
        = ∑ k ∈ Finset.Ico (m+1) (N+1), (wt_Aterm N k x - wt_Aterm N (k+1) x) := by
      apply Finset.sum_congr rfl; intro k _; rw [wt_Bterm_eq_Aterm_succ]
    rw [hstep, Finset.sum_Ico_eq_sum_range]
    have hlen : N + 1 - (m + 1) = N - m := by omega
    rw [hlen]
    have hcongr : (∑ i ∈ Finset.range (N-m), (wt_Aterm N (m+1+i) x - wt_Aterm N (m+1+i+1) x))
        = ∑ i ∈ Finset.range (N-m), ((fun j => wt_Aterm N (m+1+j) x) i - (fun j => wt_Aterm N (m+1+j) x) (i+1)) := by
      apply Finset.sum_congr rfl; intro i _; rfl
    rw [hcongr, Finset.sum_range_sub' (fun j => wt_Aterm N (m+1+j) x) (N-m)]
    have hb : m + 1 + (N - m) = N + 1 := by omega
    rw [hb, wt_Aterm_top_zero N (by omega)]
    simp only [sub_zero]
    unfold wt_Aterm
    rw [show m+1-1 = m from by omega, show N - (m+1) = N - 1 - m from by omega]
  rw [← htel]; exact hsum

theorem waiting_time_density (N m : ℕ) (lam : ℝ) (h : m < N) (t : ℝ) :
    HasDerivAt
      (fun s : ℝ => ∑ k ∈ Finset.Ico (m+1) (N+1),
        (Nat.choose N k : ℝ) * (1 - Real.exp (-(lam * s))) ^ k
          * (Real.exp (-(lam * s))) ^ (N - k))
      ((N : ℝ) * (Nat.choose (N-1) m : ℝ) * (1 - Real.exp (-(lam * t))) ^ m
          * (Real.exp (-(lam * t))) ^ (N - m) * lam) t := by
  -- inner substitution q(s) = 1 - exp(-(lam*s)),  q'(t) = lam * exp(-(lam*t))
  have hexp : HasDerivAt (fun s : ℝ => Real.exp (-(lam * s)))
      (Real.exp (-(lam * t)) * (-lam)) t := by
    have hinner : HasDerivAt (fun s : ℝ => -(lam * s)) (-lam) t := by
      have : HasDerivAt (fun s : ℝ => lam * s) lam t := by
        simpa using (hasDerivAt_id t).const_mul lam
      exact this.fun_neg
    exact (Real.hasDerivAt_exp (-(lam * t))).comp t hinner
  have hq : HasDerivAt (fun s : ℝ => 1 - Real.exp (-(lam * s)))
      (lam * Real.exp (-(lam * t))) t := by
    have := hexp.const_sub 1
    exact this.congr_deriv (by ring)
  -- outer: the binomial upper tail at q
  set q := 1 - Real.exp (-(lam * t)) with hqdef
  have houter := wt_tail_deriv N m h q
  -- chain rule: derivative of  (TailSum ∘ q)  is  TailDeriv(q) * q'(t)
  have hcomp := houter.comp t hq
  -- hcomp : HasDerivAt (TailSum ∘ q(·)) (TailDeriv(q) * (lam * exp(-lam t))) t
  -- rewrite the inner-composition function and the value
  have hfun : (fun s : ℝ => ∑ k ∈ Finset.Ico (m+1) (N+1),
        (Nat.choose N k : ℝ) * (1 - Real.exp (-(lam * s))) ^ k
          * (Real.exp (-(lam * s))) ^ (N - k))
      = (fun p : ℝ => ∑ k ∈ Finset.Ico (m+1) (N+1),
          (Nat.choose N k : ℝ) * p ^ k * (1 - p) ^ (N - k)) ∘ (fun s : ℝ => 1 - Real.exp (-(lam * s))) := by
    funext s
    simp only [Function.comp_apply]
    apply Finset.sum_congr rfl
    intro k _
    have : (1 - (1 - Real.exp (-(lam * s)))) = Real.exp (-(lam * s)) := by ring
    rw [this]
  rw [hfun]
  refine hcomp.congr_deriv ?_
  -- value:  N·C(N-1,m)·q^m·(exp)^{N-m}·lam  =  (N·C(N-1,m)·q^m·(1-q)^{N-1-m}) · (lam·exp)
  have h1q : (1 - q) = Real.exp (-(lam * t)) := by rw [hqdef]; ring
  rw [h1q]
  have hNm : N - m = (N - 1 - m) + 1 := by omega
  rw [hNm, pow_succ]
  ring


end

end Waiting

/- Grace · https://prove2.me/theorems/96f89f14-9fd8-4d0a-833f-e47da60c8a6b · accepted submission 2fccfaa3-793e-4c0e-93ab-d0217ccfae73 -/

section


set_option autoImplicit false
open scoped BigOperators
open Finset

theorem waiting_time_cdf_at_zero (N mp : ℕ) (lam : ℝ) (h : mp < N) :
    (∑ k ∈ Finset.Ico (mp+1) (N+1),
      (Nat.choose N k : ℝ) * (1 - Real.exp (-(lam * (0:ℝ)))) ^ k
        * (Real.exp (-(lam * (0:ℝ)))) ^ (N - k)) = 0 := by
  apply Finset.sum_eq_zero
  intro k hk
  rw [Finset.mem_Ico] at hk
  have h0 : Real.exp (-(lam * (0:ℝ))) = 1 := by
    rw [mul_zero, neg_zero, Real.exp_zero]
  rw [h0]
  rw [show (1:ℝ) - 1 = 0 by ring]
  rw [zero_pow (by omega : k ≠ 0)]
  ring


end

/- Grace · https://prove2.me/theorems/c28346f7-000a-4d7c-a455-7246ce947a9f · accepted submission b7f20f05-65d1-4236-b164-a4583ef87827 -/

section


set_option autoImplicit false
open scoped BigOperators
open Finset MeasureTheory Set Filter Topology

private noncomputable def Fc (N m : ℕ) (lam : ℝ) (s : ℝ) : ℝ :=
  ∑ k ∈ Finset.Ico (m+1) (N+1),
    (Nat.choose N k : ℝ) * (1 - Real.exp (-(lam * s))) ^ k
      * (Real.exp (-(lam * s))) ^ (N - k)
private noncomputable def fd (N m : ℕ) (lam : ℝ) (s : ℝ) : ℝ :=
  (N : ℝ) * (Nat.choose (N-1) m : ℝ) * (1 - Real.exp (-(lam * s))) ^ m
      * (Real.exp (-(lam * s))) ^ (N - m) * lam

private theorem Fc_zero (N m : ℕ) (lam : ℝ) (h : m < N) : Fc N m lam 0 = 0 := by
  unfold Fc
  simp only [mul_zero, neg_zero, Real.exp_zero, sub_self]
  apply Finset.sum_eq_zero
  intro k hk
  rw [Finset.mem_Ico] at hk
  have : (0:ℝ) ^ k = 0 := by apply zero_pow; omega
  rw [this]; ring

private theorem Fc_tendsto (N m : ℕ) (lam : ℝ) (h : m < N) (hlam : 0 < lam) :
    Tendsto (Fc N m lam) atTop (𝓝 1) := by
  have hexp : Tendsto (fun s : ℝ => Real.exp (-(lam * s))) atTop (𝓝 0) := by
    have : Tendsto (fun s : ℝ => -(lam * s)) atTop atBot := by
      have h1 : Tendsto (fun s : ℝ => lam * s) atTop atTop :=
        Filter.Tendsto.const_mul_atTop hlam tendsto_id
      exact tendsto_neg_atTop_atBot.comp h1
    exact Real.tendsto_exp_atBot.comp this
  have hq : Tendsto (fun s : ℝ => 1 - Real.exp (-(lam * s))) atTop (𝓝 1) := by
    simpa using (tendsto_const_nhds (x := (1:ℝ))).sub hexp
  have hterm : ∀ k ∈ Finset.Ico (m+1) (N+1),
      Tendsto (fun s : ℝ => (Nat.choose N k : ℝ) * (1 - Real.exp (-(lam * s))) ^ k
        * (Real.exp (-(lam * s))) ^ (N - k)) atTop (𝓝 (if k = N then 1 else 0)) := by
    intro k hk
    rw [Finset.mem_Ico] at hk
    by_cases hkN : k = N
    · subst hkN
      simp only [Nat.sub_self, pow_zero, mul_one, Nat.choose_self, Nat.cast_one, one_mul]
      have := hq.pow k
      simpa using this
    · rw [if_neg hkN]
      have h0 : Tendsto (fun s : ℝ => (Real.exp (-(lam * s))) ^ (N - k)) atTop (𝓝 0) := by
        have := hexp.pow (N-k)
        simpa [zero_pow (Nat.sub_ne_zero_of_lt (by omega : k < N))] using this
      have hqk : Tendsto (fun s : ℝ => (1 - Real.exp (-(lam * s))) ^ k) atTop (𝓝 1) := by
        simpa using hq.pow k
      have : Tendsto (fun s : ℝ => (Nat.choose N k : ℝ) * (1 - Real.exp (-(lam * s))) ^ k
          * (Real.exp (-(lam * s))) ^ (N - k)) atTop (𝓝 ((Nat.choose N k : ℝ) * 1 * 0)) :=
        ((tendsto_const_nhds.mul hqk).mul h0)
      simpa using this
  have hsum := tendsto_finset_sum (Finset.Ico (m+1) (N+1)) hterm
  unfold Fc
  have hval : (∑ k ∈ Finset.Ico (m+1) (N+1), (if k = N then (1:ℝ) else 0)) = 1 := by
    rw [Finset.sum_ite_eq' (Finset.Ico (m+1) (N+1)) N (fun _ => (1:ℝ))]
    rw [if_pos]; rw [Finset.mem_Ico]; omega
  rw [hval] at hsum
  exact hsum

private theorem fd_integrable (N m : ℕ) (lam : ℝ) (h : m < N) (hlam : 0 < lam) :
    IntegrableOn (fd N m lam) (Ioi (0:ℝ)) := by
  set C : ℝ := |(N : ℝ) * (Nat.choose (N-1) m : ℝ) * lam| with hC
  have hgint : IntegrableOn (fun s : ℝ => C * Real.exp (-lam * s)) (Ioi (0:ℝ)) := by
    have := integrableOn_exp_mul_Ioi (a := -lam) (c := (0:ℝ)) (by linarith)
    exact this.const_mul C
  have hcont : Continuous (fd N m lam) := by unfold fd; fun_prop
  refine Integrable.mono' hgint hcont.aestronglyMeasurable.restrict ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
  rw [Set.mem_Ioi] at hs
  have he : (0:ℝ) < Real.exp (-(lam * s)) := Real.exp_pos _
  have he1 : Real.exp (-(lam * s)) ≤ 1 := by rw [Real.exp_le_one_iff]; nlinarith [hs, hlam]
  have hq0 : (0:ℝ) ≤ 1 - Real.exp (-(lam * s)) := by linarith
  have hq1 : 1 - Real.exp (-(lam * s)) ≤ 1 := by linarith [he.le]
  have hpm : (1 - Real.exp (-(lam * s))) ^ m ≤ 1 := pow_le_one₀ hq0 hq1
  have hNm : 1 ≤ N - m := by omega
  have hpe : (Real.exp (-(lam * s))) ^ (N - m) ≤ Real.exp (-(lam * s)) := by
    calc (Real.exp (-(lam * s))) ^ (N - m)
        ≤ (Real.exp (-(lam * s))) ^ 1 := pow_le_pow_of_le_one he.le he1 hNm
      _ = Real.exp (-(lam * s)) := by rw [pow_one]
  have hpe0 : (0:ℝ) ≤ (Real.exp (-(lam * s))) ^ (N - m) := pow_nonneg he.le _
  unfold fd
  rw [Real.norm_eq_abs]
  have hrw : |(N : ℝ) * (Nat.choose (N-1) m : ℝ) * (1 - Real.exp (-(lam * s))) ^ m
      * (Real.exp (-(lam * s))) ^ (N - m) * lam|
      = C * ((1 - Real.exp (-(lam * s))) ^ m * (Real.exp (-(lam * s))) ^ (N - m)) := by
    rw [hC]
    rw [show (N : ℝ) * (Nat.choose (N-1) m : ℝ) * (1 - Real.exp (-(lam * s))) ^ m
      * (Real.exp (-(lam * s))) ^ (N - m) * lam
      = ((N : ℝ) * (Nat.choose (N-1) m : ℝ) * lam)
        * ((1 - Real.exp (-(lam * s))) ^ m * (Real.exp (-(lam * s))) ^ (N - m)) by ring]
    rw [abs_mul, abs_of_nonneg (a := (1 - Real.exp (-(lam * s))) ^ m * (Real.exp (-(lam * s))) ^ (N - m)) (by positivity)]
  rw [hrw]
  rw [show C * Real.exp (-lam * s) = C * Real.exp (-(lam * s)) by ring]
  apply mul_le_mul_of_nonneg_left _ (by rw [hC]; exact abs_nonneg _)
  calc (1 - Real.exp (-(lam * s))) ^ m * (Real.exp (-(lam * s))) ^ (N - m)
      ≤ 1 * Real.exp (-(lam * s)) := mul_le_mul hpm hpe hpe0 (by norm_num)
    _ = Real.exp (-(lam * s)) := by ring

theorem waiting_time_mass_eq_one (N m : ℕ) (lam : ℝ) (h : m < N) (hlam : 0 < lam) :
    ∫ s in Set.Ioi (0:ℝ),
      ((N : ℝ) * (Nat.choose (N-1) m : ℝ) * (1 - Real.exp (-(lam * s))) ^ m
        * (Real.exp (-(lam * s))) ^ (N - m) * lam) = 1 := by
  have hdens : ∀ x ∈ Ioi (0:ℝ), HasDerivAt (Fc N m lam) (fd N m lam x) x := by
    intro x _
    have := Waiting.waiting_time_density N m lam h x
    exact this
  have key := MeasureTheory.integral_Ioi_of_hasDerivAt_of_tendsto
    (a := (0:ℝ)) (f := Fc N m lam) (f' := fd N m lam) (m := (1:ℝ))
    ((Waiting.waiting_time_density N m lam h 0).continuousAt.continuousWithinAt)
    hdens (fd_integrable N m lam h hlam) (Fc_tendsto N m lam h hlam)
  have hgoal : (∫ s in Set.Ioi (0:ℝ),
      ((N : ℝ) * (Nat.choose (N-1) m : ℝ) * (1 - Real.exp (-(lam * s))) ^ m
        * (Real.exp (-(lam * s))) ^ (N - m) * lam))
      = ∫ s in Ioi (0:ℝ), fd N m lam s := by rfl
  rw [hgoal, key, Fc_zero N m lam h]; ring


end

/- Grace · https://prove2.me/theorems/501bde87-18ee-4c70-8a98-3cca25fa74cf · accepted submission c742f263-1417-48b6-9382-ebdac2e0ea5d -/

section


set_option autoImplicit false
open MeasureTheory Set

theorem waiting_time_density_integrable (N mp : ℕ) (lam : ℝ) (h : mp < N) (hlam : 0 < lam) :
    MeasureTheory.IntegrableOn
      (fun s => (N : ℝ) * (Nat.choose (N-1) mp : ℝ) * (1 - Real.exp (-(lam * s))) ^ mp
        * (Real.exp (-(lam * s))) ^ (N - mp) * lam) (Set.Ioi (0:ℝ)) := by
  set D : ℝ := |(N : ℝ) * (Nat.choose (N-1) mp : ℝ) * lam| with hD
  have hgint : IntegrableOn (fun t : ℝ => D * Real.exp (-lam * t)) (Ioi (0:ℝ)) := by
    have := integrableOn_exp_mul_Ioi (a := -lam) (c := (0:ℝ)) (by linarith)
    exact this.const_mul D
  have hcont : Continuous (fun s => (N : ℝ) * (Nat.choose (N-1) mp : ℝ) * (1 - Real.exp (-(lam * s))) ^ mp
        * (Real.exp (-(lam * s))) ^ (N - mp) * lam) := by fun_prop
  refine Integrable.mono' hgint hcont.aestronglyMeasurable.restrict ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  rw [Set.mem_Ioi] at ht
  have he : (0:ℝ) < Real.exp (-(lam * t)) := Real.exp_pos _
  have he1 : Real.exp (-(lam * t)) ≤ 1 := by rw [Real.exp_le_one_iff]; nlinarith [ht, hlam]
  have hq0 : (0:ℝ) ≤ 1 - Real.exp (-(lam * t)) := by linarith
  have hq1 : 1 - Real.exp (-(lam * t)) ≤ 1 := by linarith [he.le]
  have hpm : (1 - Real.exp (-(lam * t))) ^ mp ≤ 1 := pow_le_one₀ hq0 hq1
  have hpm0 : (0:ℝ) ≤ (1 - Real.exp (-(lam * t))) ^ mp := pow_nonneg hq0 _
  have hNmp : 1 ≤ N - mp := by omega
  have hpe : (Real.exp (-(lam * t))) ^ (N - mp) ≤ Real.exp (-(lam * t)) := by
    calc (Real.exp (-(lam * t))) ^ (N - mp)
        ≤ (Real.exp (-(lam * t))) ^ 1 := pow_le_pow_of_le_one he.le he1 hNmp
      _ = Real.exp (-(lam * t)) := by rw [pow_one]
  have hpe0 : (0:ℝ) ≤ (Real.exp (-(lam * t))) ^ (N - mp) := pow_nonneg he.le _
  rw [Real.norm_eq_abs]
  have habs : |(N : ℝ) * (Nat.choose (N-1) mp : ℝ) * (1 - Real.exp (-(lam * t))) ^ mp
        * (Real.exp (-(lam * t))) ^ (N - mp) * lam|
      = D * ((1 - Real.exp (-(lam * t))) ^ mp * (Real.exp (-(lam * t))) ^ (N - mp)) := by
    rw [hD]
    rw [show (N : ℝ) * (Nat.choose (N-1) mp : ℝ) * (1 - Real.exp (-(lam * t))) ^ mp
        * (Real.exp (-(lam * t))) ^ (N - mp) * lam
        = ((N : ℝ) * (Nat.choose (N-1) mp : ℝ) * lam)
            * ((1 - Real.exp (-(lam * t))) ^ mp * (Real.exp (-(lam * t))) ^ (N - mp)) by ring]
    rw [abs_mul, abs_of_nonneg (a := (1 - Real.exp (-(lam * t))) ^ mp * (Real.exp (-(lam * t))) ^ (N - mp)) (by positivity)]
  rw [habs]
  have hDnn : (0:ℝ) ≤ D := by rw [hD]; exact abs_nonneg _
  rw [show D * Real.exp (-lam * t) = D * Real.exp (-(lam * t)) by ring]
  apply mul_le_mul_of_nonneg_left _ hDnn
  calc (1 - Real.exp (-(lam * t))) ^ mp * (Real.exp (-(lam * t))) ^ (N - mp)
      ≤ 1 * Real.exp (-(lam * t)) := mul_le_mul hpm hpe hpe0 (by norm_num)
    _ = Real.exp (-(lam * t)) := by ring


end

/- Grace · https://prove2.me/theorems/a6876f43-973f-4dfe-9bd3-99fc9751f285 · accepted submission 19c616cf-30dd-4e74-ab18-f086ac49cdfd -/

section


set_option autoImplicit false
open MeasureTheory Set
open scoped BigOperators

theorem waiting_time_t_density_integrable (N mp : ℕ) (lam : ℝ) (h : mp < N) (hlam : 0 < lam) :
    MeasureTheory.IntegrableOn (fun t =>
      t * ((N : ℝ) * (Nat.choose (N-1) mp : ℝ) * (1 - Real.exp (-(lam * t))) ^ mp
        * (Real.exp (-(lam * t))) ^ (N - mp) * lam)) (Set.Ioi (0:ℝ)) := by
  -- dominating constant
  set D : ℝ := |(N : ℝ) * (Nat.choose (N-1) mp : ℝ) * lam| with hD
  -- dominating function:  (D * 2 / lam) * exp (-(lam/2) * t)
  set C : ℝ := D * 2 / lam with hC
  have hgint : IntegrableOn (fun t : ℝ => C * Real.exp (-(lam/2) * t)) (Ioi (0:ℝ)) := by
    have := integrableOn_exp_mul_Ioi (a := -(lam/2)) (c := (0:ℝ)) (by linarith)
    exact this.const_mul C
  have hcont : Continuous (fun t : ℝ => t * ((N : ℝ) * (Nat.choose (N-1) mp : ℝ)
      * (1 - Real.exp (-(lam * t))) ^ mp * (Real.exp (-(lam * t))) ^ (N - mp) * lam)) := by
    fun_prop
  refine Integrable.mono' hgint hcont.aestronglyMeasurable.restrict ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  rw [Set.mem_Ioi] at ht
  have he : (0:ℝ) < Real.exp (-(lam * t)) := Real.exp_pos _
  have he1 : Real.exp (-(lam * t)) ≤ 1 := by
    rw [Real.exp_le_one_iff]; nlinarith [ht, hlam]
  have hq0 : (0:ℝ) ≤ 1 - Real.exp (-(lam * t)) := by linarith
  have hq1 : 1 - Real.exp (-(lam * t)) ≤ 1 := by linarith [he.le]
  have hpm : (1 - Real.exp (-(lam * t))) ^ mp ≤ 1 := pow_le_one₀ hq0 hq1
  have hpm0 : (0:ℝ) ≤ (1 - Real.exp (-(lam * t))) ^ mp := pow_nonneg hq0 _
  have hNmp : 1 ≤ N - mp := by omega
  -- (e^{-λt})^{N-mp} ≤ e^{-λt}
  have hpe : (Real.exp (-(lam * t))) ^ (N - mp) ≤ Real.exp (-(lam * t)) := by
    calc (Real.exp (-(lam * t))) ^ (N - mp)
        ≤ (Real.exp (-(lam * t))) ^ 1 := pow_le_pow_of_le_one he.le he1 hNmp
      _ = Real.exp (-(lam * t)) := by rw [pow_one]
  have hpe0 : (0:ℝ) ≤ (Real.exp (-(lam * t))) ^ (N - mp) := pow_nonneg he.le _
  -- key analytic bound: t · e^{-λt} ≤ (2/λ) · e^{-(λ/2)t}
  have hkey : t * Real.exp (-(lam * t)) ≤ (2 / lam) * Real.exp (-(lam/2) * t) := by
    have hx : (lam/2) * t ≤ Real.exp ((lam/2) * t) := by
      have := Real.add_one_le_exp ((lam/2) * t)
      linarith
    have hpos : (0:ℝ) < Real.exp (-(lam/2) * t) := Real.exp_pos _
    have hmul : (lam/2) * t * Real.exp (-(lam/2) * t) ≤ 1 := by
      have h2 : (lam/2) * t * Real.exp (-(lam/2) * t)
          ≤ Real.exp ((lam/2) * t) * Real.exp (-(lam/2) * t) := by
        apply mul_le_mul_of_nonneg_right hx hpos.le
      rw [← Real.exp_add] at h2
      have : (lam/2) * t + -(lam/2) * t = 0 := by ring
      rw [this, Real.exp_zero] at h2
      exact h2
    have ht2 : t * Real.exp (-(lam/2) * t) ≤ 2 / lam := by
      rw [le_div_iff₀ hlam]
      nlinarith [hmul]
    have hsplit : Real.exp (-(lam * t)) = Real.exp (-(lam/2) * t) * Real.exp (-(lam/2) * t) := by
      rw [← Real.exp_add]; congr 1; ring
    calc t * Real.exp (-(lam * t))
        = (t * Real.exp (-(lam/2) * t)) * Real.exp (-(lam/2) * t) := by rw [hsplit]; ring
      _ ≤ (2 / lam) * Real.exp (-(lam/2) * t) := by
          apply mul_le_mul_of_nonneg_right ht2 hpos.le
  -- assemble
  rw [Real.norm_eq_abs]
  have ht0 : (0:ℝ) ≤ t := ht.le
  have habs : |t * ((N : ℝ) * (Nat.choose (N-1) mp : ℝ) * (1 - Real.exp (-(lam * t))) ^ mp
        * (Real.exp (-(lam * t))) ^ (N - mp) * lam)|
      = D * (t * ((1 - Real.exp (-(lam * t))) ^ mp * (Real.exp (-(lam * t))) ^ (N - mp))) := by
    rw [hD]
    rw [show t * ((N : ℝ) * (Nat.choose (N-1) mp : ℝ) * (1 - Real.exp (-(lam * t))) ^ mp
        * (Real.exp (-(lam * t))) ^ (N - mp) * lam)
        = ((N : ℝ) * (Nat.choose (N-1) mp : ℝ) * lam)
            * (t * ((1 - Real.exp (-(lam * t))) ^ mp * (Real.exp (-(lam * t))) ^ (N - mp))) by ring]
    rw [abs_mul, abs_of_nonneg (a := t * ((1 - Real.exp (-(lam * t))) ^ mp * (Real.exp (-(lam * t))) ^ (N - mp))) (by positivity)]
  rw [habs]
  have hDnn : (0:ℝ) ≤ D := by rw [hD]; exact abs_nonneg _
  have hbound1 : t * ((1 - Real.exp (-(lam * t))) ^ mp * (Real.exp (-(lam * t))) ^ (N - mp))
      ≤ t * Real.exp (-(lam * t)) := by
    apply mul_le_mul_of_nonneg_left _ ht0
    calc (1 - Real.exp (-(lam * t))) ^ mp * (Real.exp (-(lam * t))) ^ (N - mp)
        ≤ 1 * Real.exp (-(lam * t)) := mul_le_mul hpm hpe hpe0 (by norm_num)
      _ = Real.exp (-(lam * t)) := by ring
  calc D * (t * ((1 - Real.exp (-(lam * t))) ^ mp * (Real.exp (-(lam * t))) ^ (N - mp)))
      ≤ D * (t * Real.exp (-(lam * t))) := by
        apply mul_le_mul_of_nonneg_left hbound1 hDnn
    _ ≤ D * ((2 / lam) * Real.exp (-(lam/2) * t)) := by
        apply mul_le_mul_of_nonneg_left hkey hDnn
    _ = C * Real.exp (-(lam/2) * t) := by rw [hC]; ring



end

/- Grace · https://prove2.me/theorems/c8122852-6838-41ec-a67c-4d6ea033566d · accepted submission 99c55209-2845-4c46-9e51-7b1468c5ae1d -/

section


set_option autoImplicit false
open Finset Set Filter Topology
open scoped BigOperators

theorem waiting_time_tail_decay (N mp : ℕ) (lam : ℝ) (h : mp < N) (hlam : 0 < lam) :
    Filter.Tendsto (fun t => t * (1 -
      ∑ k ∈ Finset.Ico (mp+1) (N+1),
        (Nat.choose N k : ℝ) * (1 - Real.exp (-(lam * t))) ^ k * (Real.exp (-(lam * t))) ^ (N - k)))
      Filter.atTop (nhds 0) := by
  -- inline `full_sum_eq_one` + `one_sub_Fcdf`: rewrite (1 - upper sum) = lower partial sum (k=0..mp)
  have hone_sub : ∀ s : ℝ,
      1 - ∑ k ∈ Finset.Ico (mp+1) (N+1),
            (Nat.choose N k : ℝ) * (1 - Real.exp (-(lam * s))) ^ k * (Real.exp (-(lam * s))) ^ (N - k)
        = ∑ k ∈ Finset.range (mp+1),
            (Nat.choose N k : ℝ) * (1 - Real.exp (-(lam * s))) ^ k * (Real.exp (-(lam * s))) ^ (N - k) := by
    intro s
    set e := Real.exp (-(lam * s)) with he
    -- full binomial sum = 1
    have hfull : (∑ k ∈ Finset.range (N+1),
        (Nat.choose N k : ℝ) * (1 - e) ^ k * e ^ (N - k)) = 1 := by
      have hb : ((1 - e) + e) ^ N = ∑ k ∈ Finset.range (N+1),
          (1 - e) ^ k * e ^ (N - k) * (Nat.choose N k : ℝ) := add_pow (1-e) e N
      have hcongr : (∑ k ∈ Finset.range (N+1), (Nat.choose N k : ℝ) * (1 - e) ^ k * e ^ (N - k))
          = ∑ k ∈ Finset.range (N+1), (1 - e) ^ k * e ^ (N - k) * (Nat.choose N k : ℝ) := by
        apply Finset.sum_congr rfl; intro k _; ring
      rw [hcongr, ← hb]
      norm_num
    have hsplit : Finset.range (N+1) = Finset.range (mp+1) ∪ Finset.Ico (mp+1) (N+1) := by
      rw [Finset.range_eq_Ico, Finset.range_eq_Ico,
        Finset.Ico_union_Ico_eq_Ico (by omega) (by omega)]
    have hdisj : Disjoint (Finset.range (mp+1)) (Finset.Ico (mp+1) (N+1)) := by
      rw [Finset.range_eq_Ico]; apply Finset.Ico_disjoint_Ico_consecutive
    rw [hsplit, Finset.sum_union hdisj] at hfull
    linarith [hfull]
  -- rewrite the whole function via hone_sub then mul_sum
  have hrw : (fun t => t * (1 -
        ∑ k ∈ Finset.Ico (mp+1) (N+1),
          (Nat.choose N k : ℝ) * (1 - Real.exp (-(lam * t))) ^ k * (Real.exp (-(lam * t))) ^ (N - k)))
      = (fun t => ∑ k ∈ Finset.range (mp+1),
          t * ((Nat.choose N k : ℝ) * (1 - Real.exp (-(lam * t))) ^ k
              * (Real.exp (-(lam * t))) ^ (N - k))) := by
    funext t
    rw [hone_sub t, Finset.mul_sum]
  rw [hrw]
  -- show the sum tends to 0 = ∑ 0
  have hzero : (0 : ℝ) = ∑ k ∈ Finset.range (mp+1), (0 : ℝ) := by simp
  rw [hzero]
  apply tendsto_finset_sum (Finset.range (mp+1))
  intro k hk
  rw [Finset.mem_range] at hk
  have hkN : k < N := by omega
  -- each term → 0 by squeeze; t·e^{-λt} → 0
  have htexp : Tendsto (fun t : ℝ => t * Real.exp (-(lam * t))) atTop (𝓝 0) := by
    have hcomp : Tendsto (fun u : ℝ => u ^ 1 * Real.exp (-u)) atTop (𝓝 0) :=
      Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 1
    have hlin : Tendsto (fun t : ℝ => lam * t) atTop atTop :=
      Filter.Tendsto.const_mul_atTop hlam tendsto_id
    have hc := hcomp.comp hlin
    have : Tendsto (fun t : ℝ => (1/lam) * ((lam * t) ^ 1 * Real.exp (-(lam * t)))) atTop (𝓝 ((1/lam) * 0)) :=
      hc.const_mul (1/lam)
    rw [mul_zero] at this
    refine this.congr ?_
    intro t
    field_simp
  set g : ℝ → ℝ := fun t => (Nat.choose N k : ℝ) * (1 - Real.exp (-(lam * t))) ^ k
      * (Real.exp (-(lam * t))) ^ (N - k) with hg
  apply squeeze_zero_norm' (a := fun t => (Nat.choose N k : ℝ) * (t * Real.exp (-(lam * t))))
  · filter_upwards [eventually_ge_atTop (0:ℝ)] with t ht
    have he : (0:ℝ) < Real.exp (-(lam * t)) := Real.exp_pos _
    have he1 : Real.exp (-(lam * t)) ≤ 1 := by
      rw [Real.exp_le_one_iff]; nlinarith [ht, hlam]
    have hq0 : (0:ℝ) ≤ 1 - Real.exp (-(lam * t)) := by linarith
    have hq1 : 1 - Real.exp (-(lam * t)) ≤ 1 := by linarith [he.le]
    have hpm : (1 - Real.exp (-(lam * t))) ^ k ≤ 1 := pow_le_one₀ hq0 hq1
    have hNk : 1 ≤ N - k := by omega
    have hpe : (Real.exp (-(lam * t))) ^ (N - k) ≤ Real.exp (-(lam * t)) := by
      calc (Real.exp (-(lam * t))) ^ (N - k)
          ≤ (Real.exp (-(lam * t))) ^ 1 := pow_le_pow_of_le_one he.le he1 hNk
        _ = Real.exp (-(lam * t)) := by rw [pow_one]
    have hpe0 : (0:ℝ) ≤ (Real.exp (-(lam * t))) ^ (N - k) := pow_nonneg he.le _
    rw [Real.norm_eq_abs]
    have habs : |t * g t|
        = (Nat.choose N k : ℝ) * (t * ((1 - Real.exp (-(lam * t))) ^ k * (Real.exp (-(lam * t))) ^ (N - k))) := by
      rw [hg]
      rw [show t * ((Nat.choose N k : ℝ) * (1 - Real.exp (-(lam * t))) ^ k * (Real.exp (-(lam * t))) ^ (N - k))
          = (Nat.choose N k : ℝ) * (t * ((1 - Real.exp (-(lam * t))) ^ k * (Real.exp (-(lam * t))) ^ (N - k))) by ring]
      rw [abs_of_nonneg (by positivity)]
    rw [habs]
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    apply mul_le_mul_of_nonneg_left _ ht
    calc (1 - Real.exp (-(lam * t))) ^ k * (Real.exp (-(lam * t))) ^ (N - k)
        ≤ 1 * Real.exp (-(lam * t)) := mul_le_mul hpm hpe hpe0 (by norm_num)
      _ = Real.exp (-(lam * t)) := by ring
  · have := htexp.const_mul (Nat.choose N k : ℝ)
    rw [mul_zero] at this
    exact this



end

/- Grace · https://prove2.me/theorems/39f3fac2-cd97-4607-acdc-f246bc4be318 · accepted submission 6e0593d7-e2fc-467e-a1d0-909d31cc2d9f -/

section


set_option autoImplicit false
open MeasureTheory Set Filter Topology

/-- **Survival-function mean identity (improper integration by parts).**
For `F : ℝ → ℝ` the CDF of a nonnegative random variable with density `f` (`HasDerivAt F (f x) x`),
`E[T] = ∫₀^∞ t·f(t) dt = ∫₀^∞ (1 - F(t)) dt`, provided the boundary term `t·(1-F(t)) → 0` as
`t → ∞` and the two integrands are integrable on `(0,∞)`.  The `t → 0⁺` boundary contributes `0`
automatically.  This is the standard layer-cake / tail-integral identity for a nonnegative RV. -/
theorem survival_mean_ibp (F f : ℝ → ℝ)
    (hF : ∀ x, HasDerivAt F (f x) x)
    (hint_tf : IntegrableOn (fun t => t * f t) (Ioi (0:ℝ)))
    (hint_surv : IntegrableOn (fun t => 1 - F t) (Ioi (0:ℝ)))
    (hdecay : Tendsto (fun t => t * (1 - F t)) atTop (𝓝 0)) :
    ∫ t in Ioi (0:ℝ), t * f t = ∫ t in Ioi (0:ℝ), (1 - F t) := by
  -- IBP with u(t) = t, v(t) = 1 - F t, u'(t) = 1, v'(t) = -f t.
  set u : ℝ → ℝ := fun t => t with hu_def
  set v : ℝ → ℝ := fun t => 1 - F t with hv_def
  set u' : ℝ → ℝ := fun _ => (1:ℝ) with hu'_def
  set v' : ℝ → ℝ := fun t => -f t with hv'_def
  have hu : ∀ x ∈ Ioi (0:ℝ), HasDerivAt u (u' x) x := by
    intro x _; exact hasDerivAt_id' x
  have hv : ∀ x ∈ Ioi (0:ℝ), HasDerivAt v (v' x) x := by
    intro x _
    have := (hF x).const_sub 1
    simpa [hv_def, hv'_def] using this
  have huv' : IntegrableOn (u * v') (Ioi (0:ℝ)) := by
    have : (u * v') = (fun t => t * (-f t)) := by
      funext t; simp [hu_def, hv'_def, Pi.mul_apply]
    rw [this]
    have : (fun t => t * (-f t)) = (fun t => -(t * f t)) := by funext t; ring
    rw [this]; exact hint_tf.neg
  have hu'v : IntegrableOn (u' * v) (Ioi (0:ℝ)) := by
    have : (u' * v) = (fun t => 1 - F t) := by
      funext t; simp [hu'_def, hv_def, Pi.mul_apply]
    rw [this]; exact hint_surv
  have h_zero : Tendsto (u * v) (𝓝[>] (0:ℝ)) (𝓝 (0:ℝ)) := by
    have hFcont : Continuous F := by
      apply continuous_iff_continuousAt.mpr
      intro x; exact (hF x).continuousAt
    have h1 : Continuous u := continuous_id'
    have h2 : Continuous v := continuous_const.sub hFcont
    have huvcont : Continuous (u * v) := by
      simpa [Pi.mul_def] using h1.mul h2
    have hat0 : Tendsto (u * v) (𝓝 (0:ℝ)) (𝓝 ((u * v) 0)) := huvcont.continuousAt
    have hval : (u * v) 0 = 0 := by simp [hu_def, hv_def, Pi.mul_apply]
    rw [hval] at hat0
    exact hat0.mono_left nhdsWithin_le_nhds
  have h_infty : Tendsto (u * v) atTop (𝓝 (0:ℝ)) := by
    have : (u * v) = (fun t => t * (1 - F t)) := by
      funext t; simp [hu_def, hv_def, Pi.mul_apply]
    rw [this]; exact hdecay
  have key := integral_Ioi_mul_deriv_eq_deriv_mul hu hv huv' hu'v h_zero h_infty
  -- key : ∫ u·v' = 0 - 0 - ∫ u'·v
  simp only [sub_zero, zero_sub] at key
  -- ∫ t·(-f) = -∫ (1-F)
  have lhs_eq : ∫ x in Ioi (0:ℝ), u x * v' x = -∫ t in Ioi (0:ℝ), t * f t := by
    rw [← integral_neg]
    apply setIntegral_congr_fun measurableSet_Ioi
    intro t _; simp only [hu_def, hv'_def]; ring
  have rhs_eq : ∫ x in Ioi (0:ℝ), u' x * v x = ∫ t in Ioi (0:ℝ), (1 - F t) := by
    apply setIntegral_congr_fun measurableSet_Ioi
    intro t _; simp [hu'_def, hv_def]
  rw [lhs_eq, rhs_eq] at key
  linarith [key]


end

/- Grace · https://prove2.me/theorems/c3367394-55a5-4510-bfff-1e64b2e20d41 · accepted submission 21c3d5a8-701a-4fb1-94fd-c465ea518c48 -/

section


set_option autoImplicit false
open MeasureTheory Set

theorem exp_substitution_Ioi_to_Ioo (lam : ℝ) (hlam : 0 < lam) (g : ℝ → ℝ) :
    ∫ t in Ioi (0:ℝ), |lam * Real.exp (-(lam * t))| * g (1 - Real.exp (-(lam * t)))
      = ∫ u in Ioo (0:ℝ) 1, g u := by
  set f : ℝ → ℝ := fun t => 1 - Real.exp (-(lam * t)) with hf
  set f' : ℝ → ℝ := fun t => lam * Real.exp (-(lam * t)) with hf'
  -- f '' Ioi 0 = Ioo 0 1
  have himg : f '' Ioi 0 = Ioo (0:ℝ) 1 := by
    ext y
    constructor
    · rintro ⟨t, ht, rfl⟩
      rw [mem_Ioi] at ht
      simp only [hf, mem_Ioo]
      have he : (0:ℝ) < Real.exp (-(lam * t)) := Real.exp_pos _
      have he1 : Real.exp (-(lam * t)) < 1 := by
        rw [Real.exp_lt_one_iff]; nlinarith [ht, hlam]
      constructor <;> linarith
    · intro hy
      rw [mem_Ioo] at hy
      obtain ⟨hy0, hy1⟩ := hy
      -- t = -log(1-y)/lam
      refine ⟨-(Real.log (1 - y)) / lam, ?_, ?_⟩
      · rw [mem_Ioi]
        have h1y : (0:ℝ) < 1 - y := by linarith
        have hlog : Real.log (1 - y) < 0 := Real.log_neg h1y (by linarith)
        rw [div_pos_iff]; left; constructor <;> [linarith; linarith]
      · simp only [hf]
        have h1y : (0:ℝ) < 1 - y := by linarith
        rw [show -(lam * (-(Real.log (1 - y)) / lam)) = Real.log (1 - y) by field_simp]
        rw [Real.exp_log h1y]; ring
  -- HasDerivWithinAt on Ioi 0
  have hderiv : ∀ t ∈ Ioi (0:ℝ), HasDerivWithinAt f (f' t) (Ioi 0) t := by
    intro t _
    have hexp : HasDerivAt (fun s : ℝ => Real.exp (-(lam * s)))
        (Real.exp (-(lam * t)) * (-lam)) t := by
      have hinner : HasDerivAt (fun s : ℝ => -(lam * s)) (-lam) t :=
        ((hasDerivAt_id t).const_mul lam).neg.congr_deriv (by ring)
      exact hinner.exp
    have hF : HasDerivAt f (f' t) t := by
      show HasDerivAt (fun t => 1 - Real.exp (-(lam * t))) (lam * Real.exp (-(lam * t))) t
      exact (hexp.const_sub 1).congr_deriv (by ring)
    exact hF.hasDerivWithinAt
  -- InjOn
  have hinj : InjOn f (Ioi 0) := by
    intro a _ b _ hab
    simp only [hf] at hab
    have : Real.exp (-(lam * a)) = Real.exp (-(lam * b)) := by linarith
    have h2 : -(lam * a) = -(lam * b) := Real.exp_injective this
    have : lam * a = lam * b := by linarith
    exact mul_left_cancel₀ (by linarith : lam ≠ 0) this
  have hmeas : MeasurableSet (Ioi (0:ℝ)) := measurableSet_Ioi
  have key := integral_image_eq_integral_abs_deriv_smul hmeas hderiv hinj g
  rw [himg] at key
  rw [key]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro t _
  simp only [hf, hf', smul_eq_mul]


end

/- Grace · https://prove2.me/theorems/94d6a281-94f3-4cd5-9989-5f758baccd56 · accepted submission 78511161-8125-4b23-91db-3fbc523cc360 -/

section


set_option autoImplicit false
open scoped BigOperators
open intervalIntegral MeasureTheory

namespace BetaNat

-- base case: ∫₀¹ (1-u)^j = 1/(j+1)
theorem beta_base (j : ℕ) :
    ∫ u in (0:ℝ)..1, (1 - u) ^ j = 1 / (j + 1) := by
  have hjne : ((j:ℝ)+1) ≠ 0 := by positivity
  have hd : ∀ u ∈ Set.uIcc (0:ℝ) 1,
      HasDerivAt (fun u : ℝ => (-(1 / ((j:ℝ)+1))) * (1 - u) ^ (j+1)) ((1 - u) ^ j) u := by
    intro u _
    have h1 : HasDerivAt (fun u : ℝ => (1 - u) ^ (j+1))
        (-(((j+1 : ℕ) : ℝ) * (1 - u) ^ j)) u := by
      have hb : HasDerivAt (fun u : ℝ => (1 - u)) (-1) u := by
        simpa using (hasDerivAt_id u).const_sub 1
      have := (hasDerivAt_pow (j+1) (1 - u)).comp u hb
      exact this.congr_deriv (by simp only [Nat.add_sub_cancel]; push_cast; ring)
    have h2 := h1.const_mul (-(1 / ((j:ℝ)+1)))
    refine h2.congr_deriv ?_
    have hc : ((j:ℝ)+1) * (1 / ((j:ℝ)+1)) = 1 := mul_one_div_cancel hjne
    push_cast
    linear_combination ((1 - u) ^ j) * hc
  rw [integral_eq_sub_of_hasDerivAt hd
    (by apply Continuous.intervalIntegrable; fun_prop)]
  simp only [sub_self]
  rw [zero_pow (by omega : j+1 ≠ 0)]
  simp only [sub_zero, one_pow, mul_one, mul_zero]
  field_simp
  ring

-- recurrence: ∫₀¹ u^{k+1}(1-u)^j = ((k+1)/(j+1)) ∫₀¹ u^k (1-u)^{j+1}
theorem beta_rec (k j : ℕ) :
    ∫ u in (0:ℝ)..1, u ^ (k+1) * (1 - u) ^ j
      = ((k+1 : ℝ) / (j+1)) * ∫ u in (0:ℝ)..1, u ^ k * (1 - u) ^ (j+1) := by
  have hjne : ((j:ℝ)+1) ≠ 0 := by positivity
  -- U = u^{k+1}, U' = (k+1) u^k ;  V = -(1-u)^{j+1}/(j+1), V' = (1-u)^j
  set U : ℝ → ℝ := fun u => u ^ (k+1) with hU
  set U' : ℝ → ℝ := fun u => ((k+1 : ℕ) : ℝ) * u ^ k with hU'
  set V : ℝ → ℝ := fun u => (-(1 / ((j:ℝ)+1))) * (1 - u) ^ (j+1) with hV
  set V' : ℝ → ℝ := fun u => (1 - u) ^ j with hV'
  have hUd : ∀ x ∈ Set.uIcc (0:ℝ) 1, HasDerivAt U (U' x) x := by
    intro x _; simpa [hU, hU'] using hasDerivAt_pow (k+1) x
  have hVd : ∀ x ∈ Set.uIcc (0:ℝ) 1, HasDerivAt V (V' x) x := by
    intro x _
    have h1 : HasDerivAt (fun u : ℝ => (1 - u) ^ (j+1))
        (-(((j+1 : ℕ) : ℝ) * (1 - x) ^ j)) x := by
      have hb : HasDerivAt (fun u : ℝ => (1 - u)) (-1) x := by
        simpa using (hasDerivAt_id x).const_sub 1
      have := (hasDerivAt_pow (j+1) (1 - x)).comp x hb
      exact this.congr_deriv (by simp only [Nat.add_sub_cancel]; push_cast; ring)
    have h2 := h1.const_mul (-(1 / ((j:ℝ)+1)))
    refine h2.congr_deriv ?_
    have hc : ((j:ℝ)+1) * (1 / ((j:ℝ)+1)) = 1 := mul_one_div_cancel hjne
    push_cast
    linear_combination ((1 - x) ^ j) * hc
  have hU'int : IntervalIntegrable U' MeasureTheory.volume 0 1 := by
    apply Continuous.intervalIntegrable; rw [hU']; fun_prop
  have hV'int : IntervalIntegrable V' MeasureTheory.volume 0 1 := by
    apply Continuous.intervalIntegrable; rw [hV']; fun_prop
  have hibp := intervalIntegral.integral_mul_deriv_eq_deriv_mul hUd hVd hU'int hV'int
  -- hibp : ∫ U x * V' x = U 1 * V 1 - U 0 * V 0 - ∫ U' x * V x
  -- boundary = 0
  have hb1 : U 1 * V 1 = 0 := by simp [hU, hV]
  have hb0 : U 0 * V 0 = 0 := by simp [hU]
  rw [hb1, hb0] at hibp
  simp only [sub_zero, zero_sub] at hibp
  -- LHS of hibp = ∫ u^{k+1}(1-u)^j
  have hlhs : (∫ x in (0:ℝ)..1, U x * V' x) = ∫ u in (0:ℝ)..1, u ^ (k+1) * (1 - u) ^ j := by
    apply intervalIntegral.integral_congr; intro x _; simp [hU, hV']
  -- RHS integrand: U' x * V x = (k+1) u^k * (-(1/(j+1)))(1-u)^{j+1}
  have hrhs : (∫ x in (0:ℝ)..1, U' x * V x)
      = (-(((k+1:ℕ):ℝ)/((j:ℝ)+1))) * ∫ u in (0:ℝ)..1, u ^ k * (1 - u) ^ (j+1) := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr; intro x _
    simp only [hU', hV]; push_cast; ring
  rw [hlhs, hrhs] at hibp
  rw [hibp]
  push_cast; ring

-- full Beta-at-naturals:  ∫₀¹ u^k(1-u)^j = k! j! / (k+j+1)!
theorem beta_nat (k j : ℕ) :
    ∫ u in (0:ℝ)..1, u ^ k * (1 - u) ^ j
      = (Nat.factorial k * Nat.factorial j : ℝ) / Nat.factorial (k + j + 1) := by
  induction k generalizing j with
  | zero =>
    simp only [pow_zero, one_mul, Nat.factorial_zero, Nat.cast_one, one_mul, Nat.zero_add]
    rw [beta_base j]
    rw [Nat.factorial_succ j]
    have hj1 : ((j:ℝ)+1) ≠ 0 := by positivity
    have hfac : (Nat.factorial j : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero _
    push_cast
    field_simp
  | succ k ih =>
    rw [beta_rec k j, ih (j+1)]
    rw [Nat.factorial_succ (k), Nat.factorial_succ (j)]
    have he : (k+1) + j + 1 = k + (j+1) + 1 := by omega
    rw [he]
    have hk1 : ((k:ℝ)+1) ≠ 0 := by positivity
    have hj1 : ((j:ℝ)+1) ≠ 0 := by positivity
    have hfac : (Nat.factorial (k + (j+1) + 1) : ℝ) ≠ 0 := by
      exact_mod_cast Nat.factorial_ne_zero _
    push_cast
    field_simp

end BetaNat

theorem beta_nat_factorial (k j : ℕ) :
    ∫ u in (0:ℝ)..1, u ^ k * (1 - u) ^ j
      = (Nat.factorial k * Nat.factorial j : ℝ) / Nat.factorial (k + j + 1) :=
  BetaNat.beta_nat k j


end

/- Grace · https://prove2.me/theorems/0c95e3a2-a95f-40c1-b796-c3227bda3f7c · accepted submission 6439f4aa-a71b-426a-897e-d66253c822c3 -/

section


set_option autoImplicit false
open MeasureTheory Set
open scoped BigOperators

theorem waiting_survival_per_term_integral (N k : ℕ) (lam : ℝ) (hlam : 0 < lam) (hk : k < N) :
    ∫ t in Ioi (0:ℝ), (1 - Real.exp (-(lam * t))) ^ k * (Real.exp (-(lam * t))) ^ (N - k)
      = (1 / lam) * ((Nat.factorial k * Nat.factorial (N - k - 1) : ℝ) / Nat.factorial N) := by
  -- apply subst with g(u) = u^k (1-u)^{N-k-1} / lam
  have hkey := exp_substitution_Ioi_to_Ioo lam hlam (fun u => u ^ k * (1 - u) ^ (N - k - 1) / lam)
  -- LHS of hkey simplifies to our target integral
  have hL : (∫ t in Ioi (0:ℝ), |lam * Real.exp (-(lam * t))|
        * ((1 - Real.exp (-(lam * t))) ^ k * (1 - (1 - Real.exp (-(lam * t)))) ^ (N - k - 1) / lam))
      = ∫ t in Ioi (0:ℝ), (1 - Real.exp (-(lam * t))) ^ k * (Real.exp (-(lam * t))) ^ (N - k) := by
    apply setIntegral_congr_fun measurableSet_Ioi
    intro t _
    simp only []
    have he : (0:ℝ) < Real.exp (-(lam * t)) := Real.exp_pos _
    have habs : |lam * Real.exp (-(lam * t))| = lam * Real.exp (-(lam * t)) := by
      rw [abs_of_pos]; positivity
    rw [habs]
    have h1q : (1 - (1 - Real.exp (-(lam * t)))) = Real.exp (-(lam * t)) := by ring
    rw [h1q]
    have hNk : N - k = (N - k - 1) + 1 := by omega
    rw [hNk, pow_succ]
    have hlne : lam ≠ 0 := ne_of_gt hlam
    field_simp
    rw [show N - k - 1 + 1 - 1 = N - k - 1 from by omega]
  rw [hL] at hkey
  rw [hkey]
  -- RHS: ∫_{Ioo 0 1} u^k (1-u)^{N-k-1}/lam  = (1/lam) ∫_{Ioo} u^k(1-u)^{N-k-1}
  have hR : (∫ u in Ioo (0:ℝ) 1, u ^ k * (1 - u) ^ (N - k - 1) / lam)
      = (1 / lam) * ∫ u in Ioo (0:ℝ) 1, u ^ k * (1 - u) ^ (N - k - 1) := by
    rw [← integral_const_mul]
    apply setIntegral_congr_fun measurableSet_Ioo
    intro u _; ring
  rw [hR]
  -- convert Ioo to interval and apply beta_nat
  have hconv : (∫ u in Ioo (0:ℝ) 1, u ^ k * (1 - u) ^ (N - k - 1))
      = ∫ u in (0:ℝ)..1, u ^ k * (1 - u) ^ (N - k - 1) := by
    rw [intervalIntegral.integral_of_le (by norm_num : (0:ℝ) ≤ 1), integral_Ioc_eq_integral_Ioo]
  rw [hconv, beta_nat_factorial k (N - k - 1)]
  have hNeq : k + (N - k - 1) + 1 = N := by omega
  rw [hNeq]


end

/- Grace · https://prove2.me/theorems/4086b21a-ad15-409b-8e73-3199cfe7e009 · accepted submission 53dc331d-0b85-4b89-bf91-754c4e1167de -/

section


set_option autoImplicit false
open MeasureTheory Set Finset
open scoped BigOperators

namespace SurvivalMean

-- per-term integrability (k < N so N-k ≥ 1)
theorem term_integrable (N k : ℕ) (lam : ℝ) (hlam : 0 < lam) (hk : k < N) :
    IntegrableOn (fun t : ℝ => (Nat.choose N k : ℝ)
      * (1 - Real.exp (-(lam * t))) ^ k * (Real.exp (-(lam * t))) ^ (N - k)) (Ioi (0:ℝ)) := by
  set C : ℝ := |(Nat.choose N k : ℝ)| with hC
  have hgint : IntegrableOn (fun t : ℝ => C * Real.exp (-lam * t)) (Ioi (0:ℝ)) := by
    have := integrableOn_exp_mul_Ioi (a := -lam) (c := (0:ℝ)) (by linarith)
    exact this.const_mul C
  have hcont : Continuous (fun t : ℝ => (Nat.choose N k : ℝ)
      * (1 - Real.exp (-(lam * t))) ^ k * (Real.exp (-(lam * t))) ^ (N - k)) := by fun_prop
  refine Integrable.mono' hgint hcont.aestronglyMeasurable.restrict ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  rw [Set.mem_Ioi] at ht
  have he : (0:ℝ) < Real.exp (-(lam * t)) := Real.exp_pos _
  have he1 : Real.exp (-(lam * t)) ≤ 1 := by rw [Real.exp_le_one_iff]; nlinarith [ht, hlam]
  have hq0 : (0:ℝ) ≤ 1 - Real.exp (-(lam * t)) := by linarith
  have hq1 : 1 - Real.exp (-(lam * t)) ≤ 1 := by linarith [he.le]
  have hpm : (1 - Real.exp (-(lam * t))) ^ k ≤ 1 := pow_le_one₀ hq0 hq1
  have hNk : 1 ≤ N - k := by omega
  have hpe : (Real.exp (-(lam * t))) ^ (N - k) ≤ Real.exp (-(lam * t)) := by
    calc (Real.exp (-(lam * t))) ^ (N - k)
        ≤ (Real.exp (-(lam * t))) ^ 1 := pow_le_pow_of_le_one he.le he1 hNk
      _ = Real.exp (-(lam * t)) := by rw [pow_one]
  have hpe0 : (0:ℝ) ≤ (Real.exp (-(lam * t))) ^ (N - k) := pow_nonneg he.le _
  rw [Real.norm_eq_abs]
  have hrw : |(Nat.choose N k : ℝ) * (1 - Real.exp (-(lam * t))) ^ k
      * (Real.exp (-(lam * t))) ^ (N - k)|
      = C * ((1 - Real.exp (-(lam * t))) ^ k * (Real.exp (-(lam * t))) ^ (N - k)) := by
    rw [hC]
    rw [show (Nat.choose N k : ℝ) * (1 - Real.exp (-(lam * t))) ^ k * (Real.exp (-(lam * t))) ^ (N - k)
      = (Nat.choose N k : ℝ) * ((1 - Real.exp (-(lam * t))) ^ k * (Real.exp (-(lam * t))) ^ (N - k)) by ring]
    rw [abs_mul, abs_of_nonneg (a := (1 - Real.exp (-(lam * t))) ^ k * (Real.exp (-(lam * t))) ^ (N - k)) (by positivity)]
  rw [hrw, show C * Real.exp (-lam * t) = C * Real.exp (-(lam * t)) by ring]
  apply mul_le_mul_of_nonneg_left _ (by rw [hC]; exact abs_nonneg _)
  calc (1 - Real.exp (-(lam * t))) ^ k * (Real.exp (-(lam * t))) ^ (N - k)
      ≤ 1 * Real.exp (-(lam * t)) := mul_le_mul hpm hpe hpe0 (by norm_num)
    _ = Real.exp (-(lam * t)) := by ring

-- per-term value WITH the binomial coefficient:  ∫ C(N,k)(1-e)^k e^{N-k} = (1/λ)/(N-k)
theorem per_term_coef (N k : ℕ) (lam : ℝ) (hlam : 0 < lam) (hk : k < N) :
    ∫ t in Ioi (0:ℝ), (Nat.choose N k : ℝ)
      * (1 - Real.exp (-(lam * t))) ^ k * (Real.exp (-(lam * t))) ^ (N - k)
      = (1 / lam) * (1 / ((N - k : ℕ) : ℝ)) := by
  have hfac : (∫ t in Ioi (0:ℝ), (Nat.choose N k : ℝ)
      * (1 - Real.exp (-(lam * t))) ^ k * (Real.exp (-(lam * t))) ^ (N - k))
      = (Nat.choose N k : ℝ) * ∫ t in Ioi (0:ℝ),
          (1 - Real.exp (-(lam * t))) ^ k * (Real.exp (-(lam * t))) ^ (N - k) := by
    rw [← integral_const_mul]
    apply setIntegral_congr_fun measurableSet_Ioi
    intro t _; ring
  rw [hfac, waiting_survival_per_term_integral N k lam hlam hk]
  -- C(N,k) * (1/λ) * (k!(N-k-1)!/N!) = (1/λ)/(N-k)
  -- use C(N,k) = N!/(k!(N-k)!), and (N-k)! = (N-k)*(N-k-1)!
  have hchoose : (Nat.choose N k : ℝ) = (Nat.factorial N : ℝ)
      / ((Nat.factorial k : ℝ) * (Nat.factorial (N - k) : ℝ)) := by
    have hk' : k ≤ N := le_of_lt hk
    have := Nat.choose_mul_factorial_mul_factorial hk'
    have hcast := congrArg (Nat.cast : ℕ → ℝ) this
    push_cast at hcast
    have hkf : (Nat.factorial k : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero _
    have hnkf : (Nat.factorial (N-k) : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero _
    field_simp
    linarith [hcast]
  rw [hchoose]
  have hNk : N - k = (N - k - 1) + 1 := by omega
  have hfsucc : Nat.factorial (N - k) = (N - k) * Nat.factorial (N - k - 1) := by
    conv_lhs => rw [hNk]
    rw [Nat.factorial_succ]
    congr 1; omega
  rw [hfsucc]
  have hkf : (Nat.factorial k : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero _
  have hnk1f : (Nat.factorial (N-k-1) : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero _
  have hNf : (Nat.factorial N : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero _
  have hNkpos : ((N - k : ℕ) : ℝ) ≠ 0 := by
    have h0 : 0 < N - k := by omega
    exact_mod_cast h0.ne'
  push_cast
  field_simp

/-- **Survival-function integral = harmonic-tail / λ.** The integral over (0,∞) of the
binomial survival function (lower partial sum, $k=0..m$) of the waiting-time model equals
$(1/λ)·∑_{k=0}^{m} 1/(N-k)$. For a nonnegative random variable this is $E[T]$ (mean of the
waiting time), the genuine harmonic mean identity. -/
theorem survival_mean (N m : ℕ) (lam : ℝ) (hlam : 0 < lam) (hm : m < N) :
    ∫ t in Ioi (0:ℝ), ∑ k ∈ Finset.range (m+1),
        (Nat.choose N k : ℝ) * (1 - Real.exp (-(lam * t))) ^ k * (Real.exp (-(lam * t))) ^ (N - k)
      = (1 / lam) * ∑ k ∈ Finset.range (m+1), (1 / ((N - k : ℕ) : ℝ)) := by
  have hint : ∀ k ∈ Finset.range (m+1), IntegrableOn (fun t : ℝ => (Nat.choose N k : ℝ)
      * (1 - Real.exp (-(lam * t))) ^ k * (Real.exp (-(lam * t))) ^ (N - k)) (Ioi (0:ℝ)) := by
    intro k hk
    rw [Finset.mem_range] at hk
    exact term_integrable N k lam hlam (by omega)
  rw [MeasureTheory.integral_finset_sum (Finset.range (m+1)) hint]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k hk
  rw [Finset.mem_range] at hk
  exact per_term_coef N k lam hlam (by omega)

end SurvivalMean

theorem waiting_time_survival_mean (N m : ℕ) (lam : ℝ) (hlam : 0 < lam) (hm : m < N) :
    ∫ t in Set.Ioi (0:ℝ), ∑ k ∈ Finset.range (m+1),
        (Nat.choose N k : ℝ) * (1 - Real.exp (-(lam * t))) ^ k * (Real.exp (-(lam * t))) ^ (N - k)
      = (1 / lam) * ∑ k ∈ Finset.range (m+1), (1 / ((N - k : ℕ) : ℝ)) :=
  SurvivalMean.survival_mean N m lam hlam hm


end

/- Grace · https://prove2.me/theorems/df8aa8f6-116f-4c3a-be87-1baf2439dbab · accepted submission 88be18a5-f77d-4ec3-bc8f-261c2bbd6af4 -/

section


set_option autoImplicit false

theorem siegel_cdf_average_ge_mean (μ : ℝ) (hμ : 0 ≤ μ) (F f : ℝ → ℝ)
    (hF : ∀ x ∈ Set.Ici (0:ℝ), HasDerivAt F (f x) x)
    (hfnn : ∀ x ∈ Set.Ici (0:ℝ), 0 ≤ f x)
    (hF0 : F 0 = 0)
    (hf_int_loc : ∀ b : ℝ, IntervalIntegrable f MeasureTheory.volume 0 b)
    (hf_mass : MeasureTheory.IntegrableOn f (Set.Ioi (0:ℝ)))
    (htf_mass : MeasureTheory.IntegrableOn (fun t => t * f t) (Set.Ioi (0:ℝ)))
    (hmass : ∫ t in Set.Ioi (0:ℝ), f t = 1)
    (hmean : ∫ t in Set.Ioi (0:ℝ), t * f t = μ) :
    μ ≤ ∫ t in (0:ℝ)..(2*μ), F t := by
  set b := 2 * μ with hb_def
  have hb : 0 ≤ b := by positivity
  have hF_uIcc : ∀ x ∈ Set.uIcc (0:ℝ) b, HasDerivAt F (f x) x := by
    intro x hx
    rw [Set.uIcc_of_le hb] at hx
    exact hF x (Set.mem_Ici.mpr (le_trans (le_refl 0) hx.1))
  have hv : ∀ x ∈ Set.uIcc (0:ℝ) b, HasDerivAt (fun t => t - b) (1 : ℝ) x := by
    intro x _; simpa using (hasDerivAt_id x).sub_const b
  have hv' : IntervalIntegrable (fun _ : ℝ => (1:ℝ)) MeasureTheory.volume 0 b :=
    _root_.intervalIntegrable_const
  have key := intervalIntegral.integral_mul_deriv_eq_deriv_mul hF_uIcc hv (hf_int_loc b) hv'
  simp only [mul_one] at key
  have hbb : (b - b) = (0:ℝ) := by ring
  rw [hbb, hF0] at key
  simp only [mul_zero, zero_mul, sub_zero, zero_sub] at key
  have hIBP : ∫ t in (0:ℝ)..b, F t = ∫ t in (0:ℝ)..b, (b - t) * f t := by
    rw [key, ← intervalIntegral.integral_neg]
    apply intervalIntegral.integral_congr; intro x _; simp only; ring
  have hloc_f : MeasureTheory.IntegrableOn f (Set.Ioc 0 b) := by
    have := (hf_int_loc b)
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hb] at this; exact this
  have hloc_tf : MeasureTheory.IntegrableOn (fun t => t * f t) (Set.Ioc 0 b) := by
    exact htf_mass.mono_set (Set.Ioc_subset_Ioi_self)
  have hsplit_set : ∫ t in (0:ℝ)..b, (b - t) * f t
      = b * (∫ t in Set.Ioc (0:ℝ) b, f t) - ∫ t in Set.Ioc (0:ℝ) b, t * f t := by
    rw [intervalIntegral.integral_of_le hb]
    rw [← MeasureTheory.integral_const_mul]
    rw [← MeasureTheory.integral_sub]
    · apply MeasureTheory.setIntegral_congr_fun measurableSet_Ioc
      intro x _; simp only; ring
    · exact hloc_f.const_mul b
    · exact hloc_tf
  have hUnion : Set.Ioi (0:ℝ) = Set.Ioc (0:ℝ) b ∪ Set.Ioi b := by
    rw [Set.Ioc_union_Ioi_eq_Ioi hb]
  have hdisj : Disjoint (Set.Ioc (0:ℝ) b) (Set.Ioi b) := Set.Ioc_disjoint_Ioi le_rfl
  have hf_Ioib : MeasureTheory.IntegrableOn f (Set.Ioi b) :=
    hf_mass.mono_set (by rw [hUnion]; exact Set.subset_union_right)
  have htf_Ioib : MeasureTheory.IntegrableOn (fun t => t * f t) (Set.Ioi b) :=
    htf_mass.mono_set (by rw [hUnion]; exact Set.subset_union_right)
  have hmass_split : (∫ t in Set.Ioc (0:ℝ) b, f t) + (∫ t in Set.Ioi b, f t) = 1 := by
    rw [← MeasureTheory.setIntegral_union hdisj measurableSet_Ioi hloc_f hf_Ioib, ← hUnion, hmass]
  have hmean_split : (∫ t in Set.Ioc (0:ℝ) b, t * f t) + (∫ t in Set.Ioi b, t * f t) = μ := by
    rw [← MeasureTheory.setIntegral_union hdisj measurableSet_Ioi hloc_tf htf_Ioib, ← hUnion, hmean]
  have htail_nn : 0 ≤ (∫ t in Set.Ioi b, t * f t) - b * (∫ t in Set.Ioi b, f t) := by
    have hbm : b * (∫ t in Set.Ioi b, f t) = ∫ t in Set.Ioi b, b * f t := by
      rw [MeasureTheory.integral_const_mul]
    rw [hbm, ← MeasureTheory.integral_sub htf_Ioib (hf_Ioib.const_mul b)]
    apply MeasureTheory.setIntegral_nonneg measurableSet_Ioi
    intro x hx
    have hxb : b ≤ x := le_of_lt hx
    have hfx : 0 ≤ f x := hfnn x (Set.mem_Ici.mpr (le_trans hb hxb))
    have hpos : (0:ℝ) ≤ (x - b) * f x := mul_nonneg (by linarith) hfx
    simpa [mul_comm, mul_sub] using hpos
  rw [hIBP, hsplit_set]
  have e1 : (∫ t in Set.Ioc (0:ℝ) b, f t) = 1 - (∫ t in Set.Ioi b, f t) := by
    linarith [hmass_split]
  have e2 : (∫ t in Set.Ioc (0:ℝ) b, t * f t) = μ - (∫ t in Set.Ioi b, t * f t) := by
    linarith [hmean_split]
  rw [e1, e2]
  have hbval : b = 2 * μ := hb_def
  nlinarith [htail_nn, hbval]


end

/- Grace · https://prove2.me/theorems/7dfcd41f-04d0-4d26-8831-fa060469fd57 · accepted submission a5b197ba-11cf-4807-9749-eea696a2cdaa -/

section


set_option autoImplicit false

open Set

theorem siegel_symmetrized_cdf_unimodal_from_density_sign
    (F f : ℝ → ℝ) (μ c : ℝ)
    (hF : ∀ x, HasDerivAt F (f x) x)
    (hgL : ∀ x ∈ Set.Icc (0:ℝ) c, f x - f (2 * μ - x) ≤ 0)
    (hgR : ∀ x ∈ Set.Icc c μ, 0 ≤ f x - f (2 * μ - x)) :
    AntitoneOn (fun x => (F x + F (2 * μ - x)) / 2) (Set.Icc 0 c)
      ∧ MonotoneOn (fun x => (F x + F (2 * μ - x)) / 2) (Set.Icc c μ) := by
  have hFhat : ∀ x : ℝ,
      HasDerivAt (fun y => (F y + F (2 * μ - y)) / 2) ((f x - f (2 * μ - x)) / 2) x := by
    intro x
    have hinner : HasDerivAt (fun y : ℝ => 2 * μ - y) (-1) x :=
      (hasDerivAt_id x).const_sub (2 * μ)
    have hcomp : HasDerivAt (fun y : ℝ => F (2 * μ - y)) (f (2 * μ - x) * (-1)) x :=
      (hF (2 * μ - x)).comp x hinner
    have hsum : HasDerivAt (fun y : ℝ => F y + F (2 * μ - y))
        (f x + f (2 * μ - x) * (-1)) x := (hF x).add hcomp
    have := hsum.div_const 2
    exact this.congr_deriv (by ring)
  refine ⟨?_, ?_⟩
  · apply antitoneOn_of_hasDerivWithinAt_nonpos (convex_Icc 0 c)
    · intro x _; exact ((hFhat x).continuousAt).continuousWithinAt
    · intro x _; exact (hFhat x).hasDerivWithinAt
    · intro x hx
      have hxIcc : x ∈ Set.Icc (0:ℝ) c := interior_subset hx
      have := hgL x hxIcc
      linarith
  · apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc c μ)
    · intro x _; exact ((hFhat x).continuousAt).continuousWithinAt
    · intro x _; exact (hFhat x).hasDerivWithinAt
    · intro x hx
      have hxIcc : x ∈ Set.Icc c μ := interior_subset hx
      have := hgR x hxIcc
      linarith


end

/- Grace · https://prove2.me/theorems/3fbb354c-469f-44eb-b1bb-eb549d9860e4 · accepted submission 3ff5d509-9e0f-4c20-bf42-c98b655b2e0c -/

section


set_option autoImplicit false
open MeasureTheory

theorem moustache_value_bound_mass
    (G : ℝ → ℝ) (μ c : ℝ) (hμ : 0 < μ) (hc0 : 0 ≤ c) (hcμ : c < μ)
    (hleft : AntitoneOn G (Set.Icc 0 c))
    (hright : MonotoneOn G (Set.Icc c μ))
    (hsym : ∀ x, G (2 * μ - x) = G x)
    (hG0 : G 0 ≤ (1/2 : ℝ))
    (hint : IntervalIntegrable G volume 0 (2 * μ))
    (havg : (1 / 2 : ℝ) ≤ (1 / (2 * μ)) * ∫ x in (0:ℝ)..(2 * μ), G x) :
    (1 / 2 : ℝ) ≤ G μ := by
  have hcμ' : c ≤ μ := le_of_lt hcμ
  have h2μ : (0:ℝ) ≤ 2 * μ := by positivity
  have hμle : μ ≤ 2 * μ := by linarith
  have hsub01 : Set.uIcc (0:ℝ) μ ⊆ Set.uIcc 0 (2 * μ) := by
    rw [Set.uIcc_of_le (le_of_lt hμ), Set.uIcc_of_le h2μ]; exact Set.Icc_subset_Icc (le_refl 0) hμle
  have hsub12 : Set.uIcc (μ:ℝ) (2 * μ) ⊆ Set.uIcc 0 (2 * μ) := by
    rw [Set.uIcc_of_le hμle, Set.uIcc_of_le h2μ]; exact Set.Icc_subset_Icc (le_of_lt hμ) (le_refl _)
  have hint01 : IntervalIntegrable G volume 0 μ := hint.mono_set hsub01
  have hint12 : IntervalIntegrable G volume μ (2 * μ) := hint.mono_set hsub12
  have hrefl : (∫ x in (μ)..(2*μ), G x) = ∫ x in (0:ℝ)..μ, G x := by
    have hcg : (∫ x in (μ)..(2*μ), G x) = ∫ x in (μ)..(2*μ), G (2 * μ - x) := by
      apply intervalIntegral.integral_congr; intro x _; exact (hsym x).symm
    rw [hcg, intervalIntegral.integral_comp_sub_left G (2 * μ)]
    rw [show (2 * μ - μ) = μ by ring, show (2 * μ - 2 * μ) = (0:ℝ) by ring]
  have hsplit : (∫ x in (0:ℝ)..(2*μ), G x) = 2 * ∫ x in (0:ℝ)..μ, G x := by
    have := intervalIntegral.integral_add_adjacent_intervals hint01 hint12
    rw [← this, hrefl]; ring
  rw [hsplit] at havg
  have hμpos2 : (0:ℝ) < 2 * μ := by positivity
  have hμhalf : μ / 2 ≤ ∫ x in (0:ℝ)..μ, G x := by
    set I := ∫ x in (0:ℝ)..μ, G x with hI
    have hx : (1 / (2 * μ)) * (2 * I) = (1/μ) * I := by field_simp
    rw [hx] at havg
    have hμI : μ * (1/2) ≤ μ * ((1/μ) * I) := by
      apply mul_le_mul_of_nonneg_left havg (le_of_lt hμ)
    rw [show μ * ((1/μ) * I) = I by field_simp] at hμI
    linarith [hμI]
  have hGc_le_half : ∀ x ∈ Set.Icc (0:ℝ) c, G x ≤ (1/2 : ℝ) := by
    intro x hx; exact le_trans (hleft ⟨le_refl 0, hc0⟩ hx hx.1) hG0
  have hGc_le_Gμ : ∀ x ∈ Set.Icc c μ, G x ≤ G μ := by
    intro x hx; exact hright hx ⟨hcμ', le_refl μ⟩ hx.2
  have hsub0c : Set.uIcc (0:ℝ) c ⊆ Set.uIcc 0 μ := by
    rw [Set.uIcc_of_le hc0, Set.uIcc_of_le (le_of_lt hμ)]; exact Set.Icc_subset_Icc (le_refl 0) hcμ'
  have hsubcμ : Set.uIcc c μ ⊆ Set.uIcc 0 μ := by
    rw [Set.uIcc_of_le hcμ', Set.uIcc_of_le (le_of_lt hμ)]; exact Set.Icc_subset_Icc hc0 (le_refl μ)
  have hint0c : IntervalIntegrable G volume 0 c := hint01.mono_set hsub0c
  have hintcμ : IntervalIntegrable G volume c μ := hint01.mono_set hsubcμ
  have hb1 : (∫ x in (0:ℝ)..c, G x) ≤ ∫ _ in (0:ℝ)..c, (1/2 : ℝ) :=
    intervalIntegral.integral_mono_on hc0 hint0c intervalIntegrable_const hGc_le_half
  have hb2 : (∫ x in (c)..μ, G x) ≤ ∫ _ in (c)..μ, G μ :=
    intervalIntegral.integral_mono_on hcμ' hintcμ intervalIntegrable_const hGc_le_Gμ
  rw [intervalIntegral.integral_const] at hb1 hb2
  simp only [smul_eq_mul] at hb1 hb2
  have hadd : (∫ x in (0:ℝ)..μ, G x) = (∫ x in (0:ℝ)..c, G x) + ∫ x in (c)..μ, G x :=
    (intervalIntegral.integral_add_adjacent_intervals hint0c hintcμ).symm
  have hcomb : μ / 2 ≤ (c - 0) * (1/2) + (μ - c) * G μ := by
    have := hμhalf; rw [hadd] at this; linarith [hb1, hb2]
  have hpos : (0:ℝ) < μ - c := by linarith
  nlinarith [hcomb, hpos, mul_pos hpos hpos]


end

/- Grace · https://prove2.me/theorems/ca07dd52-3c50-4ec3-ab7f-0913715a0ae4 · accepted submission c16f85f5-a64e-4084-a763-7913047c57c0 -/

section


set_option autoImplicit false
open Set

/-- The waiting-time log-density derivative `G'(s) = m·λ·e^{-λs}/(1-e^{-λs}) - (Nn-m)·λ`. -/
noncomputable def GlogD (lam m Nn : ℝ) (s : ℝ) : ℝ :=
  m * (lam * Real.exp (-lam * s) / (1 - Real.exp (-lam * s))) - (Nn - m) * lam

/-- The log-density `G(t) = m·log(1-e^{-λt}) - (Nn-m)·λt`. -/
noncomputable def Glog (lam m Nn : ℝ) (t : ℝ) : ℝ :=
  m * Real.log (1 - Real.exp (-lam * t)) - (Nn - m) * (lam * t)

theorem Glog_hasDeriv (lam m Nn : ℝ) (s : ℝ) (hs : 0 < s) (hlam : 0 < lam) :
    HasDerivAt (Glog lam m Nn) (GlogD lam m Nn s) s := by
  unfold Glog GlogD
  have hexp : HasDerivAt (fun y => Real.exp (-lam * y)) (-lam * Real.exp (-lam * s)) s := by
    have := (((hasDerivAt_id s).const_mul (-lam)).exp); simpa [mul_comm] using this
  have hone : HasDerivAt (fun y => 1 - Real.exp (-lam * y)) (lam * Real.exp (-lam * s)) s := by
    have := hexp.const_sub 1; simpa using this
  have hposne : (1 : ℝ) - Real.exp (-lam * s) ≠ 0 := by
    have : Real.exp (-lam * s) < 1 := by rw [Real.exp_lt_one_iff]; nlinarith
    linarith
  have hlog : HasDerivAt (fun y => Real.log (1 - Real.exp (-lam * y)))
      ((lam * Real.exp (-lam * s)) / (1 - Real.exp (-lam * s))) s := hone.log hposne
  have hlin : HasDerivAt (fun y => (Nn - m) * (lam * y)) ((Nn - m) * lam) s := by
    have h2 := ((hasDerivAt_id s).const_mul lam).const_mul (Nn - m); simpa [mul_assoc] using h2
  have hd := (hlog.const_mul m).sub hlin
  exact hd

/-- φ(t) = G(t) - G(2µ-t). -/
theorem phi_hasDeriv (lam m Nn mu : ℝ) (t : ℝ) (ht0 : 0 < t) (htmu : t < mu) (hlam : 0 < lam) :
    HasDerivAt (fun y => Glog lam m Nn y - Glog lam m Nn (2*mu - y))
      (GlogD lam m Nn t + GlogD lam m Nn (2*mu - t)) t := by
  have hpt : (0:ℝ) < 2*mu - t := by linarith
  have h1 := Glog_hasDeriv lam m Nn t ht0 hlam
  have hinner : HasDerivAt (fun y => 2*mu - y) (-1 : ℝ) t := by
    have := (hasDerivAt_id t).const_sub (2*mu); simpa using this
  have h2 := Glog_hasDeriv lam m Nn (2*mu - t) hpt hlam
  have hcomp : HasDerivAt (fun y => Glog lam m Nn (2*mu - y)) (GlogD lam m Nn (2*mu - t) * (-1)) t :=
    h2.comp t hinner
  have hd := h1.sub hcomp
  have hval : GlogD lam m Nn t + GlogD lam m Nn (2*mu - t)
      = GlogD lam m Nn t - GlogD lam m Nn (2*mu - t) * (-1) := by ring
  rw [hval]
  exact hd

/-- **Sign of φ' equals sign of the quadratic `Q(e^{λt})`.**  Concretely
`φ'(t) = (λ / (α·β·u)) · Q(u)` with `u = e^{λt}`, `α = e^{λt}-1`, `β = e^{λ(2µ-t)}-1`,
`A = e^{2λµ}`, and `Q(u) = (2Nn-m)u² - 2(Nn+(Nn-m)A)u + A(2Nn-m)`.  Since `λ, α, β, u > 0`,
`sign(φ'(t)) = sign(Q(e^{λt}))`. -/
theorem phiD_eq (lam m Nn mu : ℝ) (t : ℝ) (ht0 : 0 < t) (htmu : t < mu) (hlam : 0 < lam) :
    (GlogD lam m Nn t + GlogD lam m Nn (2*mu - t))
      = (lam / ((Real.exp (lam*t) - 1) * (Real.exp (lam*(2*mu-t)) - 1) * Real.exp (lam*t)))
        * ((2*Nn - m) * (Real.exp (lam*t))^2
           - 2*(Nn + (Nn - m)*Real.exp (2*lam*mu)) * Real.exp (lam*t)
           + Real.exp (2*lam*mu) * (2*Nn - m)) := by
  have hlt : Real.exp (-lam * t) < 1 := by rw [Real.exp_lt_one_iff]; nlinarith
  have hlt2 : Real.exp (-lam * (2*mu - t)) < 1 := by rw [Real.exp_lt_one_iff]; nlinarith
  set a : ℝ := 1 - Real.exp (-lam * t) with ha
  set b : ℝ := 1 - Real.exp (-lam * (2*mu - t)) with hb
  have hapos : 0 < a := by rw [ha]; linarith
  have hbpos : 0 < b := by rw [hb]; linarith
  have hane : a ≠ 0 := ne_of_gt hapos
  have hbne : b ≠ 0 := ne_of_gt hbpos
  -- express exponentials
  set EA : ℝ := Real.exp (lam*t) with hEA
  set EB : ℝ := Real.exp (lam*(2*mu-t)) with hEB
  have hEApos : 0 < EA := Real.exp_pos _
  have hEBpos : 0 < EB := Real.exp_pos _
  have hEA1 : 1 < EA := by rw [hEA, Real.one_lt_exp_iff]; nlinarith
  have hEB1 : 1 < EB := by rw [hEB, Real.one_lt_exp_iff]; nlinarith
  have heA : Real.exp (-lam*t) = EA⁻¹ := by rw [hEA, ← Real.exp_neg]; ring_nf
  have heB : Real.exp (-lam*(2*mu-t)) = EB⁻¹ := by rw [hEB, ← Real.exp_neg]; ring_nf
  have haEA : a = (EA - 1)/EA := by rw [ha, heA]; field_simp
  have hbEB : b = (EB - 1)/EB := by rw [hb, heB]; field_simp
  have hαpos : 0 < EA - 1 := by linarith
  have hβpos : 0 < EB - 1 := by linarith
  have hprod : EA * EB = Real.exp (2*lam*mu) := by rw [hEA, hEB, ← Real.exp_add]; ring_nf
  -- GlogD t = m*(lam*exp(-lt)/a) - (Nn-m)*lam ; rewrite exp(-lt)/a
  have hGt : GlogD lam m Nn t = m * (lam * (EA⁻¹ / a)) - (Nn - m) * lam := by
    unfold GlogD; rw [← ha, heA]; ring
  have hGt2 : GlogD lam m Nn (2*mu - t) = m * (lam * (EB⁻¹ / b)) - (Nn - m) * lam := by
    unfold GlogD; rw [show 2*mu - t = 2*mu - t from rfl]
    have : (1 - Real.exp (-lam * (2*mu - t))) = b := by rw [hb]
    rw [this, heB]; ring
  rw [hGt, hGt2]
  rw [haEA, hbEB]
  have hEAne : EA ≠ 0 := ne_of_gt hEApos
  have hEBne : EB ≠ 0 := ne_of_gt hEBpos
  have hα : EA - 1 ≠ 0 := ne_of_gt hαpos
  have hβ : EB - 1 ≠ 0 := ne_of_gt hβpos
  rw [← hprod]
  field_simp
  ring

/-- The quadratic `Qp A u = (2Nn-m)u² - 2(Nn+(Nn-m)A)u + A(2Nn-m)`. -/
noncomputable def Qp (m Nn A u : ℝ) : ℝ :=
  (2*Nn - m) * u^2 - 2*(Nn + (Nn - m)*A) * u + A * (2*Nn - m)

theorem Qp_at_one (m Nn A : ℝ) : Qp m Nn A 1 = m * (A - 1) := by
  unfold Qp; ring

theorem Qp_at_sqrtA (m Nn s : ℝ) : Qp m Nn (s^2) s = -2 * s * (s - 1) * ((Nn - m)*s - Nn) := by
  unfold Qp; ring

/-- `Qp` is strictly decreasing on `[1, s]` when `s ≤ vertex`, which holds under the mean
condition. We prove it directly: for `1 ≤ x < y ≤ s`, `Qp x > Qp y`. -/
theorem Qp_strictAnti (m Nn A s : ℝ) (hs1 : 1 < s) (hA : A = s^2)
    (hlead : 0 < 2*Nn - m) (hvert : s * (2*Nn - m) < Nn + (Nn - m)*A) :
    StrictAntiOn (Qp m Nn A) (Set.Icc 1 s) := by
  intro x hx y hy hxy
  simp only [Set.mem_Icc] at hx hy
  unfold Qp
  have hxs : x ≤ s := hx.2
  have hys : y ≤ s := hy.2
  have h1x : 1 ≤ x := hx.1
  -- Qp x - Qp y = (2Nn-m)(x²-y²) - 2(Nn+(Nn-m)A)(x-y)
  --            = (x-y)[(2Nn-m)(x+y) - 2(Nn+(Nn-m)A)]
  -- x-y<0, and (2Nn-m)(x+y) ≤ (2Nn-m)(2s) = 2s(2Nn-m) < 2(Nn+(Nn-m)A), so bracket<0, product>0
  nlinarith [hlead, hvert, hxy, h1x, hxs, hys, mul_pos hlead (show (0:ℝ) < y - x by linarith)]

/-- Under the mean condition `Nn < (Nn-m)·s` (with `s = e^{λµ} > 1`, `0 < m < Nn`), the point
`s` lies strictly left of the parabola vertex: `s·(2Nn-m) < Nn + (Nn-m)·s²`. -/
theorem vertex_cond (m Nn s : ℝ) (hm : 0 < m) (hmN : m < Nn) (hs1 : 1 < s)
    (hmean : Nn < (Nn - m) * s) :
    s * (2*Nn - m) < Nn + (Nn - m) * s^2 := by
  have hNm : 0 < Nn - m := by linarith
  -- (Nn-m)s² - (2Nn-m)s + Nn = (Nn-m)(s-1)(s - Nn/(Nn-m)); both factors > 0
  -- (Nn-m)(s-1) > 0 ; (Nn-m)s - Nn > 0 from hmean
  nlinarith [mul_pos (mul_pos hNm (show (0:ℝ) < s - 1 by linarith)) (show (0:ℝ) < (Nn - m)*s - Nn by linarith)]

/-- **Siegel 2001, Thm 2.2 / §2.1.1 — the φ' single-turning-point step (failure-reversal regime).**
For the waiting-time log-density `G(t) = m·log(1-e^{-λt}) - (Nn-m)·λt` and the symmetrized
log-ratio `φ(t) = G(t) - G(2µ-t)`, under the *mean* condition `Nn < (Nn-m)·e^{λµ}`
(equivalently `e^{λµ} > Nn/(Nn-m)`, which is exactly the regime where `µ = E[T]` sits ABOVE
the threshold — the failure-reversed binomial), the derivative `φ'` is **positive then negative**:
there is a single interior maximum `a ∈ (0,µ)` with `φ'(t) > 0` for `t ∈ (0,a)` and `φ'(t) < 0`
for `t ∈ (a,µ)`.  This is the unimodality that drives Siegel's moustache argument in the
non-degenerate (binomial-median) case. -/
theorem phi_single_turning_point_aux
    (lam m Nn mu : ℝ)
    (hlam : 0 < lam) (hm : 0 < m) (hmN : m < Nn) (hmu : 0 < mu)
    (hmean : Nn < (Nn - m) * Real.exp (lam * mu)) :
    ∃ a ∈ Ioo (0:ℝ) mu,
      (∀ t ∈ Ioo (0:ℝ) a,
        HasDerivAt (fun y => Glog lam m Nn y - Glog lam m Nn (2*mu - y))
          (GlogD lam m Nn t + GlogD lam m Nn (2*mu - t)) t
        ∧ 0 < GlogD lam m Nn t + GlogD lam m Nn (2*mu - t))
      ∧ (∀ t ∈ Ioo a mu,
        HasDerivAt (fun y => Glog lam m Nn y - Glog lam m Nn (2*mu - y))
          (GlogD lam m Nn t + GlogD lam m Nn (2*mu - t)) t
        ∧ GlogD lam m Nn t + GlogD lam m Nn (2*mu - t) < 0) := by
  set s : ℝ := Real.exp (lam * mu) with hs_def
  have hspos : 0 < s := Real.exp_pos _
  have hs1 : 1 < s := by rw [hs_def, Real.one_lt_exp_iff]; positivity
  set A : ℝ := Real.exp (2*lam*mu) with hA_def
  have hAs2 : A = s^2 := by
    rw [hA_def, hs_def, sq, ← Real.exp_add]; ring_nf
  have hlead : 0 < 2*Nn - m := by linarith
  have hNm : 0 < Nn - m := by linarith
  -- ψ(t) = Qp(e^{λt})
  set ψ : ℝ → ℝ := fun t => Qp m Nn A (Real.exp (lam*t)) with hψ_def
  -- e^{λ·} maps [0,µ] into [1,s] and is strictly mono
  have hexp_mono : StrictMonoOn (fun t => Real.exp (lam*t)) (Icc 0 mu) := by
    intro x _ y _ hxy
    exact Real.exp_lt_exp.mpr (by nlinarith)
  have hexp_mem : ∀ t ∈ Icc (0:ℝ) mu, Real.exp (lam*t) ∈ Icc (1:ℝ) s := by
    intro t ht
    simp only [Set.mem_Icc] at ht ⊢
    constructor
    · rw [← Real.exp_zero]; exact Real.exp_le_exp.mpr (by nlinarith [ht.1])
    · rw [hs_def]; exact Real.exp_le_exp.mpr (by nlinarith [ht.2])
  -- Qp strictly anti on [1,s]
  have hvert : s * (2*Nn - m) < Nn + (Nn - m)*A := by
    rw [hAs2]; exact vertex_cond m Nn s hm hmN hs1 hmean
  have hQanti := Qp_strictAnti m Nn A s hs1 hAs2 hlead hvert
  -- ψ strictly anti on [0,µ]
  have hψanti : StrictAntiOn ψ (Icc 0 mu) := by
    intro x hx y hy hxy
    have hex := hexp_mem x hx
    have hey := hexp_mem y hy
    have : Real.exp (lam*x) < Real.exp (lam*y) := hexp_mono hx hy hxy
    exact hQanti hex hey this
  -- ψ continuous
  have hψcont : ContinuousOn ψ (Icc 0 mu) := by
    have : Continuous ψ := by
      rw [hψ_def]
      have hQc : Continuous (Qp m Nn A) := by unfold Qp; fun_prop
      exact hQc.comp (by fun_prop)
    exact this.continuousOn
  -- ψ(0) = Qp(1) > 0 ; ψ(µ) = Qp(s) < 0
  have hψ0 : 0 < ψ 0 := by
    have : ψ 0 = m * (A - 1) := by
      rw [hψ_def]; simp only [mul_zero, Real.exp_zero]; exact Qp_at_one m Nn A
    rw [this]
    have hA1 : 1 < A := by rw [hAs2]; nlinarith [hs1]
    have : 0 < A - 1 := by linarith
    exact mul_pos hm this
  have hψμ : ψ mu < 0 := by
    have hval : ψ mu = -2 * s * (s - 1) * ((Nn - m)*s - Nn) := by
      show Qp m Nn A (Real.exp (lam*mu)) = _
      rw [← hs_def, hAs2]; exact Qp_at_sqrtA m Nn s
    rw [hval]
    have h1 : 0 < 2 * s * (s - 1) := by nlinarith [hspos, hs1]
    have h2 : 0 < (Nn - m)*s - Nn := by linarith [hmean]
    nlinarith [h1, h2]
  -- IVT: ∃ a ∈ (0,µ), ψ a = 0
  have hμpos : (0:ℝ) ≤ mu := hmu.le
  obtain ⟨a, ha_mem, ha_zero⟩ : ∃ a ∈ Ioo (0:ℝ) mu, ψ a = 0 := by
    have hcont' : ContinuousOn ψ (Icc 0 mu) := hψcont
    have hsign : (0:ℝ) ∈ Ioo (ψ mu) (ψ 0) := ⟨hψμ, hψ0⟩
    obtain ⟨a, ha, hva⟩ := intermediate_value_Ioo' hμpos hcont' hsign
    exact ⟨a, ha, hva⟩
  obtain ⟨ha0, haμ⟩ := ha_mem
  refine ⟨a, ⟨ha0, haμ⟩, ?_, ?_⟩
  · -- t ∈ (0,a): ψ t > ψ a = 0
    intro t ht
    obtain ⟨ht0, hta⟩ := ht
    have htμ : t < mu := lt_trans hta haμ
    have hψt_pos : 0 < ψ t := by
      have := hψanti (Set.mem_Icc.mpr ⟨ht0.le, htμ.le⟩) (Set.mem_Icc.mpr ⟨ha0.le, haμ.le⟩) hta
      rw [ha_zero] at this; linarith
    refine ⟨phi_hasDeriv lam m Nn mu t ht0 htμ hlam, ?_⟩
    -- φ'(t) = prefactor · ψ t, prefactor > 0
    rw [phiD_eq lam m Nn mu t ht0 htμ hlam]
    have hpre : 0 < lam / ((Real.exp (lam*t) - 1) * (Real.exp (lam*(2*mu-t)) - 1) * Real.exp (lam*t)) := by
      apply div_pos hlam
      have h1 : 0 < Real.exp (lam*t) - 1 := by
        have : 1 < Real.exp (lam*t) := by rw [Real.one_lt_exp_iff]; positivity
        linarith
      have h2 : 0 < Real.exp (lam*(2*mu-t)) - 1 := by
        have : 1 < Real.exp (lam*(2*mu-t)) := by rw [Real.one_lt_exp_iff]; nlinarith
        linarith
      positivity
    have hψeq : ((2*Nn - m) * (Real.exp (lam*t))^2
           - 2*(Nn + (Nn - m)*Real.exp (2*lam*mu)) * Real.exp (lam*t)
           + Real.exp (2*lam*mu) * (2*Nn - m)) = ψ t := by
      rw [hψ_def]; unfold Qp; rw [hA_def]
    rw [hψeq]; exact mul_pos hpre hψt_pos
  · -- t ∈ (a,µ): ψ t < ψ a = 0
    intro t ht
    obtain ⟨hat, htμ⟩ := ht
    have ht0 : 0 < t := lt_trans ha0 hat
    have hψt_neg : ψ t < 0 := by
      have := hψanti (Set.mem_Icc.mpr ⟨ha0.le, haμ.le⟩) (Set.mem_Icc.mpr ⟨ht0.le, htμ.le⟩) hat
      rw [ha_zero] at this; linarith
    refine ⟨phi_hasDeriv lam m Nn mu t ht0 htμ hlam, ?_⟩
    rw [phiD_eq lam m Nn mu t ht0 htμ hlam]
    have hpre : 0 < lam / ((Real.exp (lam*t) - 1) * (Real.exp (lam*(2*mu-t)) - 1) * Real.exp (lam*t)) := by
      apply div_pos hlam
      have h1 : 0 < Real.exp (lam*t) - 1 := by
        have : 1 < Real.exp (lam*t) := by rw [Real.one_lt_exp_iff]; positivity
        linarith
      have h2 : 0 < Real.exp (lam*(2*mu-t)) - 1 := by
        have : 1 < Real.exp (lam*(2*mu-t)) := by rw [Real.one_lt_exp_iff]; nlinarith
        linarith
      positivity
    have hψeq : ((2*Nn - m) * (Real.exp (lam*t))^2
           - 2*(Nn + (Nn - m)*Real.exp (2*lam*mu)) * Real.exp (lam*t)
           + Real.exp (2*lam*mu) * (2*Nn - m)) = ψ t := by
      rw [hψ_def]; unfold Qp; rw [hA_def]
    rw [hψeq]
    have := mul_neg_of_pos_of_neg hpre hψt_neg
    linarith [this]


theorem phi_single_turning_point (lam m Nn mu : ℝ) (hlam : 0 < lam) (hm : 0 < m) (hmN : m < Nn) (hmu : 0 < mu) (hmean : Nn < (Nn - m) * Real.exp (lam * mu)) : ∃ a ∈ Set.Ioo (0:ℝ) mu, (∀ t ∈ Set.Ioo (0:ℝ) a, HasDerivAt (fun y => (m * Real.log (1 - Real.exp (-lam * y)) - (Nn - m) * (lam * y)) - (m * Real.log (1 - Real.exp (-lam * (2*mu - y))) - (Nn - m) * (lam * (2*mu - y)))) (((m * (lam * Real.exp (-lam * t) / (1 - Real.exp (-lam * t))) - (Nn - m) * lam)) + ((m * (lam * Real.exp (-lam * (2*mu - t)) / (1 - Real.exp (-lam * (2*mu - t)))) - (Nn - m) * lam))) t ∧ 0 < (((m * (lam * Real.exp (-lam * t) / (1 - Real.exp (-lam * t))) - (Nn - m) * lam)) + ((m * (lam * Real.exp (-lam * (2*mu - t)) / (1 - Real.exp (-lam * (2*mu - t)))) - (Nn - m) * lam)))) ∧ (∀ t ∈ Set.Ioo a mu, HasDerivAt (fun y => (m * Real.log (1 - Real.exp (-lam * y)) - (Nn - m) * (lam * y)) - (m * Real.log (1 - Real.exp (-lam * (2*mu - y))) - (Nn - m) * (lam * (2*mu - y)))) (((m * (lam * Real.exp (-lam * t) / (1 - Real.exp (-lam * t))) - (Nn - m) * lam)) + ((m * (lam * Real.exp (-lam * (2*mu - t)) / (1 - Real.exp (-lam * (2*mu - t)))) - (Nn - m) * lam))) t ∧ (((m * (lam * Real.exp (-lam * t) / (1 - Real.exp (-lam * t))) - (Nn - m) * lam)) + ((m * (lam * Real.exp (-lam * (2*mu - t)) / (1 - Real.exp (-lam * (2*mu - t)))) - (Nn - m) * lam))) < 0) := by
  exact phi_single_turning_point_aux lam m Nn mu hlam hm hmN hmu hmean


end

/- Grace · https://prove2.me/theorems/af6cbf3e-e8ae-4a1d-ba24-f32286ce54fb · accepted submission e3d1c012-9dbf-4e98-9f36-c1169e930a61 -/

section


set_option autoImplicit false
open Set

theorem upstream_g_sign_strict
    (f φ' : ℝ → ℝ) (μ a t₀ : ℝ) (hμ : 0 < μ) (ha : a ∈ Set.Ioo (0:ℝ) μ)
    (hfpos : ∀ x ∈ Set.Ioo (0:ℝ) (2*μ), 0 < f x)
    (hφd : ∀ x ∈ Set.Ioo (0:ℝ) μ,
        HasDerivAt (fun y => Real.log (f y) - Real.log (f (2*μ - y))) (φ' x) x)
    (hφpos : ∀ x ∈ Set.Ioo (0:ℝ) a, 0 < φ' x)
    (hφneg : ∀ x ∈ Set.Ioo a μ, φ' x < 0)
    (hφcont : ContinuousOn (fun y => Real.log (f y) - Real.log (f (2*μ - y))) (Set.Ioc 0 μ))
    (ht₀ : t₀ ∈ Set.Ioo (0:ℝ) a) (hφt₀ : Real.log (f t₀) - Real.log (f (2*μ - t₀)) < 0)
    (hg0 : f 0 - f (2*μ) ≤ 0) :
    ∃ c ∈ Set.Ioo (0:ℝ) μ,
      (∀ x ∈ Set.Icc (0:ℝ) c, f x - f (2*μ - x) ≤ 0)
        ∧ (∀ x ∈ Set.Icc c μ, 0 ≤ f x - f (2*μ - x)) := by
  -- inline the two boundary-aware monotonicity facts (formerly platform axioms cb4f43dc/30ae0fd6),
  -- proved from Mathlib's interior-derivative monotonicity lemmas
  have smono : ∀ (g g' : ℝ → ℝ) (p q : ℝ),
      ContinuousOn g (Icc p q) →
      (∀ x ∈ Ioo p q, HasDerivAt g (g' x) x) →
      (∀ x ∈ Ioo p q, 0 < g' x) →
      StrictMonoOn g (Icc p q) := by
    intro g g' p q hcont hd hpos
    refine strictMonoOn_of_deriv_pos (convex_Icc p q) hcont ?_
    intro x hx
    rw [interior_Icc] at hx
    rw [(hd x hx).deriv]
    exact hpos x hx
  have santi : ∀ (g g' : ℝ → ℝ) (p q : ℝ),
      ContinuousOn g (Icc p q) →
      (∀ x ∈ Ioo p q, HasDerivAt g (g' x) x) →
      (∀ x ∈ Ioo p q, g' x < 0) →
      StrictAntiOn g (Icc p q) := by
    intro g g' p q hcont hd hneg
    refine strictAntiOn_of_deriv_neg (convex_Icc p q) hcont ?_
    intro x hx
    rw [interior_Icc] at hx
    rw [(hd x hx).deriv]
    exact hneg x hx
  set φ : ℝ → ℝ := fun y => Real.log (f y) - Real.log (f (2*μ - y)) with hφ_def
  obtain ⟨ha0, haμ⟩ := ha
  -- φ(μ) = 0  (since 2µ-µ = µ)
  have hφμ : φ μ = 0 := by simp only [hφ_def]; rw [show 2*μ - μ = μ by ring]; ring
  -- φ > 0 on (a,μ): φ strictly anti on [a,μ], φ(μ)=0 ⟹ φ(x) > φ(μ) = 0
  have hcont_aμ : ContinuousOn φ (Icc a μ) := by
    apply hφcont.mono; intro x hx; rw [mem_Icc] at hx; rw [mem_Ioc]; exact ⟨by linarith, hx.2⟩
  have hanti : StrictAntiOn φ (Icc a μ) :=
    santi φ φ' a μ hcont_aμ
      (fun x hx => hφd x ⟨by have := hx.1; linarith [ha0], hx.2⟩) hφneg
  have hφpos_aμ : ∀ x ∈ Ioo a μ, 0 < φ x := by
    intro x hx
    obtain ⟨hax, hxμ⟩ := hx
    have := hanti ⟨hax.le, hxμ.le⟩ ⟨haμ.le, le_refl μ⟩ hxμ
    rw [hφμ] at this; linarith
  -- φ strictly mono on [t₀, a]
  have hcont_t₀a : ContinuousOn φ (Icc t₀ a) := by
    apply hφcont.mono; intro x hx; rw [mem_Icc] at hx; rw [mem_Ioc]
    exact ⟨by linarith [ht₀.1], by linarith [haμ]⟩
  have hmono : StrictMonoOn φ (Icc t₀ a) :=
    smono φ φ' t₀ a hcont_t₀a
      (fun x hx => hφd x ⟨by linarith [ht₀.1, hx.1], by linarith [haμ, hx.2]⟩)
      (fun x hx => hφpos x ⟨by linarith [ht₀.1, hx.1], hx.2⟩)
  -- φ(a) > 0
  have hφa : 0 < φ a := by
    rcases eq_or_lt_of_le haμ.le with h | h
    · exact absurd h (ne_of_lt haμ)
    · have hmid : (a + μ)/2 ∈ Ioo a μ := ⟨by linarith, by linarith⟩
      have := hanti ⟨le_refl a, haμ.le⟩ ⟨by linarith [hmid.1], by linarith [hmid.2]⟩ hmid.1
      have hpos := hφpos_aμ _ hmid
      linarith
  -- crossing c ∈ (t₀, a): φ(t₀) < 0 < φ(a), IVT on [t₀,a]
  obtain ⟨c, hc_mem, hc_zero⟩ : ∃ c ∈ Ioo t₀ a, φ c = 0 := by
    have hsign : (0:ℝ) ∈ Ioo (φ t₀) (φ a) := ⟨hφt₀, hφa⟩
    obtain ⟨c, hc, hv⟩ := intermediate_value_Ioo ht₀.2.le hcont_t₀a hsign
    exact ⟨c, hc, hv⟩
  obtain ⟨ht₀c, hca⟩ := hc_mem
  have hc0 : 0 < c := lt_trans ht₀.1 ht₀c
  have hcμ : c < μ := lt_trans hca haμ
  refine ⟨c, ⟨hc0, hcμ⟩, ?_, ?_⟩
  · -- g ≤ 0 on [0,c]
    intro x hx
    rw [mem_Icc] at hx
    obtain ⟨hx0, hxc⟩ := hx
    rcases eq_or_lt_of_le hx0 with hxeq | hx0'
    · -- x = 0
      rw [← hxeq]; simpa using hg0
    · -- x ∈ (0,c]: φ(x) ≤ 0 ⟹ g(x) ≤ 0
      have hxμ : x < μ := lt_of_le_of_lt hxc hcμ
      have hfx : 0 < f x := hfpos x ⟨hx0', by linarith⟩
      have hf2 : 0 < f (2*μ - x) := hfpos (2*μ - x) ⟨by linarith, by linarith⟩
      have hφx_le : φ x ≤ 0 := by
        rcases lt_or_ge x t₀ with hxt | hxt
        · -- x < t₀: φ(x) < φ(t₀) < 0
          have hcont_xt : ContinuousOn φ (Icc x t₀) := by
            apply hφcont.mono; intro y hy; rw [mem_Icc] at hy; rw [mem_Ioc]
            exact ⟨by linarith, by linarith [ht₀.2, haμ]⟩
          have hmono_xt : StrictMonoOn φ (Icc x t₀) :=
            smono φ φ' x t₀ hcont_xt
              (fun y hy => hφd y ⟨by linarith [hy.1], by linarith [hy.2, ht₀.2, haμ]⟩)
              (fun y hy => hφpos y ⟨by linarith [hy.1], by linarith [hy.2, ht₀.2]⟩)
          have := hmono_xt ⟨le_refl x, hxt.le⟩ ⟨hxt.le, le_refl t₀⟩ hxt
          linarith [hφt₀]
        · -- t₀ ≤ x ≤ c: φ(x) ≤ φ(c) = 0
          have hxa : x ≤ a := le_of_lt (lt_of_le_of_lt hxc hca)
          rcases eq_or_lt_of_le hxc with hxceq | hxclt
          · rw [hxceq, hc_zero]
          · have hmono2 := hmono ⟨hxt, hxa⟩ ⟨ht₀c.le, hca.le⟩ hxclt
            rw [hc_zero] at hmono2; linarith
      have hle : f x ≤ f (2*μ - x) := (Real.log_le_log_iff hfx hf2).mp (by simpa [hφ_def] using hφx_le)
      linarith
  · -- g ≥ 0 on [c,μ]
    intro x hx
    rw [mem_Icc] at hx
    obtain ⟨hcx, hxμ⟩ := hx
    rcases eq_or_lt_of_le hxμ with hxeq | hxμ'
    · -- x = μ: g(μ) = f(μ)-f(μ) = 0
      rw [hxeq, show 2*μ - μ = μ by ring]; simp
    · have hx0 : 0 < x := lt_of_lt_of_le hc0 hcx
      have hfx : 0 < f x := hfpos x ⟨hx0, by linarith⟩
      have hf2 : 0 < f (2*μ - x) := hfpos (2*μ - x) ⟨by linarith, by linarith⟩
      have hφx_ge : 0 ≤ φ x := by
        rcases eq_or_lt_of_le hcx with hxceq | hcx'
        · rw [← hxceq, hc_zero]
        · rcases lt_or_ge a x with hxa | hxa
          · have := hφpos_aμ x ⟨hxa, hxμ'⟩; linarith
          · have hcont_ca : ContinuousOn φ (Icc c a) := by
              apply hφcont.mono; intro y hy; rw [mem_Icc] at hy; rw [mem_Ioc]
              exact ⟨by linarith, by linarith [haμ]⟩
            have hmono_ca : StrictMonoOn φ (Icc c a) :=
              smono φ φ' c a hcont_ca
                (fun y hy => hφd y ⟨by linarith [hc0, hy.1], by linarith [haμ, hy.2]⟩)
                (fun y hy => hφpos y ⟨by linarith [hc0, hy.1], hy.2⟩)
            have := hmono_ca ⟨le_refl c, hca.le⟩ ⟨hcx'.le, hxa⟩ hcx'
            rw [hc_zero] at this; linarith
      have hge : f (2*μ - x) ≤ f x := (Real.log_le_log_iff hf2 hfx).mp (by
        have : Real.log (f (2*μ-x)) - Real.log (f x) ≤ 0 := by simpa [hφ_def] using (by linarith [hφx_ge] : -(φ x) ≤ 0)
        linarith)
      linarith



end

/- Grace · https://prove2.me/theorems/f3a3a86f-bbb9-4385-b993-5e6ba9987f09 · accepted submission d8c10cfc-2bfc-43aa-8faa-23b929c25f6e -/

section


set_option autoImplicit false
open MeasureTheory Set Finset
open scoped BigOperators

-- per-term integrability (k < N so N-k ≥ 1); copied from SurvivalMean.lean
theorem term_integrable (N k : ℕ) (lam : ℝ) (hlam : 0 < lam) (hk : k < N) :
    IntegrableOn (fun t : ℝ => (Nat.choose N k : ℝ)
      * (1 - Real.exp (-(lam * t))) ^ k * (Real.exp (-(lam * t))) ^ (N - k)) (Ioi (0:ℝ)) := by
  set C : ℝ := |(Nat.choose N k : ℝ)| with hC
  have hgint : IntegrableOn (fun t : ℝ => C * Real.exp (-lam * t)) (Ioi (0:ℝ)) := by
    have := integrableOn_exp_mul_Ioi (a := -lam) (c := (0:ℝ)) (by linarith)
    exact this.const_mul C
  have hcont : Continuous (fun t : ℝ => (Nat.choose N k : ℝ)
      * (1 - Real.exp (-(lam * t))) ^ k * (Real.exp (-(lam * t))) ^ (N - k)) := by fun_prop
  refine Integrable.mono' hgint hcont.aestronglyMeasurable.restrict ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  rw [Set.mem_Ioi] at ht
  have he : (0:ℝ) < Real.exp (-(lam * t)) := Real.exp_pos _
  have he1 : Real.exp (-(lam * t)) ≤ 1 := by rw [Real.exp_le_one_iff]; nlinarith [ht, hlam]
  have hq0 : (0:ℝ) ≤ 1 - Real.exp (-(lam * t)) := by linarith
  have hq1 : 1 - Real.exp (-(lam * t)) ≤ 1 := by linarith [he.le]
  have hpm : (1 - Real.exp (-(lam * t))) ^ k ≤ 1 := pow_le_one₀ hq0 hq1
  have hNk : 1 ≤ N - k := by omega
  have hpe : (Real.exp (-(lam * t))) ^ (N - k) ≤ Real.exp (-(lam * t)) := by
    calc (Real.exp (-(lam * t))) ^ (N - k)
        ≤ (Real.exp (-(lam * t))) ^ 1 := pow_le_pow_of_le_one he.le he1 hNk
      _ = Real.exp (-(lam * t)) := by rw [pow_one]
  have hpe0 : (0:ℝ) ≤ (Real.exp (-(lam * t))) ^ (N - k) := pow_nonneg he.le _
  rw [Real.norm_eq_abs]
  have hrw : |(Nat.choose N k : ℝ) * (1 - Real.exp (-(lam * t))) ^ k
      * (Real.exp (-(lam * t))) ^ (N - k)|
      = C * ((1 - Real.exp (-(lam * t))) ^ k * (Real.exp (-(lam * t))) ^ (N - k)) := by
    rw [hC]
    rw [show (Nat.choose N k : ℝ) * (1 - Real.exp (-(lam * t))) ^ k * (Real.exp (-(lam * t))) ^ (N - k)
      = (Nat.choose N k : ℝ) * ((1 - Real.exp (-(lam * t))) ^ k * (Real.exp (-(lam * t))) ^ (N - k)) by ring]
    rw [abs_mul, abs_of_nonneg (a := (1 - Real.exp (-(lam * t))) ^ k * (Real.exp (-(lam * t))) ^ (N - k)) (by positivity)]
  rw [hrw, show C * Real.exp (-lam * t) = C * Real.exp (-(lam * t)) by ring]
  apply mul_le_mul_of_nonneg_left _ (by rw [hC]; exact abs_nonneg _)
  calc (1 - Real.exp (-(lam * t))) ^ k * (Real.exp (-(lam * t))) ^ (N - k)
      ≤ 1 * Real.exp (-(lam * t)) := mul_le_mul hpm hpe hpe0 (by norm_num)
    _ = Real.exp (-(lam * t)) := by ring

/-- The survival (lower partial sum, `k = 0..mp`) of the waiting-time model is integrable
on `(0,∞)`: a finite sum of exp-dominated integrable terms. -/
private theorem survival_integral_aux (N mp : ℕ) (lam : ℝ) (h : mp < N) (hlam : 0 < lam) :
    MeasureTheory.IntegrableOn
      (fun t => ∑ k ∈ Finset.range (mp+1),
        (Nat.choose N k : ℝ) * (1 - Real.exp (-(lam * t))) ^ k * (Real.exp (-(lam * t))) ^ (N - k))
      (Set.Ioi (0:ℝ)) := by
  apply MeasureTheory.integrable_finset_sum (Finset.range (mp+1))
  intro k hk
  rw [Finset.mem_range] at hk
  exact term_integrable N k lam hlam (by omega)



theorem waiting_time_survival_integrable (N mp : ℕ) (lam : ℝ) (h : mp < N) (hlam : 0 < lam) :
    MeasureTheory.IntegrableOn
      (fun t => ∑ k ∈ Finset.range (mp+1),
        (Nat.choose N k : ℝ) * (1 - Real.exp (-(lam * t))) ^ k * (Real.exp (-(lam * t))) ^ (N - k))
      (Set.Ioi (0:ℝ)) :=
  survival_integral_aux N mp lam h hlam


end

/- Grace · https://prove2.me/theorems/c6f05475-7190-415d-9d1e-e08f249f66ad · accepted submission 2d416fcb-0bea-466d-8d96-eb6834004d3e -/

section


set_option autoImplicit false
open scoped BigOperators
open Finset


-- per-term strict bound: log((j+2)/(j+1)) < 1/(j+1)
theorem hlg_term_gt (j : ℕ) :
    Real.log (((j:ℝ)+2) / (j+1)) < (1 : ℝ) / (j + 1) := by
  -- log(1 + 1/(j+1)) < 1/(j+1), via log_lt_sub_one_of_pos applied to x = (j+2)/(j+1) > 1
  have hjpos : (0:ℝ) < (j:ℝ)+1 := by positivity
  set x : ℝ := ((j:ℝ)+2)/((j:ℝ)+1) with hx_def
  have hxpos : 0 < x := by rw [hx_def]; positivity
  have hxne : x ≠ 1 := by
    rw [hx_def]
    have : (1:ℝ) < ((j:ℝ)+2)/((j:ℝ)+1) := by
      rw [lt_div_iff₀ hjpos]; linarith
    linarith
  have hkey := Real.log_lt_sub_one_of_pos hxpos hxne
  -- x - 1 = 1/(j+1)
  have hx1 : x - 1 = 1 / ((j:ℝ)+1) := by rw [hx_def]; field_simp; ring
  rw [hx1] at hkey
  exact hkey

/-- **Harmonic-tail lower bound (strict).** `∑_{j∈[a,b)} 1/(j+1) > log((b+1)/(a+1))` for `a < b`.
This is the lower companion of `harmonic_tail_lt_log`; per-term `log((j+2)/(j+1)) < 1/(j+1)`
(i.e. `log(1+x) < x`), telescoped. -/
theorem harmonic_tail_gt_log (a b : ℕ) (hab : a < b) :
    Real.log (((b:ℝ)+1) / (a+1)) < (∑ j ∈ Finset.Ico a b, (1 : ℝ) / (j + 1)) := by
  have htel : (∑ j ∈ Finset.Ico a b, Real.log (((j:ℝ)+2) / (j+1))) = Real.log (((b:ℝ)+1)/(a+1)) := by
    have hcongr : (∑ j ∈ Finset.Ico a b, Real.log (((j:ℝ)+2) / (j+1)))
        = ∑ j ∈ Finset.Ico a b, (Real.log ((j:ℝ)+2) - Real.log ((j:ℝ)+1)) := by
      apply Finset.sum_congr rfl
      intro j _
      rw [Real.log_div (by positivity) (by positivity)]
    rw [hcongr, Finset.sum_Ico_eq_sum_range]
    have hstep : (∑ i ∈ Finset.range (b - a), (Real.log (((a+i:ℕ):ℝ)+2) - Real.log (((a+i:ℕ):ℝ)+1)))
        = ∑ i ∈ Finset.range (b - a),
            ((fun k => Real.log (((a+k:ℕ):ℝ)+1)) (i+1) - (fun k => Real.log (((a+k:ℕ):ℝ)+1)) i) := by
      apply Finset.sum_congr rfl
      intro i _
      simp only []
      have : ((a + (i+1) : ℕ) : ℝ) + 1 = ((a+i:ℕ):ℝ) + 2 := by push_cast; ring
      rw [this]
    rw [hstep, Finset.sum_range_sub (fun k => Real.log (((a+k:ℕ):ℝ)+1)) (b-a)]
    have hba : a + (b - a) = b := by omega
    rw [show (a + (b-a) : ℕ) = b from hba, Nat.add_zero]
    rw [← Real.log_div (by positivity) (by positivity)]
  rw [← htel]
  apply Finset.sum_lt_sum_of_nonempty
  · rw [Finset.nonempty_Ico]; exact hab
  · intro j _
    exact hlg_term_gt j


end

/- Grace · https://prove2.me/theorems/2c35b285-563f-4f81-a9e3-4e59d4e8a058 · accepted submission 13fdddd0-3b78-425e-96cb-88567374d3d4 -/

section


set_option autoImplicit false
open scoped BigOperators
open Finset

namespace HarmLog

-- per-term strict bound: 1/(j+1) < log((j+1)/j)  for j ≥ 1
theorem term_lt (j : ℕ) (hj : 1 ≤ j) :
    (1 : ℝ) / (j + 1) < Real.log ((j+1) / j) := by
  have hjpos : (0:ℝ) < j := by exact_mod_cast hj
  -- use log(j/(j+1)) < j/(j+1) - 1
  have hx : (0:ℝ) < (j:ℝ) / (j+1) := by positivity
  have hxne : (j:ℝ) / (j+1) ≠ 1 := by
    have hd : (j:ℝ) / (j+1) < 1 := by
      rw [div_lt_one (by positivity)]; linarith
    linarith
  have hkey := Real.log_lt_sub_one_of_pos hx hxne
  -- log(j/(j+1)) = -log((j+1)/j)
  have hlog : Real.log ((j:ℝ) / (j+1)) = - Real.log (((j:ℝ)+1) / j) := by
    rw [← Real.log_inv]; congr 1
    rw [inv_div]
  rw [hlog] at hkey
  have hrhs : (j:ℝ) / (j+1) - 1 = - (1 / ((j:ℝ)+1)) := by
    field_simp; ring
  rw [hrhs] at hkey
  linarith

-- telescoping log:  ∑_{j=a}^{b-1} log((j+1)/j) = log(b/a)   ... here stated as the harmonic-vs-log bound
-- ∑_{j ∈ Ico a b} 1/(j+1) < log(b/a) for 1 ≤ a < b
theorem harmonic_tail_lt_log (a b : ℕ) (ha : 1 ≤ a) (hab : a < b) :
    (∑ j ∈ Finset.Ico a b, (1 : ℝ) / (j + 1)) < Real.log ((b:ℝ) / a) := by
  -- ∑ log((j+1)/j) telescopes to log(b/a)
  have htel : (∑ j ∈ Finset.Ico a b, Real.log (((j:ℝ)+1) / j)) = Real.log ((b:ℝ)/a) := by
    have hcongr : (∑ j ∈ Finset.Ico a b, Real.log (((j:ℝ)+1) / j))
        = ∑ j ∈ Finset.Ico a b, (Real.log ((j:ℝ)+1) - Real.log (j:ℝ)) := by
      apply Finset.sum_congr rfl
      intro j hj
      rw [Finset.mem_Ico] at hj
      have hj1 : 1 ≤ j := by omega
      have hjpos : (0:ℝ) < j := by exact_mod_cast hj1
      rw [Real.log_div (by positivity) (by positivity)]
    rw [hcongr]
    -- telescoping sum of f(j+1)-f(j) with f = log
    have := Finset.sum_Ico_eq_sub (fun j => Real.log (j:ℝ)) (le_of_lt hab)
    -- ∑_{Ico a b} (g(j+1)-g(j)) = g(b) - g(a)
    rw [Finset.sum_Ico_eq_sum_range]
    have hstep : (∑ i ∈ Finset.range (b - a), (Real.log (((a+i:ℕ):ℝ)+1) - Real.log ((a+i:ℕ):ℝ)))
        = ∑ i ∈ Finset.range (b - a),
            ((fun k => Real.log ((a+k:ℕ):ℝ)) (i+1) - (fun k => Real.log ((a+k:ℕ):ℝ)) i) := by
      apply Finset.sum_congr rfl
      intro i _
      simp only []
      have : ((a + (i+1) : ℕ) : ℝ) = ((a+i:ℕ):ℝ) + 1 := by push_cast; ring
      rw [this]
    rw [hstep, Finset.sum_range_sub (fun k => Real.log ((a+k:ℕ):ℝ)) (b-a)]
    have hba : a + (b - a) = b := by omega
    have hb1 : (1:ℕ) ≤ b := by omega
    rw [show (a + (b-a) : ℕ) = b from hba, Nat.add_zero]
    have hbR : (0:ℝ) < b := by exact_mod_cast (by omega : 0 < b)
    have haR : (0:ℝ) < a := by exact_mod_cast (by omega : 0 < a)
    rw [Real.log_div hbR.ne' haR.ne']
  rw [← htel]
  apply Finset.sum_lt_sum_of_nonempty
  · rw [Finset.nonempty_Ico]; exact hab
  · intro j hj
    rw [Finset.mem_Ico] at hj
    exact term_lt j (by omega)

end HarmLog

theorem harmonic_tail_lt_log (a b : ℕ) (ha : 1 ≤ a) (hab : a < b) :
    (∑ j ∈ Finset.Ico a b, (1 : ℝ) / (j + 1)) < Real.log ((b:ℝ) / a) :=
  HarmLog.harmonic_tail_lt_log a b ha hab


end

/- Grace · https://prove2.me/theorems/e7962502-97b1-4d56-80f6-b492518bd641 · accepted submission 88644383-8f9c-4fb6-a37f-a5c5b3194bb8 -/

section

-- The supporting lemmas used below appear earlier in this file.

set_option autoImplicit false
open scoped BigOperators
open Finset MeasureTheory Set Filter Topology

theorem Fcdf_at_one_ge_half (N m : ℕ) (h : m < N) (hm1 : 1 ≤ m) :
    (1/2 : ℝ) ≤ ∑ k ∈ Finset.Ico ((N-m-1)+1) (N+1),
      (Nat.choose N k : ℝ) * (1 - Real.exp (-(Real.log ((N:ℝ)/m) * 1))) ^ k
        * (Real.exp (-(Real.log ((N:ℝ)/m) * 1))) ^ (N - k) := by
  classical
  -- ===================================================================
  -- Local definitions (tactic `let`; refer to them by name, zeta-defeq)
  -- ===================================================================
  -- The CDF F.
  let Fcdf : ℕ → ℕ → ℝ → ℝ → ℝ := fun N mp lam s =>
    ∑ k ∈ Finset.Ico (mp+1) (N+1),
      (Nat.choose N k : ℝ) * (1 - Real.exp (-(lam * s))) ^ k * (Real.exp (-(lam * s))) ^ (N - k)
  -- The density f.
  let fdens : ℕ → ℕ → ℝ → ℝ → ℝ := fun N mp lam s =>
    (N : ℝ) * (Nat.choose (N-1) mp : ℝ) * (1 - Real.exp (-(lam * s))) ^ mp
        * (Real.exp (-(lam * s))) ^ (N - mp) * lam
  -- The waiting-time log-density derivative.
  let GlogD : ℝ → ℝ → ℝ → ℝ → ℝ := fun lam m Nn s =>
    m * (lam * Real.exp (-lam * s) / (1 - Real.exp (-lam * s))) - (Nn - m) * lam
  -- The log-density.
  let Glog : ℝ → ℝ → ℝ → ℝ → ℝ := fun lam m Nn t =>
    m * Real.log (1 - Real.exp (-lam * t)) - (Nn - m) * (lam * t)
  -- survSum
  let survSum : ℕ → ℕ → ℝ → ℝ → ℝ := fun N mp lam s =>
    ∑ k ∈ Finset.range (mp+1),
      (Nat.choose N k : ℝ) * (1 - Real.exp (-(lam * s))) ^ k * (Real.exp (-(lam * s))) ^ (N - k)
  -- ===================================================================
  -- Platform nodes bound to imported theorems (each defeq to the inlined form)
  -- ===================================================================
  have node_density : ∀ (N mp : ℕ) (lam : ℝ), mp < N → ∀ (t : ℝ),
      HasDerivAt (Fcdf N mp lam) (fdens N mp lam t) t :=
    fun N mp lam h t => Waiting.waiting_time_density N mp lam h t
  have node_F0 : ∀ (N mp : ℕ) (lam : ℝ), mp < N → Fcdf N mp lam 0 = 0 :=
    fun N mp lam h => waiting_time_cdf_at_zero N mp lam h
  have node_mass : ∀ (N mp : ℕ) (lam : ℝ), mp < N → 0 < lam →
      ∫ s in Set.Ioi (0:ℝ), fdens N mp lam s = 1 :=
    fun N mp lam h hlam => waiting_time_mass_eq_one N mp lam h hlam
  have node_fint : ∀ (N mp : ℕ) (lam : ℝ), mp < N → 0 < lam →
      MeasureTheory.IntegrableOn (fdens N mp lam) (Set.Ioi (0:ℝ)) :=
    fun N mp lam h hlam => waiting_time_density_integrable N mp lam h hlam
  have node_tfint : ∀ (N mp : ℕ) (lam : ℝ), mp < N → 0 < lam →
      MeasureTheory.IntegrableOn (fun t => t * fdens N mp lam t) (Set.Ioi (0:ℝ)) :=
    fun N mp lam h hlam => waiting_time_t_density_integrable N mp lam h hlam
  have node_decay : ∀ (N mp : ℕ) (lam : ℝ), mp < N → 0 < lam →
      Filter.Tendsto (fun t => t * (1 - Fcdf N mp lam t)) Filter.atTop (nhds 0) :=
    fun N mp lam h hlam => waiting_time_tail_decay N mp lam h hlam
  have node_ibp : ∀ (F f : ℝ → ℝ), (∀ x, HasDerivAt F (f x) x) →
      MeasureTheory.IntegrableOn (fun t => t * f t) (Set.Ioi (0:ℝ)) →
      MeasureTheory.IntegrableOn (fun t => 1 - F t) (Set.Ioi (0:ℝ)) →
      Filter.Tendsto (fun t => t * (1 - F t)) Filter.atTop (nhds 0) →
      ∫ t in Set.Ioi (0:ℝ), t * f t = ∫ t in Set.Ioi (0:ℝ), (1 - F t) :=
    fun F f hF hint_tf hint_surv hdecay => survival_mean_ibp F f hF hint_tf hint_surv hdecay
  have node_survmean : ∀ (N m : ℕ) (lam : ℝ), 0 < lam → m < N →
      ∫ t in Set.Ioi (0:ℝ), ∑ k ∈ Finset.range (m+1),
          (Nat.choose N k : ℝ) * (1 - Real.exp (-(lam * t))) ^ k * (Real.exp (-(lam * t))) ^ (N - k)
        = (1 / lam) * ∑ k ∈ Finset.range (m+1), (1 / ((N - k : ℕ) : ℝ)) :=
    fun N m lam hlam hm => waiting_time_survival_mean N m lam hlam hm
  have node_lemma21 : ∀ (μ : ℝ), 0 ≤ μ → ∀ (F f : ℝ → ℝ),
      (∀ x ∈ Set.Ici (0:ℝ), HasDerivAt F (f x) x) → (∀ x ∈ Set.Ici (0:ℝ), 0 ≤ f x) →
      F 0 = 0 → (∀ b : ℝ, IntervalIntegrable f MeasureTheory.volume 0 b) →
      MeasureTheory.IntegrableOn f (Set.Ioi (0:ℝ)) →
      MeasureTheory.IntegrableOn (fun t => t * f t) (Set.Ioi (0:ℝ)) →
      (∫ t in Set.Ioi (0:ℝ), f t = 1) → (∫ t in Set.Ioi (0:ℝ), t * f t = μ) →
      μ ≤ ∫ t in (0:ℝ)..(2*μ), F t :=
    fun μ hμ F f hF hfnn hF0 hf_int_loc hf_mass htf_mass hmass hmean =>
      siegel_cdf_average_ge_mean μ hμ F f hF hfnn hF0 hf_int_loc hf_mass htf_mass hmass hmean
  have node_bridge : ∀ (F f : ℝ → ℝ) (μ c : ℝ), (∀ x, HasDerivAt F (f x) x) →
      (∀ x ∈ Set.Icc (0:ℝ) c, f x - f (2 * μ - x) ≤ 0) →
      (∀ x ∈ Set.Icc c μ, 0 ≤ f x - f (2 * μ - x)) →
      AntitoneOn (fun x => (F x + F (2 * μ - x)) / 2) (Set.Icc 0 c)
        ∧ MonotoneOn (fun x => (F x + F (2 * μ - x)) / 2) (Set.Icc c μ) :=
    fun F f μ c hF hgL hgR =>
      siegel_symmetrized_cdf_unimodal_from_density_sign F f μ c hF hgL hgR
  have node_moustache_mass : ∀ (G : ℝ → ℝ) (μ c : ℝ), 0 < μ → 0 ≤ c → c < μ →
      AntitoneOn G (Set.Icc 0 c) → MonotoneOn G (Set.Icc c μ) →
      (∀ x, G (2 * μ - x) = G x) → G 0 ≤ (1/2 : ℝ) →
      IntervalIntegrable G MeasureTheory.volume 0 (2 * μ) →
      ((1 / 2 : ℝ) ≤ (1 / (2 * μ)) * ∫ x in (0:ℝ)..(2 * μ), G x) →
      (1 / 2 : ℝ) ≤ G μ :=
    fun G μ c hμ hc0 hcμ hleft hright hsym hG0 hint havg =>
      moustache_value_bound_mass G μ c hμ hc0 hcμ hleft hright hsym hG0 hint havg
  have node_phi_turn : ∀ (lam m Nn mu : ℝ),
      0 < lam → 0 < m → m < Nn → 0 < mu → Nn < (Nn - m) * Real.exp (lam * mu) →
      ∃ a ∈ Ioo (0:ℝ) mu,
        (∀ t ∈ Ioo (0:ℝ) a,
          HasDerivAt (fun y => Glog lam m Nn y - Glog lam m Nn (2*mu - y))
            (GlogD lam m Nn t + GlogD lam m Nn (2*mu - t)) t
          ∧ 0 < GlogD lam m Nn t + GlogD lam m Nn (2*mu - t))
        ∧ (∀ t ∈ Ioo a mu,
          HasDerivAt (fun y => Glog lam m Nn y - Glog lam m Nn (2*mu - y))
            (GlogD lam m Nn t + GlogD lam m Nn (2*mu - t)) t
          ∧ GlogD lam m Nn t + GlogD lam m Nn (2*mu - t) < 0) :=
    fun lam m Nn mu hlam hm hmN hmu hmean =>
      phi_single_turning_point lam m Nn mu hlam hm hmN hmu hmean
  have node_upstream_g_sign_strict : ∀ (f φ' : ℝ → ℝ) (μ a t₀ : ℝ), 0 < μ → a ∈ Ioo (0:ℝ) μ →
      (∀ x ∈ Ioo (0:ℝ) (2*μ), 0 < f x) →
      (∀ x ∈ Ioo (0:ℝ) μ,
          HasDerivAt (fun y => Real.log (f y) - Real.log (f (2*μ - y))) (φ' x) x) →
      (∀ x ∈ Ioo (0:ℝ) a, 0 < φ' x) →
      (∀ x ∈ Ioo a μ, φ' x < 0) →
      ContinuousOn (fun y => Real.log (f y) - Real.log (f (2*μ - y))) (Ioc 0 μ) →
      t₀ ∈ Ioo (0:ℝ) a → Real.log (f t₀) - Real.log (f (2*μ - t₀)) < 0 →
      f 0 - f (2*μ) ≤ 0 →
      ∃ c ∈ Ioo (0:ℝ) μ,
        (∀ x ∈ Icc (0:ℝ) c, f x - f (2*μ - x) ≤ 0)
          ∧ (∀ x ∈ Icc c μ, 0 ≤ f x - f (2*μ - x)) :=
    fun f φ' μ a t₀ hμ ha hfpos hφd hφpos hφneg hφcont ht₀ hφt₀ hg0 =>
      upstream_g_sign_strict f φ' μ a t₀ hμ ha hfpos hφd hφpos hφneg hφcont ht₀ hφt₀ hg0
  have node_survSum_int : ∀ (N mp : ℕ) (lam : ℝ), mp < N → 0 < lam →
      MeasureTheory.IntegrableOn
        (fun t => ∑ k ∈ Finset.range (mp+1),
          (Nat.choose N k : ℝ) * (1 - Real.exp (-(lam * t))) ^ k * (Real.exp (-(lam * t))) ^ (N - k))
        (Set.Ioi (0:ℝ)) :=
    fun N mp lam h hlam => waiting_time_survival_integrable N mp lam h hlam
  have node_harm_gt : ∀ (a b : ℕ), a < b →
      Real.log (((b:ℝ)+1) / (a+1)) < (∑ j ∈ Finset.Ico a b, (1 : ℝ) / (j + 1)) :=
    fun a b hab => harmonic_tail_gt_log a b hab
  have node_harm_lt : ∀ (a b : ℕ), 1 ≤ a → a < b →
      (∑ j ∈ Finset.Ico a b, (1 : ℝ) / (j + 1)) < Real.log ((b:ℝ) / a) :=
    fun a b ha hab => harmonic_tail_lt_log a b ha hab
  -- ===================================================================
  -- Reused helper lemmas
  -- ===================================================================
  have fdens_nonneg : ∀ (N mp : ℕ) (lam : ℝ), 0 < lam → ∀ (s : ℝ), 0 < s →
      0 ≤ fdens N mp lam s := by
    intro N mp lam hlam s hs
    show 0 ≤ (N : ℝ) * (Nat.choose (N-1) mp : ℝ) * (1 - Real.exp (-(lam * s))) ^ mp
        * (Real.exp (-(lam * s))) ^ (N - mp) * lam
    have he : (0:ℝ) < Real.exp (-(lam * s)) := Real.exp_pos _
    have he1 : Real.exp (-(lam * s)) ≤ 1 := by
      apply Real.exp_le_one_iff.mpr
      have : 0 < lam * s := mul_pos hlam hs
      linarith
    have h1 : (0:ℝ) ≤ 1 - Real.exp (-(lam * s)) := by linarith
    positivity
  have Fcdf_eq_intervalIntegral : ∀ (N mp : ℕ) (lam : ℝ), mp < N → ∀ (s : ℝ),
      Fcdf N mp lam s = ∫ x in (0:ℝ)..s, fdens N mp lam x := by
    intro N mp lam h s
    have hderiv : ∀ x ∈ Set.uIcc (0:ℝ) s, HasDerivAt (Fcdf N mp lam) (fdens N mp lam x) x := by
      intro x _; exact node_density N mp lam h x
    have hcont : IntervalIntegrable (fdens N mp lam) volume 0 s := by
      apply ContinuousOn.intervalIntegrable
      have : Continuous (fdens N mp lam) := by
        show Continuous (fun s => (N : ℝ) * (Nat.choose (N-1) mp : ℝ)
          * (1 - Real.exp (-(lam * s))) ^ mp
          * (Real.exp (-(lam * s))) ^ (N - mp) * lam)
        fun_prop
      exact this.continuousOn
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hcont, node_F0 N mp lam h, sub_zero]
  have Fcdf_le_one : ∀ (N mp : ℕ) (lam : ℝ), mp < N → 0 < lam → ∀ (s : ℝ), 0 ≤ s →
      Fcdf N mp lam s ≤ 1 := by
    intro N mp lam h hlam s hs
    rw [Fcdf_eq_intervalIntegral N mp lam h]
    rw [intervalIntegral.integral_of_le hs]
    have hmono : (∫ x in Set.Ioc (0:ℝ) s, fdens N mp lam x)
        ≤ ∫ x in Set.Ioi (0:ℝ), fdens N mp lam x := by
      apply setIntegral_mono_set (node_fint N mp lam h hlam)
      · filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
        exact fdens_nonneg N mp lam hlam x hx
      · filter_upwards with x
        intro hx
        exact hx.1
    rw [node_mass N mp lam h hlam] at hmono
    exact hmono
  have Fcdf_nonneg : ∀ (N mp : ℕ) (lam : ℝ), mp < N → 0 < lam → ∀ (s : ℝ), 0 ≤ s →
      0 ≤ Fcdf N mp lam s := by
    intro N mp lam h hlam s hs
    rw [Fcdf_eq_intervalIntegral N mp lam h]
    rw [intervalIntegral.integral_of_le hs]
    apply setIntegral_nonneg measurableSet_Ioc
    intro x hx
    exact fdens_nonneg N mp lam hlam x hx.1
  have Fcdf_mono_on : ∀ (N mp : ℕ) (lam : ℝ), 0 < lam → mp < N → ∀ (a b : ℝ), 0 < a →
      MonotoneOn (Fcdf N mp lam) (Icc a b) := by
    intro N mp lam hlam h a b ha
    have hcont : Continuous (Fcdf N mp lam) :=
      continuous_iff_continuousAt.mpr (fun x => (node_density N mp lam h x).continuousAt)
    apply monotoneOn_of_deriv_nonneg (convex_Icc a b) hcont.continuousOn
      (fun x hx => (node_density N mp lam h x).differentiableAt.differentiableWithinAt)
    intro x hx
    rw [interior_Icc] at hx
    rw [(node_density N mp lam h x).deriv]
    exact fdens_nonneg N mp lam hlam x (lt_trans ha hx.1)
  have full_sum_eq_one : ∀ (N : ℕ) (e : ℝ),
      (∑ k ∈ Finset.range (N+1),
          (Nat.choose N k : ℝ) * (1 - e) ^ k * e ^ (N - k)) = 1 := by
    intro N e
    have hb : ((1 - e) + e) ^ N = ∑ k ∈ Finset.range (N+1),
        (1 - e) ^ k * e ^ (N - k) * (Nat.choose N k : ℝ) := add_pow (1-e) e N
    have hcongr : (∑ k ∈ Finset.range (N+1), (Nat.choose N k : ℝ) * (1 - e) ^ k * e ^ (N - k))
        = ∑ k ∈ Finset.range (N+1), (1 - e) ^ k * e ^ (N - k) * (Nat.choose N k : ℝ) := by
      apply Finset.sum_congr rfl; intro k _; ring
    rw [hcongr, ← hb]
    norm_num
  have one_sub_Fcdf : ∀ (N mp : ℕ) (lam : ℝ), mp ≤ N → ∀ (s : ℝ),
      1 - Fcdf N mp lam s = survSum N mp lam s := by
    intro N mp lam h s
    show 1 - (∑ k ∈ Finset.Ico (mp+1) (N+1),
        (Nat.choose N k : ℝ) * (1 - Real.exp (-(lam * s))) ^ k * (Real.exp (-(lam * s))) ^ (N - k))
      = ∑ k ∈ Finset.range (mp+1),
        (Nat.choose N k : ℝ) * (1 - Real.exp (-(lam * s))) ^ k * (Real.exp (-(lam * s))) ^ (N - k)
    set e := Real.exp (-(lam * s)) with he
    have hfull := full_sum_eq_one N e
    have hsplit : Finset.range (N+1) = Finset.range (mp+1) ∪ Finset.Ico (mp+1) (N+1) := by
      rw [Finset.range_eq_Ico, Finset.range_eq_Ico,
        Finset.Ico_union_Ico_eq_Ico (by omega) (by omega)]
    have hdisj : Disjoint (Finset.range (mp+1)) (Finset.Ico (mp+1) (N+1)) := by
      rw [Finset.range_eq_Ico]; apply Finset.Ico_disjoint_Ico_consecutive
    rw [hsplit, Finset.sum_union hdisj] at hfull
    linarith [hfull]
  -- ===================================================================
  -- e^{-λ} = m/N when λ = log(N/m)
  -- ===================================================================
  have exp_neg_lam : ∀ (N m : ℕ), m < N → 1 ≤ m →
      Real.exp (-(Real.log ((N:ℝ)/m) * 1)) = (m:ℝ)/N := by
    intro N m h hm1
    have hmpos : (0:ℝ) < m := by exact_mod_cast hm1
    have hNnat : (0:ℕ) < N := by omega
    have hNpos : (0:ℝ) < N := by exact_mod_cast hNnat
    have hratio : (0:ℝ) < (N:ℝ)/m := by positivity
    rw [mul_one, ← Real.log_inv, Real.exp_log (by positivity)]
    rw [inv_div]
  have lam_pos : ∀ (N m : ℕ), m < N → 1 ≤ m → 0 < Real.log ((N:ℝ)/m) := by
    intro N m h hm1
    have hmpos : (0:ℝ) < m := by exact_mod_cast hm1
    have hNnat : (0:ℕ) < N := by omega
    have hNpos : (0:ℝ) < N := by exact_mod_cast hNnat
    rw [Real.log_pos_iff (by positivity)]
    rw [lt_div_iff₀ hmpos]
    have : (m:ℝ) < N := by exact_mod_cast h
    linarith
  -- ===================================================================
  -- φ-identity:  log fdens = Glog + log K  (for s>0)
  -- ===================================================================
  have log_fdens_eq : ∀ (N mp : ℕ) (lam s : ℝ), mp < N → 0 < lam → 0 < s →
      Real.log (fdens N mp lam s)
        = Glog lam (mp:ℝ) (N:ℝ) s
          + Real.log ((N:ℝ) * (Nat.choose (N-1) mp : ℝ) * lam) := by
    intro N mp lam s hmp hlam hs
    show Real.log ((N : ℝ) * (Nat.choose (N-1) mp : ℝ) * (1 - Real.exp (-(lam * s))) ^ mp
        * (Real.exp (-(lam * s))) ^ (N - mp) * lam)
      = ((mp:ℝ) * Real.log (1 - Real.exp (-lam * s)) - ((N:ℝ) - (mp:ℝ)) * (lam * s))
        + Real.log ((N:ℝ) * (Nat.choose (N-1) mp : ℝ) * lam)
    have he : (0:ℝ) < Real.exp (-(lam * s)) := Real.exp_pos _
    have he1 : Real.exp (-(lam * s)) < 1 := by
      rw [Real.exp_lt_one_iff]; have : 0 < lam * s := mul_pos hlam hs; linarith
    have hq : (0:ℝ) < 1 - Real.exp (-(lam * s)) := by linarith
    have hNnat : (0:ℕ) < N := by omega
    have hNpos : (0:ℝ) < N := by exact_mod_cast hNnat
    have hchoose : (0:ℝ) < (Nat.choose (N-1) mp : ℝ) := by
      have : 0 < Nat.choose (N-1) mp := Nat.choose_pos (by omega)
      exact_mod_cast this
    rw [Real.log_mul (by positivity) (ne_of_gt hlam)]
    rw [Real.log_mul (by positivity) (by positivity)]
    rw [Real.log_mul (by positivity) (by positivity)]
    rw [Real.log_pow, Real.log_pow]
    have hexparg : Real.exp (-(lam * s)) = Real.exp (-lam * s) := by rw [neg_mul]
    rw [Real.log_exp]
    have hcast : ((N - mp : ℕ) : ℝ) = (N:ℝ) - (mp:ℝ) := by rw [Nat.cast_sub (le_of_lt hmp)]
    rw [hcast]
    have harg : (1 - Real.exp (-(lam * s))) = (1 - Real.exp (-lam * s)) := by rw [hexparg]
    rw [harg]
    rw [Real.log_mul (by positivity) (ne_of_gt hlam)]
    ring
  have fdens_pos : ∀ (N mp : ℕ) (lam : ℝ), mp < N → 0 < lam → ∀ (s : ℝ), 0 < s →
      0 < fdens N mp lam s := by
    intro N mp lam hmp hlam s hs
    show 0 < (N : ℝ) * (Nat.choose (N-1) mp : ℝ) * (1 - Real.exp (-(lam * s))) ^ mp
        * (Real.exp (-(lam * s))) ^ (N - mp) * lam
    have he : (0:ℝ) < Real.exp (-(lam * s)) := Real.exp_pos _
    have he1 : Real.exp (-(lam * s)) < 1 := by
      rw [Real.exp_lt_one_iff]; have : 0 < lam * s := mul_pos hlam hs; linarith
    have hq : (0:ℝ) < 1 - Real.exp (-(lam * s)) := by linarith
    have hNnat : (0:ℕ) < N := by omega
    have hNpos : (0:ℝ) < N := by exact_mod_cast hNnat
    have hchoose : (0:ℝ) < (Nat.choose (N-1) mp : ℝ) := by
      have : 0 < Nat.choose (N-1) mp := Nat.choose_pos (by omega)
      exact_mod_cast this
    positivity
  have fdens_zero_at_zero : ∀ (N mp : ℕ) (lam : ℝ), 1 ≤ mp → fdens N mp lam 0 = 0 := by
    intro N mp lam hmp1
    show (N : ℝ) * (Nat.choose (N-1) mp : ℝ) * (1 - Real.exp (-(lam * 0))) ^ mp
        * (Real.exp (-(lam * 0))) ^ (N - mp) * lam = 0
    have h0 : (1 - Real.exp (-(lam * 0))) ^ mp = 0 := by
      have : (1 - Real.exp (-(lam * 0))) = 0 := by simp [Real.exp_zero]
      rw [this, zero_pow (by omega)]
    rw [h0]; ring
  -- ===================================================================
  -- CASE mp = 0 (m = N-1):  Fcdf N 0 lam 1 = 1 - (m/N)^N ≥ 1/2
  -- ===================================================================
  have Fcdf_mp0_at_one : ∀ (N : ℕ) (lam : ℝ), 1 ≤ N →
      Fcdf N 0 lam 1 = 1 - (Real.exp (-(lam * 1))) ^ N := by
    intro N lam hN
    have h0 : (0 : ℕ) < N := hN
    have hone := one_sub_Fcdf N 0 lam (by omega) 1
    have hsurv : survSum N 0 lam 1 = (Real.exp (-(lam * 1))) ^ N := by
      show (∑ k ∈ Finset.range (0+1),
          (Nat.choose N k : ℝ) * (1 - Real.exp (-(lam * 1))) ^ k
            * (Real.exp (-(lam * 1))) ^ (N - k)) = (Real.exp (-(lam * 1))) ^ N
      rw [Finset.sum_range_one]
      simp
    rw [hsurv] at hone
    linarith [hone]
  have edge_half : ∀ (N m : ℕ), m < N → 1 ≤ m → m = N - 1 →
      (1/2 : ℝ) ≤ Fcdf N (N-m-1) (Real.log ((N:ℝ)/m)) 1 := by
    intro N m h hm1 hmp0
    have hN1 : 1 ≤ N := le_of_lt (lt_of_le_of_lt hm1 h)
    have hmp : N - m - 1 = 0 := by omega
    rw [hmp]
    set lam := Real.log ((N:ℝ)/m) with hlam_def
    rw [Fcdf_mp0_at_one N lam hN1]
    rw [exp_neg_lam N m h hm1]
    have hmN : (m:ℝ) = (N:ℝ) - 1 := by
      have : m = N - 1 := hmp0
      rw [this]; push_cast [Nat.cast_sub hN1]; ring
    rw [hmN]
    have hNpos : (0:ℝ) < N := by exact_mod_cast hN1
    have hN1R : (1:ℝ) ≤ N := by exact_mod_cast hN1
    have hbase : ((N:ℝ)-1)/N = (-(1/N)) + 1 := by field_simp; ring
    have hle : ((N:ℝ)-1)/N ≤ Real.exp (-(1/N)) := by
      rw [hbase]; exact Real.add_one_le_exp _
    have hnn : (0:ℝ) ≤ ((N:ℝ)-1)/N := by apply div_nonneg _ hNpos.le; linarith
    have hpow : (((N:ℝ)-1)/N)^N ≤ (Real.exp (-(1/N)))^N := pow_le_pow_left₀ hnn hle N
    have hexp : (Real.exp (-(1/N)))^N = Real.exp (-1) := by
      rw [← Real.exp_nat_mul]; congr 1; field_simp
    rw [hexp] at hpow
    have h2 : Real.exp (-1) < (1/2 : ℝ) := by
      have hh := Real.exp_one_gt_d9
      rw [show (-1 : ℝ) = -(1:ℝ) from rfl, Real.exp_neg]
      rw [inv_lt_iff_one_lt_mul₀ (by positivity)]
      nlinarith [hh]
    linarith
  -- ===================================================================
  -- Reindex
  -- ===================================================================
  have reindex_harm : ∀ (N m : ℕ), m < N → 1 ≤ m →
      (∑ k ∈ Finset.range ((N-m-1)+1), (1 / ((N - k : ℕ) : ℝ)))
        = ∑ j ∈ Finset.Ico m N, (1 / ((j:ℝ) + 1)) := by
    intro N m h hm1
    apply Finset.sum_nbij' (fun k => N - 1 - k) (fun j => N - 1 - j)
    · intro k hk; rw [Finset.mem_range] at hk; rw [Finset.mem_Ico]; omega
    · intro j hj; rw [Finset.mem_Ico] at hj; rw [Finset.mem_range]; omega
    · intro k hk; rw [Finset.mem_range] at hk; omega
    · intro j hj; rw [Finset.mem_Ico] at hj; omega
    · intro k hk
      rw [Finset.mem_range] at hk
      have : N - k = (N - 1 - k) + 1 := by omega
      rw [this]
      push_cast [Nat.cast_sub (by omega : N - 1 - k ≤ N - 1 - k)]
      norm_num
  -- ===================================================================
  -- Glog has derivative GlogD; plus the difference deriv
  -- ===================================================================
  have Glog_hasDeriv : ∀ (lam m Nn : ℝ) (s : ℝ), 0 < s → 0 < lam →
      HasDerivAt (Glog lam m Nn) (GlogD lam m Nn s) s := by
    intro lam m Nn s hs hlam
    show HasDerivAt (fun t => m * Real.log (1 - Real.exp (-lam * t)) - (Nn - m) * (lam * t))
      (m * (lam * Real.exp (-lam * s) / (1 - Real.exp (-lam * s))) - (Nn - m) * lam) s
    have hexp : HasDerivAt (fun y => Real.exp (-lam * y)) (-lam * Real.exp (-lam * s)) s := by
      have := (((hasDerivAt_id s).const_mul (-lam)).exp); simpa [mul_comm] using this
    have hone : HasDerivAt (fun y => 1 - Real.exp (-lam * y)) (lam * Real.exp (-lam * s)) s := by
      have := hexp.const_sub 1; simpa using this
    have hposne : (1 : ℝ) - Real.exp (-lam * s) ≠ 0 := by
      have : Real.exp (-lam * s) < 1 := by rw [Real.exp_lt_one_iff]; nlinarith
      linarith
    have hlog : HasDerivAt (fun y => Real.log (1 - Real.exp (-lam * y)))
        ((lam * Real.exp (-lam * s)) / (1 - Real.exp (-lam * s))) s := hone.log hposne
    have hlin : HasDerivAt (fun y => (Nn - m) * (lam * y)) ((Nn - m) * lam) s := by
      have h2 := ((hasDerivAt_id s).const_mul lam).const_mul (Nn - m); simpa [mul_assoc] using h2
    have hd := (hlog.const_mul m).sub hlin
    exact hd
  have glog_diff_hasDeriv : ∀ (lam m Nn mu : ℝ) (t : ℝ), 0 < t → t < mu → 0 < lam →
      HasDerivAt (fun y => Glog lam m Nn y - Glog lam m Nn (2*mu - y))
        (GlogD lam m Nn t + GlogD lam m Nn (2*mu - t)) t := by
    intro lam m Nn mu t ht0 htmu hlam
    have hpt : (0:ℝ) < 2*mu - t := by linarith
    have h1 := Glog_hasDeriv lam m Nn t ht0 hlam
    have hinner : HasDerivAt (fun y => 2*mu - y) (-1 : ℝ) t := by
      have := (hasDerivAt_id t).const_sub (2*mu); simpa using this
    have h2 := Glog_hasDeriv lam m Nn (2*mu - t) hpt hlam
    have hcomp : HasDerivAt (fun y => Glog lam m Nn (2*mu - y)) (GlogD lam m Nn (2*mu - t) * (-1)) t :=
      h2.comp t hinner
    have hd := h1.sub hcomp
    exact hd.congr_deriv (by ring)
  -- ===================================================================
  -- MAIN CASE  1 ≤ m ≤ N-2  (so mp = N-m-1 ≥ 1)
  -- ===================================================================
  have main_half : ∀ (N m : ℕ), m < N → 1 ≤ m → m + 1 < N →
      (1/2 : ℝ) ≤ Fcdf N (N-m-1) (Real.log ((N:ℝ)/m)) 1 := by
    intro N m h hm1 hmN2
    set mp := N - m - 1 with hmp_def
    set lam := Real.log ((N:ℝ)/m) with hlam_def
    have hmp1 : 1 ≤ mp := by omega
    have hmpN : mp < N := by omega
    have hlam : 0 < lam := lam_pos N m h hm1
    set μ : ℝ := (1 / lam) * ∑ k ∈ Finset.range (mp+1), (1 / ((N - k : ℕ) : ℝ)) with hμ_def
    have hsum_pos : 0 < ∑ k ∈ Finset.range (mp+1), (1 / ((N - k : ℕ) : ℝ)) := by
      apply Finset.sum_pos
      · intro k hk
        rw [Finset.mem_range] at hk
        have : (0:ℕ) < N - k := by omega
        have : (0:ℝ) < ((N - k : ℕ):ℝ) := by exact_mod_cast this
        positivity
      · exact ⟨0, Finset.mem_range.mpr (by omega)⟩
    have hμpos : 0 < μ := by rw [hμ_def]; positivity
    have hlamμ : lam * μ = ∑ j ∈ Finset.Ico m N, (1 / ((j:ℝ) + 1)) := by
      rw [hμ_def]
      rw [← mul_assoc, mul_one_div, div_self (ne_of_gt hlam), one_mul]
      exact reindex_harm N m h hm1
    have hsurv_eq : ∀ t, (1 - Fcdf N mp lam t) = survSum N mp lam t :=
      fun t => one_sub_Fcdf N mp lam (le_of_lt hmpN) t
    have hsurvSum_int : MeasureTheory.IntegrableOn (survSum N mp lam) (Set.Ioi (0:ℝ)) :=
      node_survSum_int N mp lam hmpN hlam
    have hsurv_int : MeasureTheory.IntegrableOn (fun t => 1 - Fcdf N mp lam t) (Set.Ioi (0:ℝ)) := by
      apply hsurvSum_int.congr_fun _ measurableSet_Ioi
      intro t _; exact (hsurv_eq t).symm
    have hint_surv_val : (∫ t in Set.Ioi (0:ℝ), (1 - Fcdf N mp lam t)) = μ := by
      have hcong : (∫ t in Set.Ioi (0:ℝ), (1 - Fcdf N mp lam t))
          = ∫ t in Set.Ioi (0:ℝ), survSum N mp lam t := by
        apply MeasureTheory.setIntegral_congr_fun measurableSet_Ioi
        intro t _; exact hsurv_eq t
      rw [hcong]
      show (∫ t in Set.Ioi (0:ℝ), ∑ k ∈ Finset.range (mp+1),
          (Nat.choose N k : ℝ) * (1 - Real.exp (-(lam * t))) ^ k
            * (Real.exp (-(lam * t))) ^ (N - k)) = μ
      rw [node_survmean N mp lam hlam hmpN]
    have hmean : (∫ t in Set.Ioi (0:ℝ), t * fdens N mp lam t) = μ := by
      rw [node_ibp (Fcdf N mp lam) (fdens N mp lam)
          (fun x => node_density N mp lam hmpN x)
          (node_tfint N mp lam hmpN hlam) hsurv_int (node_decay N mp lam hmpN hlam)]
      exact hint_surv_val
    have hcont_fdens : Continuous (fdens N mp lam) := by
      show Continuous (fun s => (N : ℝ) * (Nat.choose (N-1) mp : ℝ)
        * (1 - Real.exp (-(lam * s))) ^ mp
        * (Real.exp (-(lam * s))) ^ (N - mp) * lam)
      fun_prop
    have hlemma21 : μ ≤ ∫ t in (0:ℝ)..(2*μ), Fcdf N mp lam t := by
      apply node_lemma21 μ (le_of_lt hμpos) (Fcdf N mp lam) (fdens N mp lam)
        (fun x _ => node_density N mp lam hmpN x)
        _ (node_F0 N mp lam hmpN)
        (fun b => (hcont_fdens.intervalIntegrable 0 b))
        (node_fint N mp lam hmpN hlam) (node_tfint N mp lam hmpN hlam)
        (node_mass N mp lam hmpN hlam) hmean
      intro x hx
      rw [Set.mem_Ici] at hx
      rcases eq_or_lt_of_le hx with hx0 | hx0
      · rw [← hx0]; rw [fdens_zero_at_zero N mp lam hmp1]
      · exact le_of_lt (fdens_pos N mp lam hmpN hlam x hx0)
    set Fhat : ℝ → ℝ := fun x => (Fcdf N mp lam x + Fcdf N mp lam (2*μ - x)) / 2 with hFhat_def
    have hFhatint : (∫ x in (0:ℝ)..(2*μ), Fhat x) = ∫ x in (0:ℝ)..(2*μ), Fcdf N mp lam x := by
      have hcont_F : Continuous (Fcdf N mp lam) :=
        continuous_iff_continuousAt.mpr (fun x => (node_density N mp lam hmpN x).continuousAt)
      have hI1 : IntervalIntegrable (Fcdf N mp lam) volume 0 (2*μ) :=
        hcont_F.intervalIntegrable 0 (2*μ)
      have hI2 : IntervalIntegrable (fun x => Fcdf N mp lam (2*μ - x)) volume 0 (2*μ) := by
        apply Continuous.intervalIntegrable; exact hcont_F.comp (by fun_prop)
      have hrefl : (∫ x in (0:ℝ)..(2*μ), Fcdf N mp lam (2*μ - x))
          = ∫ x in (0:ℝ)..(2*μ), Fcdf N mp lam x := by
        rw [intervalIntegral.integral_comp_sub_left (Fcdf N mp lam) (2*μ)]
        rw [show (2*μ - 0) = 2*μ by ring, show (2*μ - 2*μ) = (0:ℝ) by ring]
      calc (∫ x in (0:ℝ)..(2*μ), Fhat x)
          = ∫ x in (0:ℝ)..(2*μ), (Fcdf N mp lam x + Fcdf N mp lam (2*μ - x)) / 2 := rfl
        _ = (∫ x in (0:ℝ)..(2*μ), Fcdf N mp lam x + Fcdf N mp lam (2*μ - x)) / 2 := by
            rw [intervalIntegral.integral_div]
        _ = ((∫ x in (0:ℝ)..(2*μ), Fcdf N mp lam x) + ∫ x in (0:ℝ)..(2*μ), Fcdf N mp lam (2*μ - x)) / 2 := by
            rw [intervalIntegral.integral_add hI1 hI2]
        _ = ((∫ x in (0:ℝ)..(2*μ), Fcdf N mp lam x) + ∫ x in (0:ℝ)..(2*μ), Fcdf N mp lam x) / 2 := by
            rw [hrefl]
        _ = ∫ x in (0:ℝ)..(2*μ), Fcdf N mp lam x := by ring
    have h2μpos : (0:ℝ) < 2*μ := by positivity
    have havg : (1 / 2 : ℝ) ≤ (1 / (2 * μ)) * ∫ x in (0:ℝ)..(2 * μ), Fhat x := by
      rw [hFhatint]
      have hI : (1/(2*μ)) * (∫ x in (0:ℝ)..(2*μ), Fcdf N mp lam x)
          = (∫ x in (0:ℝ)..(2*μ), Fcdf N mp lam x) / (2*μ) := by ring
      rw [hI, le_div_iff₀ h2μpos]
      nlinarith [hlemma21]
    have hcast_mp : (N:ℝ) - (mp:ℝ) = (m:ℝ) + 1 := by
      have hmpnat : mp = N - m - 1 := hmp_def
      have : ((mp:ℕ):ℝ) = (N:ℝ) - (m:ℝ) - 1 := by
        rw [hmpnat]
        rw [Nat.cast_sub (by omega : 1 ≤ N - m), Nat.cast_sub (by omega : m ≤ N)]
        norm_num
      rw [this]; ring
    have hmpR_pos : (0:ℝ) < (mp:ℝ) := by exact_mod_cast hmp1
    have hmpR_lt : (mp:ℝ) < (N:ℝ) := by exact_mod_cast hmpN
    have hmpos_real : (0:ℝ) < (m:ℝ) := by exact_mod_cast hm1
    have hNnat0 : (0:ℕ) < N := by omega
    have hNpos_real : (0:ℝ) < (N:ℝ) := by exact_mod_cast hNnat0
    have hmean_turn : (N:ℝ) < ((N:ℝ) - (mp:ℝ)) * Real.exp (lam * μ) := by
      rw [hcast_mp]
      have hharm := node_harm_gt m N h
      rw [← hlamμ] at hharm
      have hexp_gt : ((N:ℝ)+1)/((m:ℝ)+1) < Real.exp (lam * μ) := by
        have := Real.exp_lt_exp.mpr hharm
        rwa [Real.exp_log (by positivity)] at this
      have hm1R : (0:ℝ) < (m:ℝ) + 1 := by positivity
      have hstep : (N:ℝ)+1 < ((m:ℝ)+1) * Real.exp (lam * μ) := by
        rw [div_lt_iff₀ hm1R] at hexp_gt; linarith [hexp_gt]
      linarith [hstep]
    set φlog : ℝ → ℝ := fun y => Real.log (fdens N mp lam y) - Real.log (fdens N mp lam (2*μ - y)) with hφlog_def
    set φGlog : ℝ → ℝ := fun y => Glog lam (mp:ℝ) (N:ℝ) y - Glog lam (mp:ℝ) (N:ℝ) (2*μ - y) with hφGlog_def
    set φ' : ℝ → ℝ := fun t => GlogD lam (mp:ℝ) (N:ℝ) t + GlogD lam (mp:ℝ) (N:ℝ) (2*μ - t) with hφ'_def
    have hidentity : Set.EqOn φlog φGlog (Ioo (0:ℝ) (2*μ)) := by
      intro y hy
      rw [Set.mem_Ioo] at hy
      have hy2 : 0 < 2*μ - y := by linarith [hy.2]
      rw [hφlog_def, hφGlog_def]
      simp only
      rw [log_fdens_eq N mp lam y hmpN hlam hy.1, log_fdens_eq N mp lam (2*μ - y) hmpN hlam hy2]
      ring
    obtain ⟨a, ha_mem, ha_pos_block, ha_neg_block⟩ :=
      node_phi_turn lam (mp:ℝ) (N:ℝ) μ hlam hmpR_pos hmpR_lt hμpos hmean_turn
    have hφd : ∀ x ∈ Ioo (0:ℝ) μ, HasDerivAt φlog (φ' x) x := by
      intro x hx
      have hglogderiv : HasDerivAt φGlog (φ' x) x := by
        rcases lt_trichotomy x a with hxa | hxa | hxa
        · exact (ha_pos_block x ⟨hx.1, hxa⟩).1
        · subst hxa
          exact glog_diff_hasDeriv lam (mp:ℝ) (N:ℝ) μ x hx.1 hx.2 hlam
        · exact (ha_neg_block x ⟨hxa, hx.2⟩).1
      apply hglogderiv.congr_of_eventuallyEq
      have hxmem : x ∈ Ioo (0:ℝ) (2*μ) := ⟨hx.1, by linarith [hx.2]⟩
      filter_upwards [isOpen_Ioo.mem_nhds hxmem] with y hy using (hidentity hy)
    have hfpos : ∀ x ∈ Ioo (0:ℝ) (2*μ), 0 < fdens N mp lam x := by
      intro x hx; exact fdens_pos N mp lam hmpN hlam x hx.1
    have hφpos : ∀ x ∈ Ioo (0:ℝ) a, 0 < φ' x := fun x hx => (ha_pos_block x hx).2
    have hφneg : ∀ x ∈ Ioo a μ, φ' x < 0 := fun x hx => (ha_neg_block x hx).2
    have hφcont : ContinuousOn φlog (Ioc 0 μ) := by
      rw [hφlog_def]
      apply ContinuousOn.sub
      · apply ContinuousOn.log
        · exact hcont_fdens.continuousOn
        · intro x hx; exact ne_of_gt (fdens_pos N mp lam hmpN hlam x hx.1)
      · apply ContinuousOn.log
        · have : Continuous (fun x => fdens N mp lam (2*μ - x)) := hcont_fdens.comp (by fun_prop)
          exact this.continuousOn
        · intro x hx
          rw [Set.mem_Ioc] at hx
          exact ne_of_gt (fdens_pos N mp lam hmpN hlam (2*μ - x) (by linarith [hx.2]))
    have hg0 : fdens N mp lam 0 - fdens N mp lam (2*μ) ≤ 0 := by
      rw [fdens_zero_at_zero N mp lam hmp1]
      have : 0 ≤ fdens N mp lam (2*μ) := le_of_lt (fdens_pos N mp lam hmpN hlam (2*μ) (by linarith))
      linarith
    obtain ⟨a0, aμ⟩ := ha_mem
    set v : ℝ := fdens N mp lam (2*μ) with hv_def
    have hvpos : 0 < v := fdens_pos N mp lam hmpN hlam (2*μ) (by linarith)
    have htend0 : Filter.Tendsto (fdens N mp lam) (𝓝[>] (0:ℝ)) (𝓝 (fdens N mp lam 0)) :=
      (hcont_fdens.continuousAt (x := (0:ℝ))).mono_left (nhdsWithin_le_nhds (s := Ioi (0:ℝ)))
    rw [fdens_zero_at_zero N mp lam hmp1] at htend0
    have htendR : Filter.Tendsto (fun t => fdens N mp lam (2*μ - t)) (𝓝[>] (0:ℝ)) (𝓝 v) := by
      have hc : Continuous (fun t => fdens N mp lam (2*μ - t)) := hcont_fdens.comp (by fun_prop)
      have hcat := hc.continuousAt (x := (0:ℝ))
      have htend : Filter.Tendsto (fun t => fdens N mp lam (2*μ - t)) (𝓝 (0:ℝ)) (𝓝 (fdens N mp lam (2*μ - 0))) := hcat
      have := htend.mono_left (nhdsWithin_le_nhds (s := Ioi (0:ℝ)))
      simpa [hv_def] using this
    have hev_lt : ∀ᶠ t in 𝓝[>] (0:ℝ), fdens N mp lam t < fdens N mp lam (2*μ - t) :=
      htend0.eventually_lt htendR (by linarith)
    have hev_lt_a : ∀ᶠ t in 𝓝[>] (0:ℝ), t < a := by
      apply eventually_nhdsWithin_of_eventually_nhds
      exact eventually_lt_nhds a0
    have hself : ∀ᶠ t in 𝓝[>] (0:ℝ), (0:ℝ) < t := by
      have : Ioi (0:ℝ) ∈ 𝓝[>] (0:ℝ) := self_mem_nhdsWithin
      filter_upwards [this] with t ht using ht
    obtain ⟨t₀, ⟨⟨ht₀lt, ht₀a⟩, ht₀pos'⟩⟩ :=
      ((hev_lt.and hev_lt_a).and hself).exists
    have ht₀_mem : t₀ ∈ Ioo (0:ℝ) a := ⟨ht₀pos', ht₀a⟩
    have ht₀μ : t₀ < μ := lt_trans ht₀a aμ
    have hφt₀ : Real.log (fdens N mp lam t₀) - Real.log (fdens N mp lam (2*μ - t₀)) < 0 := by
      have h1 : 0 < fdens N mp lam t₀ := fdens_pos N mp lam hmpN hlam t₀ ht₀pos'
      have h2 : 0 < fdens N mp lam (2*μ - t₀) := fdens_pos N mp lam hmpN hlam (2*μ - t₀) (by linarith)
      have hlog := Real.log_lt_log h1 ht₀lt
      linarith [hlog]
    obtain ⟨c, hc_mem, hgL, hgR⟩ :=
      node_upstream_g_sign_strict (fdens N mp lam) φ' μ a t₀ hμpos ⟨a0, aμ⟩
        hfpos hφd hφpos hφneg hφcont ht₀_mem hφt₀ hg0
    obtain ⟨hc0, hcμ⟩ := hc_mem
    obtain ⟨hAnti, hMono⟩ :=
      node_bridge (Fcdf N mp lam) (fdens N mp lam) μ c
        (fun x => node_density N mp lam hmpN x) hgL hgR
    have hsym : ∀ x, Fhat (2 * μ - x) = Fhat x := by
      intro x
      rw [hFhat_def]; simp only
      rw [show 2*μ - (2*μ - x) = x by ring]; ring
    have hFhatint_int : IntervalIntegrable Fhat volume 0 (2*μ) := by
      have hcont_F : Continuous (Fcdf N mp lam) :=
        continuous_iff_continuousAt.mpr (fun x => (node_density N mp lam hmpN x).continuousAt)
      have : Continuous Fhat := by
        rw [hFhat_def]
        exact (hcont_F.add (hcont_F.comp (by fun_prop))).div_const 2
      exact this.intervalIntegrable 0 (2*μ)
    have hFhat0 : Fhat 0 ≤ (1/2 : ℝ) := by
      rw [hFhat_def]; simp only
      rw [show 2*μ - 0 = 2*μ by ring, node_F0 N mp lam hmpN, zero_add]
      have : Fcdf N mp lam (2*μ) ≤ 1 := Fcdf_le_one N mp lam hmpN hlam (2*μ) (by linarith)
      linarith
    have hFhatμ : (1/2 : ℝ) ≤ Fhat μ :=
      node_moustache_mass Fhat μ c hμpos hc0.le hcμ hAnti hMono hsym hFhat0 hFhatint_int havg
    have hFhatμ_eq : Fhat μ = Fcdf N mp lam μ := by
      rw [hFhat_def]; simp only
      rw [show 2*μ - μ = μ by ring]; ring
    rw [hFhatμ_eq] at hFhatμ
    have hμlt1 : μ < 1 := by
      have hharm := node_harm_lt m N hm1 h
      rw [← hlamμ] at hharm
      have hlamlt : lam * μ < lam * 1 := by
        have : lam = Real.log ((N:ℝ)/m) := hlam_def
        rw [← this] at hharm; rw [mul_one]; exact hharm
      exact lt_of_mul_lt_mul_left hlamlt (le_of_lt hlam)
    have hmono_fcdf := Fcdf_mono_on N mp lam hlam hmpN μ 1 hμpos
    have hμ1 : Fcdf N mp lam μ ≤ Fcdf N mp lam 1 := by
      apply hmono_fcdf
      · exact ⟨le_refl μ, le_of_lt hμlt1⟩
      · exact ⟨le_of_lt hμlt1, le_refl 1⟩
      · exact le_of_lt hμlt1
    linarith [hFhatμ, hμ1]
  -- ===================================================================
  -- THE SOLUTION (reduction target)
  -- ===================================================================
  show (1/2 : ℝ) ≤ Fcdf N (N-m-1) (Real.log ((N:ℝ)/m)) 1
  rcases lt_or_ge (m+1) N with hcase | hcase
  · exact main_half N m h hm1 hcase
  · have hmp0 : m = N - 1 := by omega
    exact edge_half N m h hm1 hmp0


end

/- Grace · https://prove2.me/theorems/0d18c134-d7c7-4564-af5f-2d9d9757006e · accepted submission 2e571d71-d687-4049-a65a-cb336032400c -/

section


set_option autoImplicit false
open scoped BigOperators
open Finset

/-- **Binomial upper-tail reflection (k ↔ N-k).**  For `m ≤ N` and any `q`,
`∑_{k=N-m}^{N} C(N,k) q^k (1-q)^{N-k} = ∑_{j=0}^{m} C(N,j) (1-q)^j q^{N-j}`.
Substituting `j = N-k` turns the high tail of `Bin(N,q)` into the low tail of `Bin(N,1-q)`. -/
theorem binomial_tail_reflect (N m : ℕ) (hm : m ≤ N) (q : ℝ) :
    (∑ k ∈ Finset.Ico (N-m) (N+1),
        (Nat.choose N k : ℝ) * q ^ k * (1 - q) ^ (N - k))
      = ∑ j ∈ Finset.range (m+1),
        (Nat.choose N j : ℝ) * (1 - q) ^ j * q ^ (N - j) := by
  -- reindex k = N - j over j ∈ range (m+1); image is Ico (N-m) (N+1)
  rw [← Finset.sum_range_reflect (fun j =>
        (Nat.choose N j : ℝ) * (1 - q) ^ j * q ^ (N - j)) (m+1)]
  -- now LHS sum over Ico (N-m) (N+1), RHS sum over range (m+1) with j ↦ (m+1-1-j)=m-j
  apply Finset.sum_nbij' (fun k => k - (N - m)) (fun j => j + (N - m))
  · intro k hk; rw [Finset.mem_Ico] at hk; rw [Finset.mem_range]; omega
  · intro j hj; rw [Finset.mem_range] at hj; rw [Finset.mem_Ico]; omega
  · intro k hk; rw [Finset.mem_Ico] at hk; omega
  · intro j hj; rw [Finset.mem_range] at hj; omega
  · intro k hk
    rw [Finset.mem_Ico] at hk
    have hidx : m + 1 - 1 - (k - (N - m)) = N - k := by omega
    rw [hidx]
    have hcho : Nat.choose N (N - k) = Nat.choose N k := Nat.choose_symm (by omega)
    rw [hcho]
    have hNNk : N - (N - k) = k := by omega
    rw [hNNk]
    ring


end

/- Grace · https://prove2.me/theorems/abe294d5-9ca6-4db1-a26f-445bb1722ba8 · accepted submission a357e0bb-f6c4-4a40-9269-8df55c016bc0 -/

section


open MatrixCompletion
open scoped Classical BigOperators
open Finset

theorem binomial_full_sum_eq_one (N : ℕ) (p : ℝ) :
    ∑ k ∈ Finset.range (N + 1), binomialCardinalityProb N k p = 1 := by
  have hb := add_pow p (1 - p) N
  rw [add_sub_cancel, one_pow] at hb
  rw [hb]
  apply Finset.sum_congr rfl
  intro k hk
  simp only [binomialCardinalityProb]
  ring


end

/- Grace · https://prove2.me/theorems/37ec7785-09e7-44c2-b659-c95c10706450 · accepted submission 9fd66f4d-d259-4217-a479-95d15139df6d -/

section


set_option autoImplicit false
open scoped BigOperators
open Finset
open MatrixCompletion

theorem binomial_upper_tail_complement_reflect (N m : ℕ) (h : m ≤ N) (p : ℝ) :
    (∑ k ∈ Finset.Ico (N-m) (N+1), binomialCardinalityProb N k (1 - p))
      = 1 - ∑ k ∈ Finset.Ioo m (N + 1), binomialCardinalityProb N k p := by
  have hL : (∑ k ∈ Finset.Ico (N-m) (N+1), binomialCardinalityProb N k (1 - p))
      = ∑ k ∈ Finset.Ico (N-m) (N+1),
          (Nat.choose N k : ℝ) * (1-p) ^ k * (1 - (1-p)) ^ (N - k) := by
    apply Finset.sum_congr rfl; intro k _; rfl
  rw [hL]
  rw [binomial_tail_reflect N m h (1-p)]
  have hR : (∑ j ∈ Finset.range (m+1),
        (Nat.choose N j : ℝ) * (1 - (1-p)) ^ j * (1-p) ^ (N - j))
      = ∑ j ∈ Finset.range (m+1), binomialCardinalityProb N j p := by
    apply Finset.sum_congr rfl; intro j _; unfold binomialCardinalityProb; ring_nf
  rw [hR]
  have hsplit : Finset.range (N+1) = Finset.range (m+1) ∪ Finset.Ioo m (N+1) := by
    rw [Finset.range_eq_Ico, Finset.range_eq_Ico,
        show Finset.Ioo m (N+1) = Finset.Ico (m+1) (N+1) from by
          ext x; rw [Finset.mem_Ioo, Finset.mem_Ico]; omega,
        Finset.Ico_union_Ico_eq_Ico (by omega) (by omega)]
  have hdisj : Disjoint (Finset.range (m+1)) (Finset.Ioo m (N+1)) := by
    rw [Finset.disjoint_left]; intro x hx hx2
    rw [Finset.mem_range] at hx; rw [Finset.mem_Ioo] at hx2; omega
  have hfull := binomial_full_sum_eq_one N p
  rw [hsplit, Finset.sum_union hdisj] at hfull
  linarith [hfull]


end

/- Grace · https://prove2.me/theorems/f42e6e38-de73-45bb-8b28-b5b3c00fd38e · accepted submission 9db2c1e8-4bda-4940-9dd9-b687d04f2907 -/

section


set_option autoImplicit false
open scoped BigOperators
open Finset MatrixCompletion

theorem binomial_integer_mean_upper_tail_le_half (N m : ℕ) (h : m < N) :
    ∑ k ∈ Finset.Ioo m (N + 1), binomialCardinalityProb N k ((m : ℝ) / (N : ℝ)) ≤ (1 / 2 : ℝ) := by
  rcases Nat.eq_zero_or_pos m with hm0 | hmpos
  · -- m = 0 edge: B2LHS = 0
    subst hm0
    have hz : ∀ k ∈ Finset.Ioo 0 (N+1),
        binomialCardinalityProb N k (((0:ℕ) : ℝ) / (N:ℝ)) = 0 := by
      intro k hk
      rw [Finset.mem_Ioo] at hk
      unfold binomialCardinalityProb
      rw [Nat.cast_zero, zero_div, zero_pow (by omega : k ≠ 0)]
      ring
    rw [Finset.sum_congr rfl hz, Finset.sum_const_zero]; norm_num
  · -- 1 ≤ m
    have hm1 : 1 ≤ m := hmpos
    -- bridge at p = m/N
    have hbr := binomial_upper_tail_complement_reflect N m (le_of_lt h) ((m:ℝ)/(N:ℝ))
    -- Fcdf(1) ≥ 1/2
    have hge := Fcdf_at_one_ge_half N m h hm1
    -- Fcdf(1) = ∑_{Ico (N-m) (N+1)} bcp N k (1 - m/N)
    -- Fcdf(1) summand uses exp(-(log(N/m)*1)) = m/N
    have hexp : Real.exp (-(Real.log ((N:ℝ)/m) * 1)) = (m:ℝ)/(N:ℝ) := by
      have hNpos : (0:ℝ) < N := by
        have : (0:ℕ) < N := lt_of_lt_of_le hmpos (le_of_lt h)
        exact_mod_cast this
      have hmpos' : (0:ℝ) < m := by exact_mod_cast hm1
      rw [mul_one, ← Real.log_inv, Real.exp_log (by positivity)]
      rw [inv_div]
    -- index: (N-m-1)+1 = N-m
    have hidx : (N-m-1)+1 = N - m := by omega
    -- rewrite the Fcdf sum into the bridge LHS form
    have hFcdf_eq : (∑ k ∈ Finset.Ico ((N-m-1)+1) (N+1),
          (Nat.choose N k : ℝ) * (1 - Real.exp (-(Real.log ((N:ℝ)/m) * 1))) ^ k
            * (Real.exp (-(Real.log ((N:ℝ)/m) * 1))) ^ (N - k))
        = ∑ k ∈ Finset.Ico (N-m) (N+1), binomialCardinalityProb N k (1 - (m:ℝ)/(N:ℝ)) := by
      rw [hidx]
      apply Finset.sum_congr rfl
      intro k _
      unfold binomialCardinalityProb
      rw [hexp]
      rw [show (1:ℝ) - (1 - (m:ℝ)/(N:ℝ)) = (m:ℝ)/(N:ℝ) by ring]
    rw [hFcdf_eq] at hge
    rw [hbr] at hge
    linarith [hge]


end
end

-- Solutions.StratifyMarketsBernoulliExtremum
section
open Set
namespace StratifyMarkets.BernoulliExtremum

/-- A two-coordinate slice of a symmetric multiaffine polynomial. -/
def ExchangeableSlices {l : ℕ} (F : (Fin l → ℝ) → ℝ) : Prop :=
  ∀ p i j, i ≠ j → ∃ A B C : ℝ, ∀ u v : ℝ,
    F (Function.update (Function.update p i u) j v) = A + B*(u+v) + C*(u*v)

private def sqnorm {l : ℕ} (p : Fin l → ℝ) : ℝ := ∑ i, (p i)^2

private theorem update_sum {l : ℕ} (p : Fin l → ℝ) (i : Fin l) (u : ℝ) (f : ℝ → ℝ) :
    ∑ k, f (Function.update p i u k) = (∑ k, f (p k)) - f (p i) + f u := by
  classical
  rw [← Finset.sum_erase_add _ _ (Finset.mem_univ i),Function.update_self]
  have same := Finset.sum_congr (s₁ := Finset.univ.erase i) (s₂ := Finset.univ.erase i) rfl
    (fun k hk => congrArg f (Function.update_of_ne (Finset.ne_of_mem_erase hk) u p))
  rw [same,Finset.sum_erase_eq_sub (Finset.mem_univ i)]

/-- Every symmetric multiaffine objective has a fixed-mean maximizer whose
success probabilities take only the values zero, one, and one common interior
value. The tie-breaker maximizes a strictly convex sum of squares. -/
theorem extremal {l : ℕ} (F : (Fin l → ℝ) → ℝ) (cont : Continuous F)
    (poly : ExchangeableSlices F) (p₀ : Fin l → ℝ) (box : ∀ i, p₀ i ∈ Icc 0 1) :
    ∃ p : Fin l → ℝ, (∀ i, p i ∈ Icc 0 1) ∧ (∑ i, p i) = ∑ i, p₀ i ∧ F p₀ ≤ F p ∧
      ∀ i j, p i ∈ Ioo 0 1 → p j ∈ Ioo 0 1 → p i = p j := by
  classical
  let K := {p : Fin l → ℝ | (∀ i, p i ∈ Icc 0 1) ∧ (∑ i, p i) = ∑ i, p₀ i}
  have finiteSum : Continuous (fun p : Fin l → ℝ => ∑ i, p i) :=
    continuous_finsetSum _ fun i _ => continuous_apply i
  have comp : IsCompact K := (isCompact_pi_infinite (fun _ : Fin l => isCompact_Icc)).inter_right
    (isClosed_eq finiteSum continuous_const)
  have init : p₀ ∈ K := ⟨box,rfl⟩
  obtain ⟨best,bmem,maxF⟩ := comp.exists_isMaxOn ⟨p₀,init⟩ cont.continuousOn
  let M := K ∩ {p | F p = F best}
  have cm : IsCompact M := comp.inter_right (isClosed_eq cont continuous_const)
  have bc : best ∈ M := ⟨bmem,rfl⟩
  have cn : Continuous (sqnorm (l := l)) :=
    continuous_finsetSum _ fun i _ => (continuous_apply i).pow 2
  obtain ⟨p,pm,maxN⟩ := cm.exists_isMaxOn ⟨best,bc⟩ cn.continuousOn
  have pk : p ∈ K := pm.1
  have pe : F p = F best := pm.2
  refine ⟨p,pk.1,pk.2,(maxF init).trans_eq pe.symm,?_⟩
  intro i j hi hj
  by_contra neq
  have ij : i ≠ j := fun e => neq (e ▸ rfl)
  obtain ⟨A,B,C,form⟩ := poly p i j ij
  let upd (u v : ℝ) := Function.update (Function.update p i u) j v
  have base : F p = A + B*(p i+p j) + C*(p i*p j) := by simpa using form (p i) (p j)
  have admiss (u v : ℝ) (hu : u ∈ Icc 0 1) (hv : v ∈ Icc 0 1) (sum : u+v = p i+p j) :
      upd u v ∈ K := by
    refine ⟨?_,?_⟩
    · intro k
      by_cases h : k = j
      · simpa [upd,h] using hv
      · by_cases g : k = i
        · simpa [upd,h,g,ij] using hu
        · simpa [upd,h,g] using pk.1 k
    · change (∑ k, id (Function.update (Function.update p i u) j v k)) = _
      rw [update_sum,update_sum,Function.update_of_ne ij.symm]
      simp only [id_eq]
      linarith [pk.2]
  have move (u v : ℝ) (hu : u ∈ Icc 0 1) (hv : v ∈ Icc 0 1) (sum : u+v = p i+p j) :
      C*(u*v-p i*p j) ≤ 0 ∧ (C=0 → u^2+v^2 ≤ (p i)^2+(p j)^2) := by
    have ok := admiss u v hu hv sum
    have max := (maxF ok).trans_eq pe.symm
    change F (Function.update (Function.update p i u) j v) ≤ F p at max
    rw [form,base,sum] at max
    refine ⟨by nlinarith only [max],?_⟩
    intro z
    have eq : F (upd u v) = F best := by rw [← pe,base,show F (upd u v) = _ from form u v,sum,z]; ring
    have q := maxN (show upd u v ∈ M from ⟨ok,eq⟩)
    change (∑ k, (Function.update (Function.update p i u) j v k)^2) ≤ ∑ k, (p k)^2 at q
    rw [update_sum _ j v (fun x => x^2),update_sum _ i u (fun x => x^2),Function.update_of_ne ij.symm] at q
    linarith
  let mid := (p i+p j)/2
  have md : mid ∈ Icc 0 1 := ⟨by dsimp [mid]; linarith [hi.1,hj.1],by dsimp [mid]; linarith [hi.2,hj.2]⟩
  have sumM : mid+mid = p i+p j := by dsimp [mid]; ring
  have high := (move mid mid md md sumM).1
  have pos : 0 < mid*mid-p i*p j := by
    have sq : 0 < (p i-p j)^2 := sq_pos_of_ne_zero (sub_ne_zero.mpr neq)
    dsimp [mid]; nlinarith
  have coeff : C ≤ 0 := le_of_not_gt (fun c => (not_lt_of_ge high) (mul_pos c pos))
  have endpoint (u v : ℝ) (hu : u ∈ Icc 0 1) (hv : v ∈ Icc 0 1)
      (sum : u+v = p i+p j) (low : u*v < p i*p j) : False := by
    obtain ⟨first,second⟩ := move u v hu hv sum
    have z : C = 0 := le_antisymm coeff (le_of_not_gt (fun c => (not_lt_of_ge first) (mul_pos_of_neg_of_neg c (sub_neg.mpr low))))
    have ident := congrArg (fun x : ℝ => x^2) sum
    nlinarith [second z]
  by_cases small : p i+p j ≤ 1
  · exact endpoint 0 (p i+p j) ⟨le_rfl,zero_le_one⟩ ⟨add_nonneg hi.1.le hj.1.le,small⟩
      (zero_add _) (by simpa using mul_pos hi.1 hj.1)
  · have low : (p i+p j-1)*1 < p i*p j := by nlinarith [mul_pos (sub_pos.mpr hi.2) (sub_pos.mpr hj.2)]
    exact endpoint (p i+p j-1) 1 ⟨by linarith,by linarith [hi.2,hj.2]⟩ ⟨zero_le_one,le_rfl⟩
      (by ring) low

end StratifyMarkets.BernoulliExtremum
end

-- Solutions.StratifyMarketsBernoulliLaw
section
open Set
namespace StratifyMarkets.BernoulliExtremum

/-- Expected payoff of a sum of independent indicators. The boundary vector
selects which Bernoulli coordinates have yet to be averaged. -/
noncomputable def eval {l : ℕ} (p : Fin l → ℝ) (S : Finset (Fin l)) (f : ℕ → ℝ) : ℝ :=
  ∑ U ∈ S.powerset, f U.card * ∏ i ∈ S, if i ∈ U then p i else 1-p i

theorem eval_congr {l : ℕ} {p q : Fin l → ℝ} (S : Finset (Fin l)) (f : ℕ → ℝ)
    (eq : ∀ i ∈ S, p i = q i) : eval p S f = eval q S f := by
  unfold eval
  apply Finset.sum_congr rfl
  intro U _
  congr 1
  exact Finset.prod_congr rfl fun i hi => by rw [eq i hi]

theorem eval_continuous {l : ℕ} (S : Finset (Fin l)) (f : ℕ → ℝ) :
    Continuous (fun p : Fin l → ℝ => eval p S f) := by
  apply continuous_finsetSum
  intro U _
  apply continuous_const.mul
  apply continuous_finsetProd
  intro i _
  by_cases hi : i ∈ U
  · simp only [if_pos hi]; exact continuous_apply i
  · simp only [if_neg hi]; exact continuous_const.sub (continuous_apply i)

theorem eval_insert {l : ℕ} (p : Fin l → ℝ) {S : Finset (Fin l)} {i : Fin l}
    (hi : i ∉ S) (f : ℕ → ℝ) :
    eval p (insert i S) f = (1-p i)*eval p S f + p i*eval p S (fun k => f (k+1)) := by
  classical
  let g := fun (U : Finset (Fin l)) => f U.card * ∏ j ∈ insert i S, if j ∈ U then p j else 1-p j
  have dis : Disjoint S.powerset (Finset.image (insert i) S.powerset) := by
    apply Finset.disjoint_left.mpr
    intro U h1 h2
    obtain ⟨V,hV,eq⟩ := Finset.mem_image.mp h2
    exact hi ((Finset.mem_powerset.mp h1) (eq ▸ Finset.mem_insert_self i V))
  have inj : Set.InjOn (insert i) (↑S.powerset : Set (Finset (Fin l))) := by
    intro U hU V hV equal
    have ui : i ∉ U := fun h => hi ((Finset.mem_powerset.mp hU) h)
    have vi : i ∉ V := fun h => hi ((Finset.mem_powerset.mp hV) h)
    have h := congrArg (fun A : Finset (Fin l) => A.erase i) equal
    simpa [ui,vi] using h
  change (∑ U ∈ (insert i S).powerset, g U) = _
  rw [Finset.powerset_insert,Finset.sum_union dis,Finset.sum_image inj]
  unfold eval
  rw [Finset.mul_sum,Finset.mul_sum]
  apply congrArg₂ (·+·)
  · apply Finset.sum_congr rfl
    intro U hU
    have ui : i ∉ U := fun h => hi ((Finset.mem_powerset.mp hU) h)
    dsimp [g]
    rw [Finset.prod_insert hi,if_neg ui]
    ring
  · apply Finset.sum_congr rfl
    intro U hU
    have ui : i ∉ U := fun h => hi ((Finset.mem_powerset.mp hU) h)
    dsimp [g]
    rw [Finset.prod_insert hi,Finset.card_insert_of_notMem ui,if_pos (Finset.mem_insert_self _ _)]
    have same := Finset.prod_congr (s₁ := S) (s₂ := S) rfl (fun j hj =>
      show (if j ∈ insert i U then p j else 1-p j) = (if j ∈ U then p j else 1-p j) by
        have ne : j ≠ i := fun e => hi (e ▸ hj)
        simp [ne])
    rw [same]; ring

theorem eval_slices {l : ℕ} (f : ℕ → ℝ) : ExchangeableSlices (fun p : Fin l → ℝ => eval p Finset.univ f) := by
  classical
  intro p i j ij
  let S := (Finset.univ.erase i).erase j
  have hi : i ∉ S := fun h => (Finset.mem_erase.mp (Finset.mem_erase.mp h).2).1 rfl
  have hj : j ∉ S := Finset.notMem_erase _ _
  have hi' : i ∉ insert j S := by simp [ij,hi]
  have full : (Finset.univ : Finset (Fin l)) = insert i (insert j S) := by
    dsimp [S]
    rw [Finset.insert_erase (Finset.mem_erase.mpr ⟨ij.symm,Finset.mem_univ j⟩),Finset.insert_erase (Finset.mem_univ i)]
  let A := eval p S f
  let B := eval p S (fun k => f (k+1))
  let C := eval p S (fun k => f (k+1+1))
  refine ⟨A,B-A,C-2*B+A,?_⟩
  intro u v
  let q := Function.update (Function.update p i u) j v
  have same (g : ℕ → ℝ) : eval q S g = eval p S g := by
    apply eval_congr
    intro k hk
    obtain ⟨kj,hk'⟩ := Finset.mem_erase.mp hk
    have ki := (Finset.mem_erase.mp hk').1
    simp [q,kj,ki]
  change eval q Finset.univ f = _
  rw [full,eval_insert q hi',eval_insert q hj,eval_insert q hj]
  simp only [same,show q i = u by simp [q,ij],show q j = v by simp [q]]
  dsimp only [A,B,C]
  ring


theorem eval_constant {l : ℕ} {p : Fin l → ℝ} (S : Finset (Fin l)) {q : ℝ}
    (constant : ∀ i ∈ S, p i = q) (f : ℕ → ℝ) :
    eval p S f = ∑ k ∈ Finset.range (S.card+1),
      (S.card.choose k : ℝ) * q^k * (1-q)^(S.card-k) * f k := by
  classical
  unfold eval
  have factor {U : Finset (Fin l)} (h : U ⊆ S) :
      (∏ i ∈ S, if i ∈ U then p i else 1-p i) = q^U.card * (1-q)^(S.card-U.card) := by
    rw [← Finset.prod_sdiff h]
    have inU : (∏ i ∈ U, if i ∈ U then p i else 1-p i) = ∏ _i ∈ U, q := by
      apply Finset.prod_congr rfl
      intro i hi
      simp [hi,constant i (h hi)]
    have outU : (∏ i ∈ S \ U, if i ∈ U then p i else 1-p i) = ∏ _i ∈ S \ U, (1-q) := by
      apply Finset.prod_congr rfl
      intro i hi
      obtain ⟨hs,hn⟩ := Finset.mem_sdiff.mp hi
      simp [hn,constant i hs]
    rw [inU,outU,Finset.prod_const,Finset.prod_const,Finset.card_sdiff_of_subset h,mul_comm]
  have all := Finset.sum_congr (s₁ := S.powerset) (s₂ := S.powerset) rfl
    (fun U h => congrArg (fun x => f U.card * x) (factor (Finset.mem_powerset.mp h)))
  rw [all,Finset.sum_powerset_apply_card (fun k => f k * (q^k*(1-q)^(S.card-k)))]
  apply Finset.sum_congr rfl
  intro k _
  rw [nsmul_eq_mul]; ring

/-- Indicators equal to zero or one can be removed before applying the
common-probability binomial formula to the remaining coordinates. -/
theorem strip_deterministic {l : ℕ} (p : Fin l → ℝ) (S : Finset (Fin l)) (f : ℕ → ℝ) :
    eval p S f = eval p (S.filter (fun i => p i ≠ 0 ∧ p i ≠ 1))
      (fun k => f (k+(S.filter (fun i => p i = 1)).card)) := by
  classical
  induction S using Finset.induction_on generalizing f with
  | empty => simp [eval]
  | insert i S hi ih =>
    rw [eval_insert p hi]
    have hnot : i ∉ S.filter (fun j => p j ≠ 0 ∧ p j ≠ 1) := fun h => hi (Finset.mem_filter.mp h).1
    have hnot1 : i ∉ S.filter (fun j => p j = 1) := fun h => hi (Finset.mem_filter.mp h).1
    by_cases z : p i = 0
    · simp [z,Finset.filter_insert,ih f]
    · by_cases o : p i = 1
      · rw [o]
        simp [o,Finset.filter_insert,hnot1,ih (fun k => f (k+1)),Nat.add_right_comm,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm]
      · simp only [Finset.filter_insert,if_pos (And.intro z o),if_neg o,eval_insert p hnot]
        rw [ih f,ih (fun k => f (k+1))]
        congr 2
        apply congrArg (eval p _)
        funext k
        simp [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm]


theorem eval_nonneg {l : ℕ} (p : Fin l → ℝ) (box : ∀ i, p i ∈ Icc 0 1)
    (S : Finset (Fin l)) {f : ℕ → ℝ} (pos : ∀ k ≤ S.card, 0 ≤ f k) : 0 ≤ eval p S f := by
  unfold eval
  apply Finset.sum_nonneg
  intro U hU
  refine mul_nonneg (pos U.card (Finset.card_le_card (Finset.mem_powerset.mp hU))) ?_
  exact Finset.prod_nonneg (fun i _ => by split <;> first | exact (box i).1 | exact sub_nonneg.mpr (box i).2)

theorem eval_mono {l : ℕ} (p : Fin l → ℝ) (box : ∀ i, p i ∈ Icc 0 1)
    (S : Finset (Fin l)) {f g : ℕ → ℝ} (mono : ∀ k ≤ S.card, f k ≤ g k) : eval p S f ≤ eval p S g := by
  apply Finset.sum_le_sum
  intro U hu
  refine mul_le_mul_of_nonneg_right (mono _ (Finset.card_le_card (Finset.mem_powerset.mp hu))) ?_
  exact Finset.prod_nonneg (fun i _ => by split <;> first | exact (box i).1 | exact sub_nonneg.mpr (box i).2)

end StratifyMarkets.BernoulliExtremum
end

-- Solutions.StratifyMarketsMedianBound
section
namespace StratifyMarkets.BernoulliExtremum
open Set

/-- The common-probability binomial tail passed to the extremal argument. -/
def IntegerBinomialBound : Prop :=
  ∀ N m : ℕ, m < N → ∑ k ∈ Finset.Ioo m (N+1),
    (N.choose k : ℝ) * ((m:ℝ)/N)^k * (1-(m:ℝ)/N)^(N-k) ≤ 1/2

theorem parameter_sum {l : ℕ} (p : Fin l → ℝ) (S : Finset (Fin l)) :
    (∑ i ∈ S, p i) = (S.filter (fun i => p i = 1)).card +
      ∑ i ∈ S.filter (fun i => p i ≠ 0 ∧ p i ≠ 1), p i := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | insert i S hi ih =>
    have hnot : i ∉ S.filter (fun k => p k = 1) := fun h => hi (Finset.mem_filter.mp h).1
    have hnot' : i ∉ S.filter (fun k => p k ≠ 0 ∧ p k ≠ 1) := fun h => hi (Finset.mem_filter.mp h).1
    by_cases zero : p i = 0
    · simp [Finset.filter_insert,hi,zero,ih]
    · by_cases one : p i = 1
      · simp [Finset.filter_insert,hi,one,hnot,ih]; ring
      · simp [Finset.filter_insert,hi,one,zero,hnot',ih]; ring

theorem integer_upper {l : ℕ} (core : IntegerBinomialBound) (p₀ : Fin l → ℝ)
    (box : ∀ i, p₀ i ∈ Icc 0 1) {M : ℕ} (hM : (∑ i, p₀ i) = M) :
    eval p₀ Finset.univ (fun k => if M < k then 1 else 0) ≤ 1/2 := by
  classical
  let f := fun k : ℕ => if M < k then (1:ℝ) else 0
  obtain ⟨p,boxP,mean,upper,equal⟩ := extremal (fun p => eval p Finset.univ f)
    (eval_continuous _ f) (eval_slices f) p₀ box
  apply upper.trans
  let U := Finset.univ.filter (fun i => p i ≠ 0 ∧ p i ≠ 1)
  let ones := (Finset.univ.filter (fun i => p i = 1)).card
  have sum := parameter_sum p Finset.univ
  change (∑ i, p i) = (ones:ℝ) + ∑ i ∈ U, p i at sum
  rw [mean,hM] at sum
  rw [strip_deterministic]
  change eval p U (fun k => f (k+ones)) ≤ _
  rcases U.eq_empty_or_nonempty with e|⟨i,hi⟩
  · rw [e] at sum ⊢
    simp only [Finset.sum_empty,add_zero] at sum
    have eq : M = ones := by exact_mod_cast sum
    simp only [eval,Finset.powerset_empty,Finset.sum_singleton,Finset.prod_empty,Finset.card_empty,zero_add,mul_one]
    simp [f,eq]
  let q := p i
  have inner {j} (hj : j ∈ U) : p j ∈ Ioo 0 1 := by
    obtain ⟨z,o⟩ := (Finset.mem_filter.mp hj).2
    exact ⟨(boxP j).1.lt_of_ne z.symm,(boxP j).2.lt_of_ne o⟩
  have hq : 0 < q ∧ q < 1 := inner hi
  have eq (j) (hj : j ∈ U) : p j = q := equal j i (inner hj) hq
  rw [Finset.sum_congr rfl eq,Finset.sum_const,nsmul_eq_mul] at sum
  have npos : 0 < (U.card:ℝ) := by exact_mod_cast (Finset.card_pos.mpr ⟨i,hi⟩)
  have dpos : (ones:ℝ) ≤ M := by nlinarith [mul_pos npos hq.1]
  have on : ones ≤ M := by exact_mod_cast dpos
  let m := M-ones
  have cast : (m:ℝ) = M-ones := Nat.cast_sub on
  have small : m < U.card := by
    have sub : (m:ℝ) < U.card := by rw [cast]; nlinarith [mul_pos npos (sub_pos.mpr hq.2)]
    exact_mod_cast sub
  have qval : q = (m:ℝ)/U.card := by
    apply (eq_div_iff npos.ne').2
    rw [cast]
    linarith [mul_comm (U.card:ℝ) q]
  rw [eval_constant U eq]
  have iff (k : ℕ) : M < k + ones ↔ m < k := by dsimp [m]; omega
  have event : (Finset.range (U.card+1)).filter (fun k => m < k) = Finset.Ioo m (U.card+1) := by
    ext k
    simp [and_comm]
  simp only [f,iff,mul_ite,mul_one,mul_zero,← Finset.sum_filter,event,qval]
  exact core U.card m small


/-- Moving all Bernoulli parameters toward one can only increase any
nondecreasing payoff of the success count. -/
theorem increase_parameters {l : ℕ} (p q : Fin l → ℝ) (hp : ∀ i, p i ∈ Icc 0 1)
    (hq : ∀ i, q i ∈ Icc 0 1) (pq : ∀ i, p i ≤ q i) (S : Finset (Fin l))
    (f : ℕ → ℝ) (up : Monotone f) : eval p S f ≤ eval q S f := by
  classical
  induction S using Finset.induction_on generalizing f with
  | empty => simp [eval]
  | insert i S hi ih =>
    rw [eval_insert p hi,eval_insert q hi]
    let g := fun k => f (k+1)
    have gup : Monotone g := fun _ _ hh => up (Nat.add_le_add_right hh _)
    have h0 := ih f up
    have h1 := ih g gup
    have diff := eval_mono q hq S (f := f) (g := g) (fun k _ => up (Nat.le_succ k))
    change (1-p i)*eval p S f + p i*eval p S g ≤ (1-q i)*eval q S f + q i*eval q S g
    calc
      _ ≤ (1-p i)*eval q S f + p i*eval q S g := add_le_add
        (mul_le_mul_of_nonneg_left h0 (sub_nonneg.mpr (hp i).2)) (mul_le_mul_of_nonneg_left h1 (hp i).1)
      _ ≤ _ := by nlinarith [mul_nonneg (sub_nonneg.mpr (pq i)) (sub_nonneg.mpr diff)]

/-- Rounding the total mean upwards is realized by increasing the original
parameters proportionally to their unused probability mass. -/
theorem round_parameters {l : ℕ} (p : Fin l → ℝ) (hp : ∀ i, p i ∈ Icc 0 1) :
    ∃ q : Fin l → ℝ, (∀ i, q i ∈ Icc 0 1) ∧ (∀ i, p i ≤ q i) ∧
      (∑ i, q i) = (⌈∑ i, p i⌉₊ : ℝ) := by
  let s := ∑ i, p i
  let m := ⌈s⌉₊
  have sl : s ≤ (l:ℝ) := by
    simpa [s] using (Finset.sum_le_sum (s := Finset.univ) fun i (_ : i ∈ Finset.univ) => (hp i).2)
  have sm : s ≤ (m:ℝ) := Nat.le_ceil s
  have ml : (m:ℝ) ≤ l := by exact_mod_cast (Nat.ceil_le.mpr sl)
  by_cases eq : s = l
  · exact ⟨p,hp,fun _ => le_rfl,by change s = (m:ℝ); linarith⟩
  have den : 0 < (l:ℝ)-s := sub_pos.mpr (sl.lt_of_ne eq)
  let t := ((m:ℝ)-s)/((l:ℝ)-s)
  have tn : 0 ≤ t := div_nonneg (sub_nonneg.mpr sm) den.le
  have tmax : t ≤ 1 := (div_le_one den).mpr (by linarith)
  let q := fun i => p i+t*(1-p i)
  have growth (i) : p i ≤ q i := le_add_of_nonneg_right (mul_nonneg tn (sub_nonneg.mpr (hp i).2))
  refine ⟨q,fun i => ⟨(hp i).1.trans (growth i),?_⟩,growth,?_⟩
  · change p i+t*(1-p i) ≤ 1
    nlinarith [mul_nonneg (sub_nonneg.mpr tmax) (sub_nonneg.mpr (hp i).2)]
  · change (∑ i, (p i+t*(1-p i))) = (m:ℝ)
    rw [Finset.sum_add_distrib,← Finset.mul_sum,Finset.sum_sub_distrib]
    simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,mul_one]
    change s+t*(l-s) = m
    dsimp only [t]
    rw [div_mul_cancel₀ _ den.ne']
    ring

theorem upper_ceil {l : ℕ} (core : IntegerBinomialBound) (p : Fin l → ℝ)
    (box : ∀ i, p i ∈ Icc 0 1) :
    eval p Finset.univ (fun k => if ⌈∑ i, p i⌉₊ < k then 1 else 0) ≤ 1/2 := by
  let m := ⌈∑ i, p i⌉₊
  obtain ⟨q,hq,inc,mass⟩ := round_parameters p box
  have up : Monotone (fun k : ℕ => if m < k then (1:ℝ) else 0) := by
    intro k j kj
    dsimp only
    split_ifs <;> norm_num <;> omega
  exact (increase_parameters p q box hq inc _ _ up).trans (integer_upper core q hq mass)

end StratifyMarkets.BernoulliExtremum
end

-- Solutions.StratifyMarketsBernoulliTransport
section
open MeasureTheory ProbabilityTheory Set
namespace StratifyMarkets.BernoulliExtremum

noncomputable def successes {Ω : Type*} {l : ℕ} (X : Fin l → Ω → ℝ) (ω : Ω) :=
  Finset.univ.filter (fun i => X i ω = 1)

theorem sum_eq_card {Ω : Type*} [MeasurableSpace Ω] {l : ℕ} (P : Measure Ω) (X : Fin l → Ω → ℝ)
    (bern : ∀ i, ∀ᵐ ω ∂P, X i ω = 0 ∨ X i ω = 1) :
    ∀ᵐ ω ∂P, (∑ i, X i ω) = ((successes X ω).card : ℝ) := by
  classical
  filter_upwards [ae_all_iff.mpr bern] with ω h
  have eq (i) : X i ω = if X i ω = 1 then 1 else 0 := by rcases h i with a|a <;> simp [a]
  simpa only [successes,Finset.sum_boole] using Finset.sum_congr (s₁ := Finset.univ) (s₂ := Finset.univ) rfl (fun i _ => eq i)

theorem mean_eq_sum {Ω : Type*} [MeasurableSpace Ω] {l : ℕ} (P : Measure Ω) [IsProbabilityMeasure P]
    (X : Fin l → Ω → ℝ) (meas : ∀ i, Measurable (X i))
    (bern : ∀ i, ∀ᵐ ω ∂P, X i ω = 0 ∨ X i ω = 1) :
    (∫ ω, ∑ i, X i ω ∂P) = ∑ i, P.real {ω | X i ω = 1} := by
  classical
  let E := fun i => {ω | X i ω = 1}
  have hE (i) : MeasurableSet (E i) := (meas i) (measurableSet_singleton 1)
  have eq (i) : X i =ᵐ[P] (E i).indicator (fun _ => (1:ℝ)) := by
    filter_upwards [bern i] with ω h
    rcases h with h|h <;> simp [E,h]
  have int (i) : Integrable (X i) P := ((integrable_const _).indicator (hE i)).congr (eq i).symm
  rw [integral_finsetSum _ fun i _ => int i]
  apply Finset.sum_congr rfl
  intro i _
  rw [integral_congr_ae (eq i),integral_indicator (hE i),setIntegral_one_eq_measureReal]

theorem payoff_law {Ω : Type*} [MeasurableSpace Ω] {l : ℕ} (P : Measure Ω) [IsProbabilityMeasure P]
    (X : Fin l → Ω → ℝ) (meas : ∀ i, Measurable (X i)) (ind : iIndepFun X P) (f : ℕ → ℝ) :
    (∫ ω, f (successes X ω).card ∂P) = eval (fun i => P.real {ω | X i ω = 1}) Finset.univ f := by
  classical
  let cell := fun (U : Finset (Fin l)) => {ω | successes X ω = U}
  let target := fun (U : Finset (Fin l)) (i : Fin l) => if i ∈ U then ({1} : Set ℝ) else ({1} : Set ℝ)ᶜ
  have box (U : Finset (Fin l)) : cell U = ⋂ i ∈ (Finset.univ : Finset (Fin l)), X i ⁻¹' target U i := by
    ext ω
    simp only [cell,mem_setOf_eq,mem_iInter,Finset.mem_univ,true_implies,mem_preimage]
    constructor
    · intro h i
      have member : i ∈ U ↔ X i ω = 1 := by rw [← h]; simp [successes]
      by_cases hi : i ∈ U
      · simp [target,hi,member.mp hi]
      · simp [target,hi,mt member.mpr hi]
    · intro h
      ext i
      by_cases hi : i ∈ U
      · simpa [successes,hi] using (show X i ω = 1 by simpa [target,hi] using h i)
      · simpa [successes,hi] using (show X i ω ≠ 1 by simpa [target,hi] using h i)
  have mt (U) (i) : MeasurableSet (target U i) := by
    by_cases h : i ∈ U <;> simp [target,h]
  have mc (U) : MeasurableSet (cell U) := by
    rw [box]
    apply MeasurableSet.iInter
    intro i
    apply MeasurableSet.iInter
    intro _
    exact (meas i) (mt U i)
  have V (U) : P.real (cell U) = ∏ i, if i ∈ U then P.real {ω | X i ω = 1} else 1-P.real {ω | X i ω = 1} := by
    rw [box,measureReal_def,ind.measure_inter_preimage_eq_mul Finset.univ (fun i _ => mt U i),ENNReal.toReal_prod]
    apply Finset.prod_congr rfl
    intro i _
    by_cases hi : i ∈ U
    · simp [target,hi,measureReal_def]; rfl
    · simp only [target,if_neg hi,preimage_compl]
      change P.real (X i ⁻¹' {1})ᶜ = _
      rw [measureReal_compl ((meas i) (measurableSet_singleton 1)),probReal_univ]; rfl
  have point (ω) : f (successes X ω).card =
      ∑ U : Finset (Fin l), (cell U).indicator (fun _ => f U.card) ω := by
    rw [Finset.sum_eq_single (successes X ω)]
    · simp [cell]
    · intro V _ hv
      have absent : ω ∉ cell V := fun hh => hv (show successes X ω = V from hh).symm
      exact Set.indicator_of_notMem absent _
    · simp
  simp_rw [point]
  rw [integral_finsetSum _ (fun U _ => (integrable_const _).indicator (mc U))]
  unfold eval
  rw [Finset.powerset_univ]
  apply Finset.sum_congr rfl
  intro U _
  rw [integral_indicator (mc U)]
  simp only [setIntegral_const,smul_eq_mul,← measureReal_def,V]
  ring


theorem upper_near_mean {Ω : Type*} [MeasurableSpace Ω] {l : ℕ} (core : IntegerBinomialBound)
    (P : Measure Ω) [IsProbabilityMeasure P] (X : Fin l → Ω → ℝ) (meas : ∀ i, Measurable (X i))
    (bern : ∀ i, ∀ᵐ ω ∂P, X i ω = 0 ∨ X i ω = 1) (ind : iIndepFun X P) :
    (1/2:ℝ) ≤ P.real {ω | (∑ i, X i ω) < (∫ z, ∑ i, X i z ∂P)+1} := by
  classical
  let p := fun i => P.real {ω | X i ω = 1}
  have box (i) : p i ∈ Icc 0 1 := ⟨measureReal_nonneg,measureReal_le_one⟩
  let s := ∑ i, p i
  let m := ⌈s⌉₊
  have center : (∫ ω, ∑ i, X i ω ∂P) = s := mean_eq_sum P X meas bern
  have sn : 0 ≤ s := Finset.sum_nonneg fun i _ => (box i).1
  have near : (m:ℝ) < s+1 := Nat.ceil_lt_add_one sn
  let total := fun ω => ∑ i, X i ω
  let E := {ω | (m:ℝ) < total ω}
  have hm : Measurable total := Finset.measurable_sum _ fun i _ => meas i
  have hE : MeasurableSet E := hm measurableSet_Ioi
  have bw := upper_ceil core p box
  let f := fun k : ℕ => if m < k then (1:ℝ) else 0
  have eq := payoff_law P X meas ind f
  have convert : (fun ω => f (successes X ω).card) =ᵐ[P] E.indicator (fun _ => (1:ℝ)) := by
    filter_upwards [sum_eq_card P X bern] with ω h
    change total ω = ((successes X ω).card:ℝ) at h
    by_cases c : m < (successes X ω).card
    · have mem : ω ∈ E := by change (m:ℝ) < total ω; rw [h]; exact_mod_cast c
      simp [f,c,mem]
    · have mem : ω ∉ E := by
        intro H
        change (m:ℝ) < total ω at H
        rw [h] at H
        exact c (by exact_mod_cast H)
      simp [f,c,mem]
  have tail : P.real E ≤ 1/2 := by
    rw [integral_congr_ae convert,integral_indicator hE,setIntegral_one_eq_measureReal] at eq
    exact eq.trans_le bw
  rw [center]
  apply le_trans _ (measureReal_mono (μ := P) (s₁ := Eᶜ) (s₂ := {ω | ∑ i, X i ω < s+1}) ?_)
  · rw [measureReal_compl hE,probReal_univ]
    linarith
  · intro ω h
    change ¬ (m:ℝ) < total ω at h
    exact (le_of_not_gt h).trans_lt near

theorem two_tails {Ω : Type*} [MeasurableSpace Ω] {l : ℕ} (core : IntegerBinomialBound)
    (P : Measure Ω) [IsProbabilityMeasure P] (X : Fin l → Ω → ℝ) (meas : ∀ i, Measurable (X i))
    (bern : ∀ i, ∀ᵐ ω ∂P, X i ω = 0 ∨ X i ω = 1) (ind : iIndepFun X P) :
    (1/2:ℝ) ≤ P.real {ω | (∫ z, ∑ i, X i z ∂P)-1 < ∑ i, X i ω} ∧
    (1/2:ℝ) ≤ P.real {ω | (∑ i, X i ω) < (∫ z, ∑ i, X i z ∂P)+1} := by
  classical
  let Y := fun (i : Fin l) ω => 1-X i ω
  have ym (i) : Measurable (Y i) := measurable_const.sub (meas i)
  have yb (i) : ∀ᵐ ω ∂P, Y i ω = 0 ∨ Y i ω = 1 := by
    filter_upwards [bern i] with ω h
    rcases h with z|z <;> simp [Y,z]
  have yi : iIndepFun Y P := ind.comp (fun _ x => 1-x) fun _ => measurable_const.sub measurable_id
  have reverse (ω) : (∑ i, Y i ω) = (l:ℝ) - ∑ i, X i ω := by simp [Y,Finset.sum_sub_distrib]
  have ix (i) : Integrable (X i) P := by
    apply Integrable.of_bound (meas i).aestronglyMeasurable 1
    filter_upwards [bern i] with ω h
    rcases h with z|z <;> simp [z]
  have rel : (∫ ω, ∑ i, Y i ω ∂P) = (l:ℝ) - ∫ ω, ∑ i, X i ω ∂P := by
    simp_rw [reverse]
    rw [integral_sub (integrable_const _) (integrable_finsetSum _ fun i _ => ix i),integral_const]
    simp
  have upper := upper_near_mean core P Y ym yb yi
  refine ⟨upper.trans (measureReal_mono (μ := P) ?_),upper_near_mean core P X meas bern ind⟩
  intro ω h
  change (∑ i, Y i ω) < (∫ z, ∑ i, Y i z ∂P)+1 at h
  rw [reverse,rel] at h
  change (∫ z, ∑ i, X i z ∂P)-1 < ∑ i, X i ω
  linarith

theorem median_of_binomial_bound (core : IntegerBinomialBound) {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (l : ℕ) (X : Fin l → Ω → ℝ) (hmeas : ∀ i, Measurable (X i))
    (hbern : ∀ i, ∀ᵐ ω ∂P, X i ω = 0 ∨ X i ω = 1) (hindep : ProbabilityTheory.iIndepFun X P) :
    (∀ k : ℤ, (k : ℝ) ≤ ∫ ω, ∑ i, X i ω ∂P → ∫ ω, ∑ i, X i ω ∂P ≤ (k : ℝ) + 1 →
      ∃ M : ℤ, (M = k ∨ M = k + 1) ∧
        (1 / 2 : ENNReal) ≤ P {ω | ∑ i, X i ω ≤ (M : ℝ)} ∧
        (1 / 2 : ENNReal) ≤ P {ω | (M : ℝ) ≤ ∑ i, X i ω}) ∧
    (1 / 2 : ENNReal) ≤ P {ω | (∫ ω', ∑ i, X i ω' ∂P) - 1 < ∑ i, X i ω} ∧
    (1 / 2 : ENNReal) ≤ P {ω | ∑ i, X i ω < (∫ ω', ∑ i, X i ω' ∂P) + 1} := by
  classical
  let total := fun ω => ∑ i, X i ω
  let avg := ∫ ω, total ω ∂P
  have lower := (two_tails core P X hmeas hbern hindep).1
  have upper := (two_tails core P X hmeas hbern hindep).2
  change (1/2:ℝ) ≤ P.real {ω | avg-1 < total ω} at lower
  change (1/2:ℝ) ≤ P.real {ω | total ω < avg+1} at upper
  have liftHalf {E : Set Ω} (h : (1/2:ℝ) ≤ P.real E) : (1/2:ENNReal) ≤ P E := by
    apply (ENNReal.toReal_le_toReal (by norm_num) (measure_ne_top P E)).mp
    simpa [measureReal_def] using h
  have real_mono {s t : Set Ω} (h : s ≤ᵐ[P] t) : P.real s ≤ P.real t :=
    ENNReal.toReal_mono (measure_ne_top P t) (measure_mono_ae h)
  have integerVal := sum_eq_card P X hbern
  refine ⟨?_,liftHalf lower,liftHalf upper⟩
  intro k ks sk
  change (k:ℝ) ≤ avg at ks
  change avg ≤ (k:ℝ)+1 at sk
  have hm : Measurable total := Finset.measurable_sum _ fun i _ => hmeas i
  have left : (1/2:ℝ) ≤ P.real {ω | (k:ℝ) ≤ total ω} := by
    apply lower.trans (real_mono ?_)
    filter_upwards [integerVal] with ω eq
    change total ω = ((successes X ω).card:ℝ) at eq
    intro hu
    change avg-1 < total ω at hu
    change (k:ℝ) ≤ total ω
    rw [eq] at hu ⊢
    by_contra neg
    have one : (((successes X ω).card:ℕ):ℤ) + 1 ≤ k := by
      have lt : (((successes X ω).card:ℕ):ℤ) < k := by exact_mod_cast lt_of_not_ge neg
      omega
    have bound : ((successes X ω).card:ℝ)+1 ≤ (k:ℝ) := by exact_mod_cast one
    linarith
  have right : (1/2:ℝ) ≤ P.real {ω | total ω ≤ ((k+1:ℤ):ℝ)} := by
    apply upper.trans (real_mono ?_)
    filter_upwards [integerVal] with ω eq
    change total ω = ((successes X ω).card:ℝ) at eq
    intro hu
    change total ω < avg+1 at hu
    change total ω ≤ ((k+1:ℤ):ℝ)
    rw [eq] at hu ⊢
    by_contra neg
    have lt : k+1 < (((successes X ω).card:ℕ):ℤ) := by exact_mod_cast lt_of_not_ge neg
    have one : k+2 ≤ (((successes X ω).card:ℕ):ℤ) := by omega
    have bound : (k:ℝ)+2 ≤ ((successes X ω).card:ℝ) := by exact_mod_cast one
    linarith
  by_cases med : (1/2:ℝ) ≤ P.real {ω | total ω ≤ (k:ℝ)}
  · exact ⟨k,Or.inl rfl,liftHalf med,liftHalf left⟩
  · refine ⟨k+1,Or.inr rfl,liftHalf right,liftHalf ?_⟩
    let E := {ω | total ω ≤ (k:ℝ)}
    have half : (1/2:ℝ) ≤ P.real Eᶜ := by
      have mE : MeasurableSet E := hm measurableSet_Iic
      rw [measureReal_compl mE,probReal_univ]
      change ¬ (1/2:ℝ) ≤ P.real E at med
      linarith
    apply half.trans (real_mono ?_)
    filter_upwards [integerVal] with ω eq
    change total ω = ((successes X ω).card:ℝ) at eq
    intro hu
    change ¬ total ω ≤ (k:ℝ) at hu
    change ((k+1:ℤ):ℝ) ≤ total ω
    rw [eq] at hu ⊢
    have lt : k < (((successes X ω).card:ℕ):ℤ) := by exact_mod_cast lt_of_not_ge hu
    exact_mod_cast (show k+1 ≤ (((successes X ω).card:ℕ):ℤ) by omega)

end StratifyMarkets.BernoulliExtremum
end

-- Solutions.Sol_StratifyMarkets_DoubleAuction_theorem_4_2
section
open MeasureTheory StratifyMarkets.BernoulliExtremum

theorem solution {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (l : ℕ) (X : Fin l → Ω → ℝ) (hmeas : ∀ i, Measurable (X i))
    (hbern : ∀ i, ∀ᵐ ω ∂P, X i ω = 0 ∨ X i ω = 1) (hindep : ProbabilityTheory.iIndepFun X P) :
    (∀ k : ℤ, (k : ℝ) ≤ ∫ ω, ∑ i, X i ω ∂P → ∫ ω, ∑ i, X i ω ∂P ≤ (k : ℝ) + 1 →
      ∃ M : ℤ, (M = k ∨ M = k + 1) ∧
        (1 / 2 : ENNReal) ≤ P {ω | ∑ i, X i ω ≤ (M : ℝ)} ∧
        (1 / 2 : ENNReal) ≤ P {ω | (M : ℝ) ≤ ∑ i, X i ω}) ∧
    (1 / 2 : ENNReal) ≤ P {ω | (∫ ω', ∑ i, X i ω' ∂P) - 1 < ∑ i, X i ω} ∧
    (1 / 2 : ENNReal) ≤ P {ω | ∑ i, X i ω < (∫ ω', ∑ i, X i ω' ∂P) + 1} := by
  apply median_of_binomial_bound _ P l X hmeas hbern hindep
  intro N m hm
  simpa only [MatrixCompletion.binomialCardinalityProb] using binomial_integer_mean_upper_tail_le_half N m hm
end
