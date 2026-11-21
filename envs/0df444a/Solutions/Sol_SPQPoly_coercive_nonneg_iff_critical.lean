-- Prove2me | solution 1 for SPQPoly.coercive_nonneg_iff_critical
-- status  : ACCEPTED   (prove)
-- author  : @ducloc
-- created : 2026-11-20T13:33:27.59402+00:00
-- url     : https://prove2.me/submissions/583385ff-f0e5-4fc7-b782-1af6a5089307

import Mathlib

open MvPolynomial Filter

/-- Evaluation of the `i`-th partial derivative of a variable at a point. -/
private lemma eval_pderiv_X {n : ℕ} (x : Fin n → ℝ) (i j : Fin n) :
    MvPolynomial.eval x (MvPolynomial.pderiv i (MvPolynomial.X j)) =
      (Pi.single i (1 : ℝ) : Fin n → ℝ) j := by
  by_cases h : i = j
  · subst h
    simp
  · rw [MvPolynomial.pderiv_X_of_ne (Ne.symm h), map_zero, Pi.single_eq_of_ne (Ne.symm h)]

/-- The derivative at `0` of the univariate restriction
`t ↦ p (x + t • Pi.single i 1)` equals the `i`-th partial derivative of `p` at `x`. -/
private lemma hasDerivAt_eval_add_smul_single {n : ℕ} (p : MvPolynomial (Fin n) ℝ)
    (x : Fin n → ℝ) (i : Fin n) :
    HasDerivAt (fun t : ℝ => MvPolynomial.eval (x + t • (Pi.single i (1 : ℝ) : Fin n → ℝ)) p)
      (MvPolynomial.eval x (MvPolynomial.pderiv i p)) 0 := by
  induction p using MvPolynomial.induction_on with
  | C a =>
      simpa [MvPolynomial.eval_C, MvPolynomial.pderiv_C] using
        (hasDerivAt_const (c := a) (x := (0 : ℝ)))
  | add p q hp hq =>
      have h := hp.add hq
      convert h using 1
      · rfl
      · rfl
      · funext t
        simp [MvPolynomial.eval_add]
      · simp [map_add]
  | mul_X p j hp =>
      have hX : HasDerivAt
          (fun t : ℝ => (x + t • (Pi.single i (1 : ℝ) : Fin n → ℝ)) j)
          ((Pi.single i (1 : ℝ) : Fin n → ℝ) j) 0 := by
        have h := (hasDerivAt_const (c := x j) (x := (0 : ℝ))).add
          ((hasDerivAt_id (x := (0 : ℝ))).mul_const ((Pi.single i (1 : ℝ) : Fin n → ℝ) j))
        convert h using 1
        · rfl
        · rfl
        · funext t
          simp [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
        · simp
      have h := hp.mul hX
      convert h using 1
      · rfl
      · rfl
      · funext t
        simp [MvPolynomial.eval_mul, MvPolynomial.eval_X, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      · simp only [MvPolynomial.pderiv_mul, MvPolynomial.eval_add, MvPolynomial.eval_mul,
          MvPolynomial.eval_X, eval_pderiv_X, zero_smul, Pi.add_apply, Pi.zero_apply, add_zero]

theorem solution {n : ℕ} (p : MvPolynomial (Fin n) ℝ)
    (hp : Tendsto (fun x : Fin n → ℝ => MvPolynomial.eval x p) (cocompact (Fin n → ℝ)) atTop) :
    (∀ x : Fin n → ℝ, 0 ≤ MvPolynomial.eval x p) ↔
      (∀ x : Fin n → ℝ, (∀ i : Fin n, MvPolynomial.eval x (MvPolynomial.pderiv i p) = 0) →
        0 ≤ MvPolynomial.eval x p) := by
  constructor
  · intro h x _
    exact h x
  · intro hcrit
    by_contra hneg
    push Not at hneg
    obtain ⟨x, hx⟩ := hneg
    have hcont : Continuous (fun x : Fin n → ℝ => MvPolynomial.eval x p) :=
      MvPolynomial.continuous_eval p
    have hmem : {x : Fin n → ℝ | MvPolynomial.eval (0 : Fin n → ℝ) p ≤ MvPolynomial.eval x p} ∈
        cocompact (Fin n → ℝ) :=
      tendsto_atTop.1 hp (MvPolynomial.eval (0 : Fin n → ℝ) p)
    obtain ⟨K, hKcomp, hKsub⟩ := Filter.mem_cocompact.1 hmem
    let K' : Set (Fin n → ℝ) := insert (0 : Fin n → ℝ) K
    have hK'comp : IsCompact K' := by
      simpa [K'] using hKcomp.insert (0 : Fin n → ℝ)
    have hK'ne : K'.Nonempty := ⟨0, by simp [K']⟩
    obtain ⟨x₀, hx₀K', hx₀min⟩ := hK'comp.exists_isMinOn hK'ne hcont.continuousOn
    rw [isMinOn_iff] at hx₀min
    have hmin : ∀ y : Fin n → ℝ, MvPolynomial.eval x₀ p ≤ MvPolynomial.eval y p := by
      intro y
      by_cases hy : y ∈ K'
      · exact hx₀min y hy
      · have hyK : y ∈ Kᶜ := by
          intro hyK
          exact hy (by simp [K', hyK])
        have h1 : MvPolynomial.eval (0 : Fin n → ℝ) p ≤ MvPolynomial.eval y p := hKsub hyK
        have h2 : MvPolynomial.eval x₀ p ≤ MvPolynomial.eval (0 : Fin n → ℝ) p :=
          hx₀min 0 (by simp [K'])
        exact le_trans h2 h1
    have hzero : ∀ i : Fin n, MvPolynomial.eval x₀ (MvPolynomial.pderiv i p) = 0 := by
      intro i
      have hg : HasDerivAt
          (fun t : ℝ => MvPolynomial.eval (x₀ + t • (Pi.single i (1 : ℝ) : Fin n → ℝ)) p)
          (MvPolynomial.eval x₀ (MvPolynomial.pderiv i p)) 0 :=
        hasDerivAt_eval_add_smul_single p x₀ i
      have hgmin : IsMinOn
          (fun t : ℝ => MvPolynomial.eval (x₀ + t • (Pi.single i (1 : ℝ) : Fin n → ℝ)) p)
          Set.univ (0 : ℝ) := by
        rw [isMinOn_univ_iff]
        intro t
        simpa [zero_smul] using hmin (x₀ + t • (Pi.single i (1 : ℝ) : Fin n → ℝ))
      exact (hgmin.isLocalMin Filter.univ_mem).hasDerivAt_eq_zero hg
    have hnonneg : 0 ≤ MvPolynomial.eval x₀ p := hcrit x₀ hzero
    have hle : MvPolynomial.eval x₀ p ≤ MvPolynomial.eval x p := hmin x
    linarith
