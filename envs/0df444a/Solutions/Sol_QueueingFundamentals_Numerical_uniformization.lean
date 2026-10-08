-- Prove2me | solution 1 for QueueingFundamentals.Numerical.uniformization
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-06T16:33:55.645671+00:00
-- url     : https://prove2.me/submissions/b600a3b5-907f-4c89-a768-af6af64bc8ea

import Mathlib
import Definitions.Def_QueueingFundamentals_Numerical_Uniformization

set_option autoImplicit false

open Matrix

namespace UnifAuxCF41

open QueueingFundamentals.Numerical

variable {N : ℕ}

noncomputable def opOf (M : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ) :
    (Fin (N + 1) → ℝ) →L[ℝ] (Fin (N + 1) → ℝ) :=
  LinearMap.toContinuousLinearMap (Matrix.vecMulLinear M)

lemma opOf_apply (M : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ) (v : Fin (N + 1) → ℝ) :
    opOf M v = v ᵥ* M := rfl

lemma opOf_pow (M : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ) (k : ℕ) (v : Fin (N + 1) → ℝ) :
    (opOf M ^ k) v = v ᵥ* (M ^ k) := by
  induction k generalizing v with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, ContinuousLinearMap.mul_apply, ih, opOf_apply, pow_succ', vecMul_vecMul]

lemma opOf_unif (Λ : ℝ) (Q : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ) :
    opOf (uniformizedMatrix Λ Q) = Λ⁻¹ • opOf Q + 1 := by
  ext1 v
  simp only [opOf_apply, uniformizedMatrix, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.smul_apply, ContinuousLinearMap.one_apply, vecMul_add, vecMul_smul,
    vecMul_one]

/-- the explicit solution -/
noncomputable def sol (Q : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ) (p₀ : Fin (N + 1) → ℝ)
    (t : ℝ) : Fin (N + 1) → ℝ :=
  (NormedSpace.exp (t • opOf Q)) p₀

lemma sol_hasDerivAt (Q : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ) (p₀ : Fin (N + 1) → ℝ)
    (t : ℝ) : HasDerivAt (sol Q p₀) (sol Q p₀ t ᵥ* Q) t := by
  have h := hasDerivAt_exp_smul_const' (𝕂 := ℝ) (opOf Q) t
  have h2 := (ContinuousLinearMap.apply ℝ (Fin (N + 1) → ℝ) p₀).hasFDerivAt.comp_hasDerivAt t h
  exact h2

lemma sol_zero (Q : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ) (p₀ : Fin (N + 1) → ℝ) :
    sol Q p₀ 0 = p₀ := by
  simp [sol]

lemma sol_solves (Q : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ) (p₀ : Fin (N + 1) → ℝ) :
    SolvesForward Q p₀ (sol Q p₀) :=
  ⟨sol_zero Q p₀, fun t _ => (sol_hasDerivAt Q p₀ t).hasDerivWithinAt⟩

lemma unique (Q : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ) (p₀ : Fin (N + 1) → ℝ)
    (p : ℝ → Fin (N + 1) → ℝ) (hp : SolvesForward Q p₀ p) (t : ℝ) (ht : 0 ≤ t) :
    p t = sol Q p₀ t := by
  have key := ODE_solution_unique_of_mem_Icc_right (v := fun _ x => opOf Q x)
    (s := fun _ => Set.univ) (K := ‖opOf Q‖₊) (a := 0) (b := t)
    (fun _ _ => (opOf Q).lipschitz.lipschitzOnWith)
    (f := p) (g := sol Q p₀)
    (fun x hx => (hp.2 x hx.1).continuousWithinAt.mono Set.Icc_subset_Ici_self)
    (fun x hx => (hp.2 x hx.1).mono (Set.Ici_subset_Ici.2 hx.1))
    (fun _ _ => Set.mem_univ _)
    (fun x _ => (sol_hasDerivAt Q p₀ x).continuousAt.continuousWithinAt)
    (fun x _ => (sol_hasDerivAt Q p₀ x).hasDerivWithinAt)
    (fun _ _ => Set.mem_univ _)
    (by rw [hp.1, sol_zero])
  exact key ⟨ht, le_rfl⟩

lemma sol_eq (Λ : ℝ) (hΛ : Λ ≠ 0) (Q : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ)
    (p₀ : Fin (N + 1) → ℝ) (t : ℝ) :
    sol Q p₀ t = Real.exp (-(Λ * t)) •
      (NormedSpace.exp ((Λ * t) • opOf (uniformizedMatrix Λ Q))) p₀ := by
  have hsplit : t • opOf Q = (Λ * t) • opOf (uniformizedMatrix Λ Q) +
      algebraMap ℝ ((Fin (N + 1) → ℝ) →L[ℝ] (Fin (N + 1) → ℝ)) (-(Λ * t)) := by
    rw [opOf_unif, Algebra.algebraMap_eq_smul_one, smul_add, smul_smul,
      mul_comm Λ t, mul_assoc, mul_inv_cancel₀ hΛ, mul_one, neg_smul]
    abel
  have hball : ∀ x : (Fin (N + 1) → ℝ) →L[ℝ] (Fin (N + 1) → ℝ),
      x ∈ Metric.eball (0 : (Fin (N + 1) → ℝ) →L[ℝ] (Fin (N + 1) → ℝ))
        (NormedSpace.expSeries ℝ ((Fin (N + 1) → ℝ) →L[ℝ] (Fin (N + 1) → ℝ))).radius := fun x =>
    (NormedSpace.expSeries_radius_eq_top ℝ ((Fin (N + 1) → ℝ) →L[ℝ] (Fin (N + 1) → ℝ))).symm ▸ edist_lt_top _ _
  rw [sol, hsplit, NormedSpace.exp_add_of_commute_of_mem_ball (𝕂 := ℝ)
      (Algebra.commutes _ _).symm (hball _) (hball _),
    ← NormedSpace.algebraMap_exp_comm, ← Real.exp_eq_exp_ℝ, Algebra.algebraMap_eq_smul_one,
    mul_smul_comm, mul_one, ContinuousLinearMap.smul_apply]

lemma sol_hasSum (Λ : ℝ) (hΛ : Λ ≠ 0) (Q : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ)
    (p₀ : Fin (N + 1) → ℝ) (t : ℝ) (n : Fin (N + 1)) :
    HasSum (fun k : ℕ => poissonWeight Λ t k * phi Λ Q p₀ k n) (sol Q p₀ t n) := by
  set B := opOf (uniformizedMatrix Λ Q)
  have h1 := NormedSpace.exp_series_hasSum_exp' (𝕂 := ℝ) ((Λ * t) • B)
  let L : ((Fin (N + 1) → ℝ) →L[ℝ] (Fin (N + 1) → ℝ)) →L[ℝ] ℝ :=
    (ContinuousLinearMap.proj n).comp (ContinuousLinearMap.apply ℝ (Fin (N + 1) → ℝ) p₀)
  have h2 := (h1.mapL L).mul_left (Real.exp (-(Λ * t)))
  have e1 : (fun k : ℕ => poissonWeight Λ t k * phi Λ Q p₀ k n) = fun k : ℕ =>
      Real.exp (-(Λ * t)) * L ((k.factorial⁻¹ : ℝ) • ((Λ * t) • B) ^ k) := by
    funext k
    rw [smul_pow, smul_smul, map_smul, smul_eq_mul]
    have hL : L (B ^ k) = phi Λ Q p₀ k n := by
      simp only [L, ContinuousLinearMap.comp_apply, ContinuousLinearMap.apply_apply,
        ContinuousLinearMap.proj_apply, B, opOf_pow, phi]
    rw [hL]
    unfold poissonWeight
    field_simp
  have e2 : sol Q p₀ t n = Real.exp (-(Λ * t)) * L (NormedSpace.exp ((Λ * t) • B)) := by
    rw [sol_eq Λ hΛ Q p₀ t]
    rfl
  rw [e1, e2]
  exact h2

/-- stochasticity of the uniformized matrix -/
lemma unif_stoch (Q : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ)
    (hQ : IsGenerator Q) (Λ : ℝ) (hΛ : 0 < Λ) (hΛq : ∀ i, exitRate Q i ≤ Λ) :
    IsStochastic (uniformizedMatrix Λ Q) := by
  constructor
  · intro i j
    simp only [uniformizedMatrix, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
    by_cases hij : i = j
    · subst hij
      have := hΛq i
      simp only [exitRate] at this
      rw [one_apply_eq]
      have : -1 ≤ Λ⁻¹ * Q i i := by
        rw [le_inv_mul_iff₀ hΛ]; linarith
      linarith
    · rw [one_apply_ne hij]
      have := hQ.1 i j hij
      positivity
  · intro i
    have hrow : ∑ j, Q i j = 0 := by
      rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i), hQ.2 i]; ring
    simp only [uniformizedMatrix, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, hrow]
    simp [one_apply]

lemma probvec_vecMul (φ : Fin (N + 1) → ℝ) (hφ : IsProbVec φ)
    (P : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ) (hP : IsStochastic P) :
    IsProbVec (φ ᵥ* P) := by
  constructor
  · intro j
    simp only [vecMul, dotProduct]
    exact Finset.sum_nonneg fun i _ => mul_nonneg (hφ.1 i) (hP.1 i j)
  · simp only [vecMul, dotProduct]
    rw [Finset.sum_comm]
    simp_rw [← Finset.mul_sum, hP.2, mul_one]
    exact hφ.2

lemma phi_prob (Λ : ℝ) (Q : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ)
    (hP : IsStochastic (uniformizedMatrix Λ Q)) (p₀ : Fin (N + 1) → ℝ) (hp₀ : IsProbVec p₀)
    (k : ℕ) : IsProbVec (phi Λ Q p₀ k) := by
  induction k with
  | zero => simpa [phi] using hp₀
  | succ k ih =>
    have : phi Λ Q p₀ (k + 1) = phi Λ Q p₀ k ᵥ* uniformizedMatrix Λ Q := by
      simp only [phi, pow_succ, vecMul_vecMul]
    rw [this]
    exact probvec_vecMul _ ih _ hP

lemma prob_le_one (φ : Fin (N + 1) → ℝ) (hφ : IsProbVec φ) (n : Fin (N + 1)) : φ n ≤ 1 := by
  rw [← hφ.2]
  exact Finset.single_le_sum (fun i _ => hφ.1 i) (Finset.mem_univ n)

lemma poisson_hasSum (Λ t : ℝ) : HasSum (poissonWeight Λ t) 1 := by
  have h := (NormedSpace.expSeries_div_hasSum_exp (Λ * t)).mul_left
    (Real.exp (-(Λ * t)))
  rw [← Real.exp_eq_exp_ℝ, ← Real.exp_add, neg_add_cancel, Real.exp_zero] at h
  have e : poissonWeight Λ t = fun i : ℕ =>
      Real.exp (-(Λ * t)) * ((Λ * t) ^ i / (i.factorial : ℝ)) := by
    funext k
    simp only [poissonWeight]
    ring
  rw [e]
  exact h

lemma poisson_nonneg (Λ t : ℝ) (hΛ : 0 < Λ) (ht : 0 ≤ t) (k : ℕ) : 0 ≤ poissonWeight Λ t k := by
  unfold poissonWeight
  have : 0 ≤ Λ * t := mul_nonneg hΛ.le ht
  positivity

end UnifAuxCF41

open QueueingFundamentals.Numerical in
theorem solution {N : ℕ} (Q : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ)
    (hQ : IsGenerator Q) (Λ : ℝ) (hΛ : 0 < Λ) (hΛq : ∀ i, exitRate Q i ≤ Λ)
    (p₀ : Fin (N + 1) → ℝ) (hp₀ : IsProbVec p₀) :
    (∃ p : ℝ → Fin (N + 1) → ℝ, SolvesForward Q p₀ p) ∧
      ∀ p : ℝ → Fin (N + 1) → ℝ, SolvesForward Q p₀ p → ∀ t : ℝ, 0 ≤ t →
        (∀ n, HasSum (fun k : ℕ => poissonWeight Λ t k * phi Λ Q p₀ k n) (p t n)) ∧
        ∀ (T : ℕ) (ε : ℝ), 1 - ε < ∑ k ∈ Finset.range (T + 1), poissonWeight Λ t k →
          ∀ n, |p t n - truncatedSolution Λ Q p₀ t T n| < ε := by
  refine ⟨⟨UnifAuxCF41.sol Q p₀, UnifAuxCF41.sol_solves Q p₀⟩, fun p hp t ht => ?_⟩
  have hpt := UnifAuxCF41.unique Q p₀ p hp t ht
  have hS : ∀ n, HasSum (fun k : ℕ => poissonWeight Λ t k * phi Λ Q p₀ k n) (p t n) := by
    intro n; rw [hpt]; exact UnifAuxCF41.sol_hasSum Λ hΛ.ne' Q p₀ t n
  refine ⟨hS, fun T ε hT n => ?_⟩
  have hP := UnifAuxCF41.unif_stoch Q hQ Λ hΛ hΛq
  have hw := UnifAuxCF41.poisson_nonneg Λ t hΛ ht
  have ha0 : ∀ k, 0 ≤ poissonWeight Λ t k * phi Λ Q p₀ k n :=
    fun k => mul_nonneg (hw k) ((UnifAuxCF41.phi_prob Λ Q hP p₀ hp₀ k).1 n)
  have hb0 : ∀ k, 0 ≤ poissonWeight Λ t k - poissonWeight Λ t k * phi Λ Q p₀ k n := by
    intro k
    have := UnifAuxCF41.prob_le_one _ (UnifAuxCF41.phi_prob Λ Q hP p₀ hp₀ k) n
    nlinarith [hw k]
  have htr : truncatedSolution Λ Q p₀ t T n =
      ∑ k ∈ Finset.range (T + 1), poissonWeight Λ t k * phi Λ Q p₀ k n := by
    simp [truncatedSolution, Finset.sum_apply]
  have hb := (UnifAuxCF41.poisson_hasSum Λ t).sub (hS n)
  have i1 := sum_le_hasSum (Finset.range (T + 1)) (fun k _ => ha0 k) (hS n)
  have i2 := sum_le_hasSum (Finset.range (T + 1)) (fun k _ => hb0 k) hb
  rw [Finset.sum_sub_distrib] at i2
  rw [htr, abs_of_nonneg (by linarith)]
  linarith
