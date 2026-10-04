-- Prove2me | solution 1 for TeschlODE.Linear.liouville_formula
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-03T20:09:39.165092+00:00
-- url     : https://prove2.me/submissions/c73c76bf-9db6-4168-901a-04d39e1c8066

import Mathlib
import Definitions.Def_TeschlODE_Linear_IsSolution

open Polynomial Set TeschlODE.Linear

lemma jacobi_core {n : ℕ} (a B : Matrix (Fin n) (Fin n) ℝ) :
    ∑ σ : Equiv.Perm (Fin n), (Equiv.Perm.sign σ : ℝ) *
      ∑ j : Fin n, (∏ i ∈ Finset.univ.erase j, a (σ i) i) * (B * a) (σ j) j =
      B.trace * a.det := by
  set P : ℝ[X] := (a.map C + (X : ℝ[X]) • (B * a).map C).det with hP
  have h1 : P = (1 + (X : ℝ[X]) • B.map C).det * C a.det := by
    rw [hP, RingHom.map_det]
    rw [← Matrix.det_mul]
    congr 1
    rw [add_mul, one_mul, Matrix.smul_mul, Matrix.map_mul]
    rfl
  have h2 : P.coeff 1 = B.trace * a.det := by
    rw [h1, coeff_mul_C, Matrix.coeff_det_one_add_X_smul_one]
  have h3 : P.coeff 1 = (derivative P).eval 0 := by
    rw [← coeff_zero_eq_eval_zero, coeff_derivative]; simp
  rw [← h2, h3, hP, Matrix.det_apply']
  simp only [derivative_sum, Matrix.add_apply, Matrix.map_apply, Matrix.smul_apply, smul_eq_mul]
  rw [eval_finsetSum]
  refine Finset.sum_congr rfl fun σ _ => ?_
  have hc : ((Equiv.Perm.sign σ : ℤ) : ℝ[X]) = C ((Equiv.Perm.sign σ : ℤ) : ℝ) := by simp
  rw [hc, derivative_C_mul, eval_mul, eval_C, derivative_prod_finset, eval_finsetSum]
  congr 1
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [eval_mul, eval_prod]
  simp

theorem solution {n : ℕ} (A : ℝ → Matrix (Fin n) (Fin n) ℝ) (I : Set ℝ)
    (hI : I.OrdConnected) (hA : ContinuousOn A I) (U : ℝ → Matrix (Fin n) (Fin n) ℝ)
    (hU : ∀ j : Fin n, IsSolution A I (fun t i => U t i j)) (t₀ t : ℝ) (ht₀ : t₀ ∈ I)
    (ht : t ∈ I) :
    (U t).det = (U t₀).det * Real.exp (∫ s in t₀..t, (A s).trace) := by
  -- derivative of the Wronskian
  have hW : ∀ s ∈ I, HasDerivWithinAt (fun τ => (U τ).det) ((A s).trace * (U s).det) I s := by
    intro s hs
    have hent : ∀ i k : Fin n, HasDerivWithinAt (fun τ => U τ k i) ((A s * U s) k i) I s := by
      intro i k
      have := (hasDerivWithinAt_pi.mp (hU i s hs)) k
      have heq : (A s * U s) k i = (A s).mulVec (fun l => U s l i) k := by
        simp [Matrix.mul_apply, Matrix.mulVec, dotProduct]
      rw [heq]; exact this
    have : HasDerivWithinAt (fun τ => ∑ σ : Equiv.Perm (Fin n), (Equiv.Perm.sign σ : ℝ) *
        ∏ i, U τ (σ i) i)
        (∑ σ : Equiv.Perm (Fin n), (Equiv.Perm.sign σ : ℝ) *
          ∑ j : Fin n, (∏ i ∈ Finset.univ.erase j, U s (σ i) i) * (A s * U s) (σ j) j) I s := by
      apply HasDerivWithinAt.fun_sum
      intro σ _
      apply HasDerivWithinAt.const_mul
      have := HasDerivWithinAt.fun_finsetProd (u := Finset.univ) (f := fun i τ => U τ (σ i) i)
        (f' := fun i => (A s * U s) (σ i) i) (fun i _ => hent i (σ i))
      simpa [smul_eq_mul] using this
    rw [← jacobi_core]
    convert this using 1
    funext τ
    rw [Matrix.det_apply']
  -- the interval between `t₀` and `t`
  set J := Icc (min t₀ t) (max t₀ t) with hJ
  have hJI : J ⊆ I := hI.out (by rcases le_total t₀ t with h | h <;> simp [h, ht₀, ht])
    (by rcases le_total t₀ t with h | h <;> simp [h, ht₀, ht])
  have ht₀J : t₀ ∈ J := ⟨min_le_left _ _, le_max_left _ _⟩
  have htJ : t ∈ J := ⟨min_le_right _ _, le_max_right _ _⟩
  set g : ℝ → ℝ := fun s => (A s).trace with hg
  have hgc : ContinuousOn g J := ((continuous_id.matrix_trace).comp_continuousOn hA).mono hJI
  have hF : ∀ s ∈ J, HasDerivWithinAt (fun u => ∫ x in t₀..u, g x) (g s) J s := by
    intro s hs
    have : Fact (s ∈ Icc (min t₀ t) (max t₀ t)) := ⟨hs⟩
    have hsub : uIcc t₀ s ⊆ J := uIcc_subset_Icc ht₀J hs
    exact intervalIntegral.integral_hasDerivWithinAt_right ((hgc.mono hsub).intervalIntegrable)
      (hgc.stronglyMeasurableAtFilter_nhdsWithin measurableSet_Icc s) (hgc s hs)
  -- `G(s) = W(s) * exp(-F(s))` is constant
  set G : ℝ → ℝ := fun s => (U s).det * Real.exp (-∫ x in t₀..s, g x) with hG
  have hG' : ∀ s ∈ J, HasDerivWithinAt G 0 J s := by
    intro s hs
    have h1 := (hW s (hJI hs)).mono hJI
    have h2 := ((hF s hs).neg).exp
    refine (h1.mul h2).congr_deriv ?_
    simp only [Pi.neg_apply, hg]
    ring
  have hconst := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le (C := 0) hG' (fun _ _ => by simp)
    (convex_Icc _ _) ht₀J htJ
  rw [zero_mul] at hconst
  have hGeq : G t = G t₀ := sub_eq_zero.mp (norm_le_zero_iff.mp hconst)
  simp only [hG, intervalIntegral.integral_same, neg_zero, Real.exp_zero, mul_one] at hGeq
  rw [← hGeq, mul_assoc, ← Real.exp_add, neg_add_cancel, Real.exp_zero, mul_one]

#print axioms solution
