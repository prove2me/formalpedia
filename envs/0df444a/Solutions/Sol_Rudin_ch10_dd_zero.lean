-- Prove2me | solution 1 for Rudin.ch10_dd_zero
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T21:08:03.114257+00:00
-- url     : https://prove2.me/submissions/feea1fd4-4e8b-4ccc-ab3c-ed666d82f3df

import Mathlib
import Definitions.Def_Rudin_ch10_forms
set_option autoImplicit false
open Filter Topology MeasureTheory Rudin

lemma scout_second_const {n : ℕ} (f : (Fin n → ℝ) → ℝ) (hf : ContDiff ℝ 2 f)
    (x v w : Fin n → ℝ) :
    fderiv ℝ (fun y => fderiv ℝ f y w) x v = fderiv ℝ (fderiv ℝ f) x v w := by
  rw [fderiv_clm_apply ((hf.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num) x)
    (differentiableAt_const w)]
  simp
theorem solution (k n : ℕ) (ω : KForm k n) (hω : ∀ i, ContDiff ℝ 2 (ω.coeff i))
    (Φ : SimplexSurface (k + 2) n) (hΦ : ContDiff ℝ 1 Φ.map) :
    integralOverSimplex (extDeriv (extDeriv ω)) Φ = 0 := by
  classical
  let τ : Equiv.Perm (Fin (k + 2)) := Equiv.swap 0 1
  have h01 : (0 : Fin (k + 2)) ≠ 1 := Fin.zero_ne_one
  have htail (r : Fin k) : τ r.succ.succ = r.succ.succ := by
    exact Equiv.swap_apply_of_ne_of_ne (Fin.succ_ne_zero _) (Fin.succ_succ_ne_one _)
  have hc (i : Fin (k + 2) → Fin n) (x : Fin n → ℝ) :
      (extDeriv (extDeriv ω)).coeff (i ∘ τ) x = (extDeriv (extDeriv ω)).coeff i x := by
    have ht : (fun r : Fin k => (i ∘ τ) r.succ.succ) = (fun r : Fin k => i r.succ.succ) := by
      funext r; simp only [Function.comp_apply, htail]
    change fderiv ℝ (fun y => fderiv ℝ (ω.coeff (fun r : Fin k => (i ∘ τ) r.succ.succ)) y
        (Pi.single ((i ∘ τ) 1) 1)) x (Pi.single ((i ∘ τ) 0) 1) =
      fderiv ℝ (fun y => fderiv ℝ (ω.coeff (fun r : Fin k => i r.succ.succ)) y
        (Pi.single (i 1) 1)) x (Pi.single (i 0) 1)
    rw [ht]
    simp only [Function.comp_apply, τ, Equiv.swap_apply_left, Equiv.swap_apply_right]
    rw [scout_second_const _ (hω _) , scout_second_const _ (hω _)]
    exact (hω _).contDiffAt.isSymmSndFDerivAt (by norm_num) _ _
  have hj (i : Fin (k + 2) → Fin n) (u : Fin (k + 2) → ℝ) :
      jacobian Φ.map (i ∘ τ) u = -jacobian Φ.map i u := by
    change (Matrix.submatrix (Matrix.of fun r s : Fin (k + 2) =>
      partialDeriv (fun v => Φ.map v (i r)) s u) τ id).det = _
    rw [Matrix.det_permute]
    simp [τ, h01, jacobian]
  have hsum (u : Fin (k + 2) → ℝ) :
      (∑ i : Fin (k + 2) → Fin n, (extDeriv (extDeriv ω)).coeff i (Φ.map u) *
        jacobian Φ.map i u) = 0 := by
    let F := fun i : Fin (k + 2) → Fin n =>
      (extDeriv (extDeriv ω)).coeff i (Φ.map u) * jacobian Φ.map i u
    let e : (Fin (k + 2) → Fin n) ≃ (Fin (k + 2) → Fin n) :=
      { toFun := fun i => i ∘ τ
        invFun := fun i => i ∘ τ
        left_inv := fun i => by funext r; simp [Function.comp_apply, τ]
        right_inv := fun i => by funext r; simp [Function.comp_apply, τ] }
    have hs := e.sum_comp F
    change (∑ i, F (i ∘ τ)) = ∑ i, F i at hs
    have hn (i : Fin (k + 2) → Fin n) : F (i ∘ τ) = -F i := by
      dsimp only [F]
      rw [hc, hj, mul_neg]
    simp_rw [hn] at hs
    rw [Finset.sum_neg_distrib] at hs
    change (∑ i, F i) = 0
    linarith
  simp only [integralOverSimplex, hsum, integral_zero]

#print axioms solution
