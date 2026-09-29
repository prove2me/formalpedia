-- Prove2me | solution 1 for Rudin.ch10_pullback_integral
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T20:31:54.177685+00:00
-- url     : https://prove2.me/submissions/58b74800-8839-4e8a-8591-77e8a263922e

import Mathlib
import Definitions.Def_Rudin_ch10_forms
set_option autoImplicit false
open Filter Topology MeasureTheory Rudin

lemma scout_partial_eq {k n : ℕ} (T : (Fin k → ℝ) → (Fin n → ℝ))
    (x : Fin k → ℝ) (hd : DifferentiableAt ℝ T x) (i : Fin n) (j : Fin k) :
    partialDeriv (fun v => T v i) j x = (fderiv ℝ T x) (Pi.single j 1) i := by
  rw [partialDeriv, ((hasFDerivAt_pi'.mp hd.hasFDerivAt) i).fderiv]
  rfl
lemma scout_det_row_sums {k m : ℕ} (A : Matrix (Fin k) (Fin m) ℝ) (B : Matrix (Fin m) (Fin k) ℝ) :
    (Matrix.of fun r s => ∑ j, A r j * B j s).det =
      ∑ j : Fin k → Fin m, (∏ r, A r (j r)) * (Matrix.of fun r s => B (j r) s).det := by
  classical
  calc
    _ = Matrix.det (fun r => ∑ j, A r j • B j) := by congr 1; ext r s; simp
    _ = ∑ j : Fin k → Fin m, Matrix.det (fun r => A r (j r) • B (j r)) :=
      Matrix.detRowAlternating.toMultilinearMap.map_sum (fun r j => A r j • B j)
    _ = _ := by
      apply Finset.sum_congr rfl
      intro j hj
      exact Matrix.detRowAlternating.toMultilinearMap.map_smul_univ _ _
lemma scout_jac_comp {k m n : ℕ} (T : (Fin m → ℝ) → (Fin n → ℝ))
    (Φ : (Fin k → ℝ) → (Fin m → ℝ)) (u : Fin k → ℝ)
    (hT : DifferentiableAt ℝ T (Φ u)) (hΦ : DifferentiableAt ℝ Φ u) (i : Fin k → Fin n) :
    jacobian (T ∘ Φ) i u = ∑ j : Fin k → Fin m,
      (∏ r, partialDeriv (fun v => T v (i r)) (j r) (Φ u)) * jacobian Φ j u := by
  classical
  have hcomp : fderiv ℝ (T ∘ Φ) u = (fderiv ℝ T (Φ u)).comp (fderiv ℝ Φ u) :=
    (hT.hasFDerivAt.comp u hΦ.hasFDerivAt).fderiv
  have he (r s : Fin k) : partialDeriv (fun v => (T ∘ Φ) v (i r)) s u =
      ∑ j : Fin m, partialDeriv (fun v => T v (i r)) j (Φ u) *
        partialDeriv (fun v => Φ v j) s u := by
    rw [scout_partial_eq _ _ (hT.comp u hΦ), hcomp]
    simp_rw [scout_partial_eq _ _ hT, scout_partial_eq _ _ hΦ]
    exact congrFun (congrFun (LinearMap.toMatrix'_comp
      (fderiv ℝ T (Φ u)).toLinearMap (fderiv ℝ Φ u).toLinearMap) (i r)) s
  unfold jacobian
  simp_rw [he]
  exact scout_det_row_sums _ _
theorem solution (k m n : ℕ) (T : (Fin m → ℝ) → (Fin n → ℝ))
    (hT : ContDiff ℝ 1 T) (ω : KForm k n) (Φ : SimplexSurface k m) (hΦ : ContDiff ℝ 1 Φ.map) :
    integralOverSimplex ω ⟨T ∘ Φ.map⟩ = integralOverSimplex (pullback T ω) Φ := by
  classical
  apply MeasureTheory.integral_congr_ae
  filter_upwards [] with u
  change (∑ i : Fin k → Fin n, ω.coeff i (T (Φ.map u)) * jacobian (T ∘ Φ.map) i u) =
    ∑ j : Fin k → Fin m, (∑ i : Fin k → Fin n,
      ω.coeff i (T (Φ.map u)) * ∏ r, partialDeriv (fun v => T v (i r)) (j r) (Φ.map u)) *
        jacobian Φ.map j u
  simp_rw [scout_jac_comp T Φ.map u (hT.differentiable (by norm_num) _) (hΦ.differentiable (by norm_num) _),
    Finset.mul_sum, Finset.sum_mul, ← mul_assoc]
  exact Finset.sum_comm
#print axioms solution
