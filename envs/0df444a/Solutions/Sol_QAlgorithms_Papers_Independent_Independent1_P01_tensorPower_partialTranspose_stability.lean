-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Independent1.P01.tensorPower_partialTranspose_stability
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-18T20:59:53.222928+00:00
-- url     : https://prove2.me/submissions/1d638b21-e7b3-447b-a739-a16f6883ec06

import Mathlib
import Definitions.Def_QAlgorithms_Defs_BipartiteSeparability
import Definitions.Def_QAlgorithms_Defs_Hamiltonian
import Definitions.Def_QAlgorithms_Papers_Independent_Independent1_P01_Model
set_option autoImplicit false

/-!
# Peres: Separability Criterion for Density Matrices

Source: arXiv:quant-ph/9604005v2, PDF pp.2–5. The first subsystem alone
is transposed, without complex conjugation. Equation (5), which has a
conjugating-factor defect, is deferred; its valid spectral conclusion is stated.
-/

noncomputable section

open scoped Matrix ComplexOrder

open QAlgorithms QAlgorithms.Papers QAlgorithms.Papers.Independent QAlgorithms.Papers.Independent.Independent1 QAlgorithms.Papers.Independent.Independent1.P01
open QAlgorithms.Entanglement

/-- Peres PDF p.5, final paragraph: finite identical copies preserve separability,
partial transposition commutes with the observer-grouped tensor product, and
nonnegative partial-transpose spectrum is preserved without separability. -/
theorem gp_tp_dummy : True := trivial

open scoped MatrixOrder in
theorem gp_prod_psd {k : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : Fin k → Matrix ι ι ℂ) (h : ∀ t, (M t).PosSemidef) :
    (Matrix.of fun p q : Fin k → ι => ∏ t, M t (p t) (q t)).PosSemidef := by
  choose B hB using fun t => CStarAlgebra.nonneg_iff_eq_star_mul_self.mp (h t).nonneg
  let C : Matrix (Fin k → ι) (Fin k → ι) ℂ := Matrix.of fun r p => ∏ t, B t (r t) (p t)
  have hC : (Matrix.of fun p q : Fin k → ι => ∏ t, M t (p t) (q t)) = Cᴴ * C := by
    ext p q
    simp only [Matrix.of_apply, hB, Matrix.star_eq_conjTranspose, Matrix.mul_apply,
      Matrix.conjTranspose_apply, C]
    rw [Fintype.prod_sum]
    refine Finset.sum_congr rfl fun r _ => ?_
    rw [star_prod, ← Finset.prod_mul_distrib]
  rw [hC]
  exact Matrix.posSemidef_conjTranspose_mul_self C

theorem gp_otp_psd {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
    (M : Matrix (I × J) (I × J) ℂ) (hM : M.PosSemidef) (k : ℕ) :
    (observerTensorPower M k).PosSemidef := by
  have := (gp_prod_psd (fun _ : Fin k => M) (fun _ => hM)).submatrix
    (Equiv.arrowProdEquivProdArrow (Fin k) (fun _ => I) (fun _ => J)).symm
  convert this using 1
  ext p q
  rfl

theorem solution
    {I J : Type*} [Fintype I] [Fintype J] [Nonempty I] [Nonempty J]
    [DecidableEq I] [DecidableEq J]
    (rho : Matrix (I × J) (I × J) ℂ) (density : IsDensityMatrix rho)
    (k : ℕ) (copies : 1 ≤ k) :
    (IsSeparableDensity rho → IsSeparableDensity (observerTensorPower rho k)) ∧
    partialTransposeFirst (observerTensorPower rho k) =
      observerTensorPower (partialTransposeFirst rho) k ∧
    ((partialTransposeFirst rho).PosSemidef →
      (partialTransposeFirst (observerTensorPower rho k)).PosSemidef) := by
  refine ⟨?_, rfl, fun h => ?_⟩
  · rintro ⟨q, w, A, B, hw, hsum, hAB, hrho⟩
    let σ := (Fintype.equivFin (Fin k → Fin q)).symm
    refine ⟨Fintype.card (Fin k → Fin q), fun i => ∏ t, w (σ i t),
      fun i => Matrix.of fun x y => ∏ t, A (σ i t) (x t) (y t),
      fun i => Matrix.of fun x y => ∏ t, B (σ i t) (x t) (y t), ?_, ?_, ?_, ?_⟩
    · exact fun i => Finset.prod_nonneg fun t _ => hw _
    · rw [Equiv.sum_comp σ (fun f => ∏ t, w (f t)), ← Fintype.prod_sum, hsum, Finset.prod_const_one]
    · intro i
      refine ⟨⟨gp_prod_psd _ fun t => (hAB _).1.1, ?_⟩, ⟨gp_prod_psd _ fun t => (hAB _).2.1, ?_⟩⟩
      · simp only [Matrix.trace, Matrix.diag, Matrix.of_apply]
        rw [← Fintype.prod_sum (fun t a => A (σ i t) a a)]
        exact Finset.prod_eq_one fun t _ => (hAB _).1.2
      · simp only [Matrix.trace, Matrix.diag, Matrix.of_apply]
        rw [← Fintype.prod_sum (fun t a => B (σ i t) a a)]
        exact Finset.prod_eq_one fun t _ => (hAB _).2.2
    · ext p r
      simp only [observerTensorPower, hrho, Matrix.of_apply, Matrix.sum_apply, Matrix.smul_apply,
        Matrix.kronecker, Matrix.kroneckerMap_apply, smul_eq_mul]
      rw [Fintype.prod_sum, ← Equiv.sum_comp σ]
      refine Finset.sum_congr rfl fun i _ => ?_
      simp only [Complex.ofReal_prod, ← Finset.prod_mul_distrib]
  · exact gp_otp_psd _ h k

