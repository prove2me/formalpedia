-- Prove2me | solution 1 for WatrousTQI.psd_convex_summand_range
-- status  : ACCEPTED   (prove)
-- author  : @Mrnaiq
-- created : 2026-11-14T15:04:43.229688+00:00
-- url     : https://prove2.me/submissions/a6ba79fe-d541-4947-931f-d5949fd9c450

import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.InnerProductSpace.Adjoint
noncomputable section
open scoped Matrix ComplexConjugate ComplexOrder MatrixOrder
set_option backward.isDefEq.respectTransparency false
variable {n : ℕ}
lemma hermitian_range_of_ker (P Q : Matrix (Fin n) (Fin n) ℂ)
    (hP : P.IsHermitian) (hQ : Q.IsHermitian)
    (hk : ∀ x, P.mulVec x = 0 → Q.mulVec x = 0) :
    LinearMap.range Q.mulVecLin ≤ LinearMap.range P.mulVecLin := by
  have he : LinearMap.range Q.toEuclideanLin ≤ LinearMap.range P.toEuclideanLin := by
    rw [← Submodule.orthogonal_le_orthogonal_iff,
      LinearMap.orthogonal_range,LinearMap.orthogonal_range,
      ← Matrix.toEuclideanLin_conjTranspose_eq_adjoint,
      ← Matrix.toEuclideanLin_conjTranspose_eq_adjoint,hP.eq,hQ.eq]
    intro x hx
    change P.toEuclideanLin x = 0 at hx
    change Q.toEuclideanLin x = 0
    have hx' : P.mulVec (WithLp.ofLp x) = 0 := by
      have := congrArg WithLp.ofLp hx
      simpa using this
    simpa only [Matrix.toEuclideanLin_apply,← WithLp.toLp_zero] using
      congrArg (WithLp.toLp 2) (hk _ hx')
  rintro y ⟨x,rfl⟩
  obtain ⟨z,hz⟩ := he ⟨WithLp.toLp 2 x,rfl⟩
  refine ⟨WithLp.ofLp z,?_⟩
  have h := congrArg WithLp.ofLp hz
  simpa using h

set_option autoImplicit false


theorem solution {n : ℕ} (hn : 0 < n)
    (P Q₀ Q₁ : Matrix (Fin n) (Fin n) ℂ)
    (h₀ : Q₀.PosSemidef) (h₁ : Q₁.PosSemidef)
    (t : ℝ) (ht₀ : 0 < t) (ht₁ : t < 1)
    (hP : P = t • Q₀ + (1 - t) • Q₁) :
    LinearMap.range Q₀.mulVecLin ≤ LinearMap.range P.mulVecLin ∧
    LinearMap.range Q₁.mulVecLin ≤ LinearMap.range P.mulVecLin := by
  have hp : P.PosSemidef := hP ▸ (h₀.smul ht₀.le).add (h₁.smul (sub_pos.mpr ht₁).le)
  have hk (x : Fin n → ℂ) (hx : P.mulVec x = 0) :
      Q₀.mulVec x = 0 ∧ Q₁.mulVec x = 0 := by
    have hz : t • (star x ⬝ᵥ Q₀.mulVec x) + (1-t) • (star x ⬝ᵥ Q₁.mulVec x) = 0 := by
      have := congrArg (fun v => star x ⬝ᵥ v) hx
      rw [hP,Matrix.add_mulVec,Matrix.smul_mulVec,Matrix.smul_mulVec,
        dotProduct_add,dotProduct_smul,dotProduct_smul,
        dotProduct_zero] at this
      exact this
    have hz₀ : t • (star x ⬝ᵥ Q₀.mulVec x) = 0 := by
      apply le_antisymm _ (smul_nonneg ht₀.le (h₀.dotProduct_mulVec_nonneg x))
      calc
        _ ≤ t • (star x ⬝ᵥ Q₀.mulVec x) + (1-t) • (star x ⬝ᵥ Q₁.mulVec x) :=
          le_add_of_nonneg_right (smul_nonneg (sub_pos.mpr ht₁).le (h₁.dotProduct_mulVec_nonneg x))
        _ = 0 := hz
    have hz₁ : (1-t) • (star x ⬝ᵥ Q₁.mulVec x) = 0 := by
      simpa only [hz₀,zero_add] using hz
    exact ⟨(h₀.dotProduct_mulVec_zero_iff x).mp ((smul_eq_zero.mp hz₀).resolve_left ht₀.ne'),
      (h₁.dotProduct_mulVec_zero_iff x).mp ((smul_eq_zero.mp hz₁).resolve_left (sub_pos.mpr ht₁).ne')⟩
  exact ⟨hermitian_range_of_ker P Q₀ hp.isHermitian h₀.isHermitian (fun x hx => (hk x hx).1),
    hermitian_range_of_ker P Q₁ hp.isHermitian h₁.isHermitian (fun x hx => (hk x hx).2)⟩
