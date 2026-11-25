-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Vertical_SecAlgFieldChange_proof_8385afe2af7e
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T06:07:26.978883+00:00
-- url     : https://prove2.me/submissions/9bac9db1-6760-4bbf-8f13-129060d8425f

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_StatementsChowNorm
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_PSecAlgFieldChange
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Vertical_SecAlgFieldChange_normForm_eq_det_40a80ca110c3
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Vertical_SecAlgFieldChange_secIdeal_map_7adffbdf0ec9

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Vertical
open MvPolynomial
open scoped TensorProduct
noncomputable section
namespace GroundTheory.Heights₂.Heights.Vertical
namespace SecAlgFieldChange
theorem _root_.solution : SecAlgFieldChange.Statement := by
  intro E₀ E _ _ φ n e Q₀ y₀ hfin
  classical
  letI : Algebra E₀ E := φ.toAlgebra
  have hI := SecAlgFieldChange.secIdeal_map φ Q₀ y₀
  set Q := Q₀.map (MvPolynomial.map φ)
  set y : Par e n → E := φ ∘ y₀

  let g : SecAlg Q₀ y₀ →ₐ[E₀] SecAlg Q y :=
    Ideal.quotientMapₐ (secIdeal Q y) (MvPolynomial.mapAlgHom (Algebra.ofId E₀ E))
      (by rw [hI]; exact Ideal.le_comap_map)
  have hg : ∀ p, g (Ideal.Quotient.mk _ p) = Ideal.Quotient.mk _ (MvPolynomial.map φ p) := by
    intro p; rfl

  let ψ : SecAlg Q y →ₐ[E] E ⊗[E₀] SecAlg Q₀ y₀ :=
    Ideal.Quotient.liftₐ (secIdeal Q y)
      (aeval fun j => (1 : E) ⊗ₜ[E₀] secCoord Q₀ y₀ j) (by
        intro a ha
        rw [hI] at ha
        have hle : (secIdeal Q₀ y₀).map (MvPolynomial.map φ) ≤
            RingHom.ker
              (MvPolynomial.aeval (R := E) fun j => (1 : E) ⊗ₜ[E₀] secCoord Q₀ y₀ j).toRingHom := by
          rw [Ideal.map_le_iff_le_comap]
          intro p hp
          rw [Ideal.mem_comap, RingHom.mem_ker]
          change aeval (fun j => (1 : E) ⊗ₜ[E₀] secCoord Q₀ y₀ j)
            (MvPolynomial.map (algebraMap E₀ E) p) = 0
          rw [MvPolynomial.aeval_map_algebraMap, MvPolynomial.aeval_one_tmul]
          have h0 : aeval (secCoord Q₀ y₀) p = 0 := by
            rw [show secCoord Q₀ y₀ = (Ideal.Quotient.mkₐ E₀ (secIdeal Q₀ y₀)) ∘ X from rfl,
              ← MvPolynomial.aeval_unique, Ideal.Quotient.mkₐ_eq_mk]
            exact Ideal.Quotient.eq_zero_iff_mem.mpr hp
          rw [h0, TensorProduct.tmul_zero]
        exact RingHom.mem_ker.mp (hle ha))
  have hψ : ∀ p, ψ (Ideal.Quotient.mk _ p) = aeval (fun j => (1 : E) ⊗ₜ[E₀] secCoord Q₀ y₀ j) p :=
    fun p => rfl
  let θ : E ⊗[E₀] SecAlg Q₀ y₀ →ₐ[E] SecAlg Q y :=
    Algebra.TensorProduct.lift (Algebra.ofId E _) g (fun _ _ => Commute.all _ _)
  have hθ : ∀ a, θ (1 ⊗ₜ a) = g a := by
    intro a; simp [θ]
  let eqv : E ⊗[E₀] SecAlg Q₀ y₀ ≃ₐ[E] SecAlg Q y :=
    AlgEquiv.ofAlgHom θ ψ
      (by
        apply Ideal.Quotient.algHom_ext
        apply MvPolynomial.algHom_ext
        intro j
        show θ (ψ (Ideal.Quotient.mk _ (X j))) = Ideal.Quotient.mk _ (X j)
        rw [hψ, aeval_X, hθ, secCoord, hg, map_X])
      (by
        apply Algebra.TensorProduct.ext
        · exact Subsingleton.elim _ _
        · apply Ideal.Quotient.algHom_ext
          apply MvPolynomial.algHom_ext
          intro j
          show ψ (θ (1 ⊗ₜ Ideal.Quotient.mk _ (X j))) = 1 ⊗ₜ Ideal.Quotient.mk _ (X j)
          rw [hθ, hg, map_X, hψ, aeval_X]
          rfl)
  haveI := hfin
  let b := Module.Free.chooseBasis E₀ (SecAlg Q₀ y₀)
  let B := (Algebra.TensorProduct.basis E b).map eqv.toLinearEquiv
  have hB : ∀ a i, B.repr (g a) i = φ (b.repr a i) := by
    intro a i
    have : g a = eqv.toLinearEquiv (1 ⊗ₜ a) := (hθ a).symm
    simp [B, this]
    rfl
  have hBk : ∀ k, B k = g (b k) := by
    intro k; simp [B, eqv, hθ]
  have hx : ∀ j, secCoord Q y j = g (secCoord Q₀ y₀ j) := by
    intro j; simp [secCoord, hg]
  refine ⟨Module.Finite.of_basis B, ?_⟩
  rw [SecAlgFieldChange.normForm_eq_det b, SecAlgFieldChange.normForm_eq_det B, RingHom.map_det]
  congr 1
  refine Matrix.ext fun i k => ?_
  simp only [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.of_apply, map_sum, map_mul,
    MvPolynomial.map_X, MvPolynomial.map_C, hx, hBk]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← map_mul, hB]
end SecAlgFieldChange
end GroundTheory.Heights₂.Heights.Vertical
