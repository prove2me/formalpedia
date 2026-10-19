-- Prove2me | solution 1 for SchwartzMap.integer_lattice_poisson_identity
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:37.283608+00:00
-- url     : https://prove2.me/submissions/e2eaefd5-c8eb-4655-bd88-7b495960a5d8

import Mathlib
import Definitions.Def_SpherePacking
import Theorems.Thm_SpherePacking_ForMathlib_Fourier_fourier_precompose_linear_equivalence
import Theorems.Thm_SchwartzMap_PoissonSummation_Standard_reference_lattice_poisson_formula
import Theorems.Thm_SchwartzMap_lattice_covolume_eq_coordinate_determinant

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
open scoped BigOperators FourierTransform Real
open MeasureTheory Module
open SchwartzMap
variable {d : ℕ}
variable (L : Submodule ℤ (EuclideanSpace ℝ (Fin d))) [DiscreteTopology L] [IsZLattice ℝ L]
namespace SchwartzMap
theorem _root_.solution (f : SchwartzMap (EuclideanSpace ℝ (Fin d)) ℂ) (v : (EuclideanSpace ℝ (Fin d))) :
    (∑' ℓ : L, f (v + (ℓ : (EuclideanSpace ℝ (Fin d))))) =
      (1 / ZLattice.covolume L) *
        ∑' m : polarIntegerLattice (d := d) L,
          (𝓕 (fun x : (EuclideanSpace ℝ (Fin d)) => f x) m) * Complex.exp (2 * π * Complex.I * ⟪v, m⟫_[ℝ]) := by
  let A : (EuclideanSpace ℝ (Fin d)) ≃ₗ[ℝ] (EuclideanSpace ℝ (Fin d)) := latticeCoordinateTransport (d := d) (L := L)
  let g : SchwartzMap (EuclideanSpace ℝ (Fin d)) ℂ :=
    SchwartzMap.compCLMOfContinuousLinearEquiv ℂ A.toContinuousLinearEquiv f
  have hstd :=
    SchwartzMap.PoissonSummation.Standard.reference_lattice_poisson_formula
      (d := d) (f := g) (v := A.symm v)
  have hlhs :
      (∑' ℓ : SchwartzMap.referenceIntegerLattice d, g (A.symm v + (ℓ : (EuclideanSpace ℝ (Fin d))))) =
        ∑' ℓ : L, f (v + (ℓ : (EuclideanSpace ℝ (Fin d)))) := by
    calc
      (∑' ℓ : SchwartzMap.referenceIntegerLattice d, g (A.symm v + (ℓ : (EuclideanSpace ℝ (Fin d))))) =
          ∑' ℓ : SchwartzMap.referenceIntegerLattice d, f (v + A (ℓ : (EuclideanSpace ℝ (Fin d)))) := by
            refine tsum_congr fun ℓ ↦ ?_
            simp [g, map_add]
      _ = ∑' ℓ : L, f (v + (ℓ : (EuclideanSpace ℝ (Fin d)))) := by
          simpa [reference_lattice_coordinate_equiv_apply] using!
            ((referenceLatticeCoordinateEquiv (d := d) L).toEquiv.tsum_eq
              (f := fun ℓ : L => f (v + (ℓ : (EuclideanSpace ℝ (Fin d))))))
  have hrhs :
      (∑' n : Fin d → ℤ,
          (𝓕 (fun x : (EuclideanSpace ℝ (Fin d)) => g x) (SchwartzMap.PoissonSummation.Standard.embeddedIntegerVector (d := d) n)) *
            Complex.exp
              (2 * π * Complex.I *
                ⟪A.symm v, SchwartzMap.PoissonSummation.Standard.embeddedIntegerVector (d := d) n⟫_[ℝ])) =
        (1 / ZLattice.covolume L) *
          ∑' m : polarIntegerLattice (d := d) L,
            (𝓕 (fun x : (EuclideanSpace ℝ (Fin d)) => f x) m) * Complex.exp (2 * π * Complex.I * ⟪v, m⟫_[ℝ]) := by
    let F : polarIntegerLattice (d := d) L → ℂ :=
      fun m => (𝓕 (fun x : (EuclideanSpace ℝ (Fin d)) => f x) m) * Complex.exp (2 * π * Complex.I * ⟪v, m⟫_[ℝ])
    let detA : ℝ := (LinearMap.det : ((EuclideanSpace ℝ (Fin d)) →ₗ[ℝ] (EuclideanSpace ℝ (Fin d))) →* ℝ) (A : (EuclideanSpace ℝ (Fin d)) →ₗ[ℝ] (EuclideanSpace ℝ (Fin d)))
    let cC : ℂ := ((abs detA)⁻¹ : ℝ)
    have hfourier (w : (EuclideanSpace ℝ (Fin d))) :
        𝓕 (fun x : (EuclideanSpace ℝ (Fin d)) => g x) w =
          cC * 𝓕 (fun x : (EuclideanSpace ℝ (Fin d)) => f x) ((dualCoordinateTransport (d := d) L) w) := by
      simpa [g, A, dualCoordinateTransport, detA, cC, Complex.real_smul] using!
        (SpherePacking.ForMathlib.Fourier.fourier_precompose_linear_equivalence
          (A := A) (f := fun x : (EuclideanSpace ℝ (Fin d)) => f x) w)
    have hexp (w : (EuclideanSpace ℝ (Fin d))) :
        Complex.exp (2 * π * Complex.I * ⟪A.symm v, w⟫_[ℝ]) =
          Complex.exp (2 * π * Complex.I * ⟪v, (dualCoordinateTransport (d := d) L) w⟫_[ℝ]) := by
      have hinner : ⟪A.symm v, w⟫_[ℝ] = ⟪v, (dualCoordinateTransport (d := d) L) w⟫_[ℝ] := by
        have : inner ℝ (A.symm v) w = inner ℝ v ((dualCoordinateTransport (d := d) L) w) := by
          simpa [A, dualCoordinateTransport] using!
            (LinearMap.adjoint_inner_right ((A.symm : (EuclideanSpace ℝ (Fin d)) ≃ₗ[ℝ] (EuclideanSpace ℝ (Fin d))).toLinearMap) v w).symm
        simpa [RCLike.inner_eq_wInner_one] using! this
      simp [hinner]
    have hdetC : cC = (1 / ZLattice.covolume L) := by
      have hcovol : ZLattice.covolume L = abs detA := by
        simpa [A, latticeCoordinateTransport, detA] using! (lattice_covolume_eq_coordinate_determinant (d := d) (L := L))
      simp [cC, hcovol, one_div]
    have hsum :
        (∑' n : Fin d → ℤ,
            (𝓕 (fun x : (EuclideanSpace ℝ (Fin d)) => g x) (SchwartzMap.PoissonSummation.Standard.embeddedIntegerVector (d := d) n)) *
              Complex.exp
                (2 * π * Complex.I *
                  ⟪A.symm v, SchwartzMap.PoissonSummation.Standard.embeddedIntegerVector (d := d) n⟫_[ℝ])) =
          cC * ∑' m : polarIntegerLattice (d := d) L, F m := by
      calc
        (∑' n : Fin d → ℤ,
            (𝓕 (fun x : (EuclideanSpace ℝ (Fin d)) => g x) (SchwartzMap.PoissonSummation.Standard.embeddedIntegerVector (d := d) n)) *
              Complex.exp
                (2 * π * Complex.I *
                  ⟪A.symm v, SchwartzMap.PoissonSummation.Standard.embeddedIntegerVector (d := d) n⟫_[ℝ])) =
            ∑' n : Fin d → ℤ, cC * F (integerVectorPolarLatticeEquiv (d := d) L n) := by
              refine tsum_congr fun n ↦ ?_
              simpa [F, mul_assoc] using!
                congrArg₂ (· * ·)
                  (hfourier (w := SchwartzMap.PoissonSummation.Standard.embeddedIntegerVector (d := d) n))
                  (hexp (w := SchwartzMap.PoissonSummation.Standard.embeddedIntegerVector (d := d) n))
        _ = cC * ∑' n : Fin d → ℤ, F (integerVectorPolarLatticeEquiv (d := d) L n) := tsum_mul_left
        _ = cC * ∑' m : polarIntegerLattice (d := d) L, F m := by
              rw [(integerVectorPolarLatticeEquiv (d := d) L).tsum_eq]
    simp [hsum, hdetC, F]
  simpa [hlhs, hrhs] using! hstd
end SchwartzMap
