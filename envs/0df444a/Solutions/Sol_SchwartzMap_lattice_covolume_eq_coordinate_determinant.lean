-- Prove2me | solution 1 for SchwartzMap.lattice_covolume_eq_coordinate_determinant
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:37.283608+00:00
-- url     : https://prove2.me/submissions/3a25f4d4-2859-4110-88f4-176f8a310f7b

import Mathlib
import Definitions.Def_SpherePacking
import Theorems.Thm_SchwartzMap_reference_basis_fundamental_region_volume

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
theorem _root_.solution :
    ZLattice.covolume L =
      abs ((LinearMap.det : ((EuclideanSpace ℝ (Fin d)) →ₗ[ℝ] (EuclideanSpace ℝ (Fin d))) →* ℝ) ((latticeCoordinateEquiv L).toLinearMap)) := by
  let bZ : Basis (Fin d) ℤ L := integralLatticeCoordinateBasis L
  have hdet :
      (referenceEuclideanBasis (d := d)).det (fun i : Fin d => (bZ i : (EuclideanSpace ℝ (Fin d)))) =
        (LinearMap.det : ((EuclideanSpace ℝ (Fin d)) →ₗ[ℝ] (EuclideanSpace ℝ (Fin d))) →* ℝ) ((latticeCoordinateEquiv L).toLinearMap) := by
    have hdetA :
        (LinearMap.det : ((EuclideanSpace ℝ (Fin d)) →ₗ[ℝ] (EuclideanSpace ℝ (Fin d))) →* ℝ) ((latticeCoordinateEquiv L).toLinearMap) =
          (referenceEuclideanBasis (d := d)).det (realLatticeCoordinateBasis (d := d) L) := by
      simp [latticeCoordinateEquiv, referenceEuclideanBasis]
    have hr : realLatticeCoordinateBasis (d := d) L = fun i : Fin d => (bZ i : (EuclideanSpace ℝ (Fin d))) := by
      funext i
      simp [realLatticeCoordinateBasis, bZ]
    exact (congrArg ((referenceEuclideanBasis (d := d)).det) hr.symm).trans hdetA.symm
  have hcovol :
      ZLattice.covolume L = |(referenceEuclideanBasis (d := d)).det (fun i : Fin d => (bZ i : (EuclideanSpace ℝ (Fin d))))| := by
    simpa [referenceEuclideanBasis, reference_basis_fundamental_region_volume (d := d)] using!
      (ZLattice.covolume_eq_det_mul_measureReal
        (L := L) (b := bZ) (b₀ := referenceEuclideanBasis (d := d)) (μ := (volume : Measure (EuclideanSpace ℝ (Fin d)))))
  simp [hcovol, hdet]
end SchwartzMap
