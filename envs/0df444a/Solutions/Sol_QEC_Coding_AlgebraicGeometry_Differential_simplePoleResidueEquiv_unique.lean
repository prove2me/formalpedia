-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.Differential.simplePoleResidueEquiv_unique
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T18:34:15.617617+00:00
-- url     : https://prove2.me/submissions/e8f486ab-bcf4-4f50-815f-80eb2641c1e6

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Differentials_LocalUniformizerDerivative
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Residues_Local_Residue
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_Differential_simplePoleResidueEquiv_uniformizerLogDifferentialClass

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry
open scoped Polynomial RatFunc
open QEC.Coding.AlgebraicGeometry.Differential
open FunctionFieldDifferential
variable {k F : Type*} [Field k] [Finite k] [Field F] [Algebra k F]
variable [Algebra (RatFunc k) F] [IsScalarTower k (RatFunc k) F]
variable [Algebra.IsSeparable (RatFunc k) F] [FiniteDimensional (RatFunc k) F]
namespace QEC.Coding.AlgebraicGeometry.Differential
theorem _root_.solution
    (P : GlobalPlace k F)
    (e : localResidueLine P ≃ₗ[P.valuationRing] GlobalPlace.residueField P)
    (he : e (uniformizerLogDifferentialClass (k := k) (F := F) P) = 1) :
    e = simplePoleResidueEquiv (k := k) (F := F) P := by
  ext x
  let y : GlobalPlace.residueField P :=
    simplePoleResidueEquiv (k := k) (F := F) P x
  obtain ⟨r, hr⟩ := IsLocalRing.residue_surjective y
  have hr_smul : r • (1 : GlobalPlace.residueField P) =
      simplePoleResidueEquiv (k := k) (F := F) P x := by
    rw [Algebra.smul_def, mul_one,
      IsLocalRing.ResidueField.algebraMap_eq]
    exact hr
  have hx : x = r • uniformizerLogDifferentialClass (k := k) (F := F) P := by
    apply (simplePoleResidueEquiv (k := k) (F := F) P).injective
    rw [map_smul,
      simplePoleResidueEquiv_uniformizerLogDifferentialClass
        (k := k) (F := F) P]
    exact hr_smul.symm
  calc
    e x = e (r • uniformizerLogDifferentialClass (k := k) (F := F) P) := by rw [hx]
    _ = r • e (uniformizerLogDifferentialClass (k := k) (F := F) P) := map_smul e r _
    _ = r • 1 := by rw [he]
    _ = simplePoleResidueEquiv (k := k) (F := F) P x := hr_smul
end QEC.Coding.AlgebraicGeometry.Differential
