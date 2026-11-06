-- Prove2me | solution 1 for QEC.Bounds.BPTCommutingProjectorModel.boundaryGlobalToFourFactorTransport_eq_fourFactorTransport
-- status  : ACCEPTED   (prove)
-- author  : @Secousses
-- created : 2026-11-06T00:09:01.528605+00:00
-- url     : https://prove2.me/submissions/383afc68-1f71-49fe-b91d-f4f4a8593b19

import Definitions.Def_QEC_Bounds_BPTDisentangling_InteractionAlgebra
import Definitions.Def_QEC_Bounds_BPTDisentangling_FourFactor
set_option autoImplicit false
noncomputable section
open QEC
open QEC.Bounds
open Classical
open scoped BigOperators ComplexOrder TensorProduct
universe u v
open QEC.Bounds.BPTCommutingProjectorModel
variable {L : BPTQuditLattice} {kappa : Type v} [Fintype kappa]

namespace QBAux

theorem reg_apply_basis {ι : Type u} [Fintype ι] [DecidableEq ι] {q : ι → Nat}
    (S : Semantics.QuditSubsystem q) (l : Semantics.Qudit.Label q) :
    S.registerFactorization.toLinearEquiv
        (EuclideanSpace.basisFun (Semantics.Qudit.Label q) Complex l) =
      EuclideanSpace.basisFun (Semantics.Qudit.Label S.selectedDimensions) Complex (S.splitLabel l).1 ⊗ₜ[Complex]
      EuclideanSpace.basisFun (Semantics.Qudit.Label S.complementDimensions) Complex (S.splitLabel l).2 := by
  unfold Semantics.QuditSubsystem.registerFactorization
  dsimp only
  rw [LinearIsometryEquiv.coe_toLinearEquiv, OrthonormalBasis.equiv_apply_basis, OrthonormalBasis.tensorProduct_apply]
  rfl

theorem sel_apply_basis {ι : Type u} [Fintype ι] [DecidableEq ι] {q : ι → Nat}
    (S T : Semantics.QuditSubsystem q) (hST : S.selected ⊆ T.selected) (l : Semantics.Qudit.Label T.selectedDimensions) :
    (S.selectedFactorization T hST).toLinearEquiv
        (EuclideanSpace.basisFun (Semantics.Qudit.Label T.selectedDimensions) Complex l) =
      EuclideanSpace.basisFun (Semantics.Qudit.Label S.selectedDimensions) Complex (S.splitSelectedLabel T hST l).1 ⊗ₜ[Complex]
      EuclideanSpace.basisFun (Semantics.Qudit.Label (S.additionalRetainedDimensions T)) Complex (S.splitSelectedLabel T hST l).2 := by
  unfold Semantics.QuditSubsystem.selectedFactorization
  dsimp only
  rw [LinearIsometryEquiv.coe_toLinearEquiv, OrthonormalBasis.equiv_apply_basis, OrthonormalBasis.tensorProduct_apply]
  rfl

theorem compl_apply_basis {ι : Type u} [Fintype ι] [DecidableEq ι] {q : ι → Nat}
    (S T : Semantics.QuditSubsystem q) (hST : S.selected ⊆ T.selected) (l : Semantics.Qudit.Label S.complementDimensions) :
    (S.complementFactorization T hST).toLinearEquiv
        (EuclideanSpace.basisFun (Semantics.Qudit.Label S.complementDimensions) Complex l) =
      EuclideanSpace.basisFun (Semantics.Qudit.Label (S.additionalRetainedDimensions T)) Complex (S.splitComplementLabel T hST l).1 ⊗ₜ[Complex]
      EuclideanSpace.basisFun (Semantics.Qudit.Label T.complementDimensions) Complex (S.splitComplementLabel T hST l).2 := by
  unfold Semantics.QuditSubsystem.complementFactorization
  dsimp only
  rw [LinearIsometryEquiv.coe_toLinearEquiv, OrthonormalBasis.equiv_apply_basis, OrthonormalBasis.tensorProduct_apply]
  rfl

theorem relabel_apply_basis {I J : Type u} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
    {q : I → Nat} {r : J → Nat} (e : I ≃ J) (hdim : ∀ i, q i = r (e i)) (l : Semantics.Qudit.Label q) :
    (quditCoordinateRelabel e hdim).toLinearEquiv
        (EuclideanSpace.basisFun (Semantics.Qudit.Label q) Complex l) =
      EuclideanSpace.basisFun (Semantics.Qudit.Label r) Complex (quditLabelRelabel e hdim l) := by
  unfold quditCoordinateRelabel
  dsimp only
  rw [LinearIsometryEquiv.coe_toLinearEquiv, OrthonormalBasis.equiv_apply_basis]


theorem ut_ext {H K : Type u}
    [NormedAddCommGroup H] [InnerProductSpace Complex H] [Semantics.FiniteQuantumSystem H]
    [NormedAddCommGroup K] [InnerProductSpace Complex K] [Semantics.FiniteQuantumSystem K]
    (U V : Semantics.UnitaryTransport H K) (h : U.toLinearEquiv = V.toLinearEquiv) : U = V := by
  cases U
  cases V
  cases h
  rfl


abbrev QA (M : BPTCommutingProjectorModel L kappa) (region : Finset L.Site) :=
  M.regionSubsystem (M.interior region)
abbrev QAB (M : BPTCommutingProjectorModel L kappa) (region : Finset L.Site) :=
  M.regionSubsystem region
abbrev QABC (M : BPTCommutingProjectorModel L kappa) (region : Finset L.Site) :=
  M.regionSubsystem (region ∪ M.externalBoundary region)
abbrev QB (M : BPTCommutingProjectorModel L kappa) (region : Finset L.Site) :=
  M.regionSubsystem (M.internalBoundary region)
abbrev QBC (M : BPTCommutingProjectorModel L kappa) (region : Finset L.Site) :=
  M.regionSubsystem (M.boundary region)

theorem hAAB (M : BPTCommutingProjectorModel L kappa) (region : Finset L.Site) :
    (QA M region).selected ⊆ (QAB M region).selected :=
  fun _ hsite => (Finset.mem_sdiff.mp hsite).1

theorem hABABC (M : BPTCommutingProjectorModel L kappa) (region : Finset L.Site) :
    (QAB M region).selected ⊆ (QABC M region).selected :=
  fun _ hsite => Finset.mem_union_left _ hsite

theorem hBBC (M : BPTCommutingProjectorModel L kappa) (region : Finset L.Site) :
    (QB M region).selected ⊆ (QBC M region).selected :=
  fun _ hsite => (Finset.mem_inter.mp hsite).1

theorem boundary_eq (M : BPTCommutingProjectorModel L kappa) (region : Finset L.Site) :
    M.boundary region = M.internalBoundary region ∪ M.externalBoundary region := by
  ext x
  simp only [BPTCommutingProjectorModel.internalBoundary,
    BPTCommutingProjectorModel.externalBoundary, Finset.mem_union, Finset.mem_inter,
    Finset.mem_sdiff]
  tauto

theorem hBCABC (M : BPTCommutingProjectorModel L kappa) (region : Finset L.Site) :
    (QBC M region).selected ⊆ (QABC M region).selected := by
  intro site hsite
  have hboundary : site ∈ M.boundary region := hsite
  rw [boundary_eq] at hboundary
  rcases Finset.mem_union.mp hboundary with hinternal | hexternal
  · exact Finset.mem_union_left _ (Finset.mem_inter.mp hinternal).2
  · exact Finset.mem_union_right _ hexternal

theorem fourFactorTransport_eq (M : BPTCommutingProjectorModel L kappa) (region : Finset L.Site) :
    M.fourFactorTransport region =
      composeUnitaryTransport
        (composeUnitaryTransport (nestedFactorizationLeft (QAB M region) (QABC M region) (hABABC M region))
          (unitaryRTensor ((QA M region).selectedFactorization (QAB M region) (hAAB M region))
            (Semantics.CompositeSystem ((QAB M region).additionalRetainedSystem (QABC M region))
              (QABC M region).complementSystem)))
        (tensorAssociatorUnitary (QA M region).selectedSystem
          ((QA M region).additionalRetainedSystem (QAB M region))
          (Semantics.CompositeSystem ((QAB M region).additionalRetainedSystem (QABC M region))
            (QABC M region).complementSystem)) := rfl

theorem selectedToBC_eq (M : BPTCommutingProjectorModel L kappa) (region : Finset L.Site) :
    M.boundarySelectedToBCTransport region =
      composeUnitaryTransport
        (composeUnitaryTransport ((QB M region).selectedFactorization (QBC M region) (hBBC M region))
          (unitaryRTensor (M.fourFactorBCoordinateRelabel region)
            ((QB M region).additionalRetainedSystem (QBC M region))))
        (unitaryLTensor (M.fourFactorB region)
          (quditCoordinateRelabel
            (q := (QB M region).additionalRetainedDimensions (QBC M region))
            (r := (M.regionSubsystem region).additionalRetainedDimensions
              (M.regionSubsystem (region ∪ M.externalBoundary region)))
            (M.boundaryAdditionalCoordinateEquiv region) (fun _ => rfl))) := rfl

theorem complementToAD_eq (M : BPTCommutingProjectorModel L kappa) (region : Finset L.Site) :
    M.boundaryComplementToADTransport region =
      composeUnitaryTransport ((QBC M region).complementFactorization (QABC M region) (hBCABC M region))
        (unitaryRTensor
          (quditCoordinateRelabel
            (q := (QBC M region).additionalRetainedDimensions (QABC M region))
            (r := (QA M region).selectedDimensions)
            (M.boundaryComplementAdditionalCoordinateEquiv region) (fun _ => rfl))
          (QABC M region).complementSystem) := rfl

theorem fourFactorTransport_apply_basis (M : BPTCommutingProjectorModel L kappa)
    (region : Finset L.Site) (labels : Semantics.Qudit.Label L.localDimension) :
    (M.fourFactorTransport region).toLinearEquiv
        (EuclideanSpace.basisFun (Semantics.Qudit.Label L.localDimension) Complex labels) =
      M.fourFactorBasisVector region labels := by
  rw [fourFactorTransport_eq]
  simp only [composeUnitaryTransport_toLinearEquiv_apply, nestedFactorizationLeft_apply_basis,
    unitaryRTensor_toLinearEquiv_apply_tmul, sel_apply_basis,
    tensorAssociatorUnitary_toLinearEquiv_apply_tmul]
  rfl

theorem boundaryGlobal_apply_basis (M : BPTCommutingProjectorModel L kappa)
    (region : Finset L.Site) (labels : Semantics.Qudit.Label L.localDimension) :
    (M.boundaryGlobalToFourFactorTransport region).toLinearEquiv
        (EuclideanSpace.basisFun (Semantics.Qudit.Label L.localDimension) Complex labels) =
      M.fourFactorBasisVector region labels := by
  unfold BPTCommutingProjectorModel.boundaryGlobalToFourFactorTransport
    BPTCommutingProjectorModel.boundaryGlobalToMiddleTransport
  simp only [composeUnitaryTransport_toLinearEquiv_apply, reg_apply_basis,
    unitaryRTensor_toLinearEquiv_apply_tmul]
  rw [selectedToBC_eq, complementToAD_eq]
  simp only [composeUnitaryTransport_toLinearEquiv_apply, sel_apply_basis, compl_apply_basis,
    unitaryRTensor_toLinearEquiv_apply_tmul,
    unitaryLTensor_toLinearEquiv_apply_tmul, boundaryToMiddleReorder_toLinearEquiv_apply_tmul,
    fourFactorMiddleReassociate_symm_toLinearEquiv_apply_tmul]
  have hA : ∀ l, (quditCoordinateRelabel (q := (QBC M region).additionalRetainedDimensions (QABC M region))
        (r := (QA M region).selectedDimensions)
        (M.boundaryComplementAdditionalCoordinateEquiv region) (fun _ => rfl)).toLinearEquiv
      (EuclideanSpace.basisFun (Semantics.Qudit.Label ((QBC M region).additionalRetainedDimensions (QABC M region))) Complex l) =
      EuclideanSpace.basisFun (Semantics.Qudit.Label (QA M region).selectedDimensions) Complex
        (quditLabelRelabel (M.boundaryComplementAdditionalCoordinateEquiv region) (fun _ => rfl) l) :=
    fun l => relabel_apply_basis (q := (QBC M region).additionalRetainedDimensions (QABC M region))
      (r := (QA M region).selectedDimensions) _ _ l
  have hB : ∀ l, (M.fourFactorBCoordinateRelabel region).toLinearEquiv
      (EuclideanSpace.basisFun (Semantics.Qudit.Label (QB M region).selectedDimensions) Complex l) =
      EuclideanSpace.basisFun (Semantics.Qudit.Label ((QA M region).additionalRetainedDimensions (QAB M region))) Complex
        (quditLabelRelabel (M.fourFactorBCoordinateEquiv region) (fun _ => rfl) l) :=
    fun l => relabel_apply_basis (q := (QB M region).selectedDimensions)
      (r := (QA M region).additionalRetainedDimensions (QAB M region)) _ _ l
  have hC : ∀ l, (quditCoordinateRelabel (q := (QB M region).additionalRetainedDimensions (QBC M region))
        (r := (QAB M region).additionalRetainedDimensions (QABC M region))
        (M.boundaryAdditionalCoordinateEquiv region) (fun _ => rfl)).toLinearEquiv
      (EuclideanSpace.basisFun (Semantics.Qudit.Label ((QB M region).additionalRetainedDimensions (QBC M region))) Complex l) =
      EuclideanSpace.basisFun (Semantics.Qudit.Label ((QAB M region).additionalRetainedDimensions (QABC M region))) Complex
        (quditLabelRelabel (M.boundaryAdditionalCoordinateEquiv region) (fun _ => rfl) l) :=
    fun l => relabel_apply_basis (q := (QB M region).additionalRetainedDimensions (QBC M region))
      (r := (QAB M region).additionalRetainedDimensions (QABC M region)) _ _ l
  rw [hA, hB, hC]
  rfl

end QBAux

theorem solution
    (M : BPTCommutingProjectorModel L kappa) (region : Finset L.Site) :
    M.boundaryGlobalToFourFactorTransport region = M.fourFactorTransport region := by
  apply QBAux.ut_ext
  apply LinearEquiv.toLinearMap_injective
  apply (EuclideanSpace.basisFun (Semantics.Qudit.Label L.localDimension) Complex).toBasis.ext
  intro labels
  change (M.boundaryGlobalToFourFactorTransport region).toLinearEquiv
      (EuclideanSpace.basisFun (Semantics.Qudit.Label L.localDimension) Complex labels) =
    (M.fourFactorTransport region).toLinearEquiv
      (EuclideanSpace.basisFun (Semantics.Qudit.Label L.localDimension) Complex labels)
  rw [QBAux.boundaryGlobal_apply_basis, QBAux.fourFactorTransport_apply_basis]
