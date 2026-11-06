-- Prove2me | solution 2 for QEC.Bounds.BPTCommutingProjectorModel.fourFactorTransport_conj_projectorBC
-- status  : ACCEPTED   (prove)
-- author  : @Secousses
-- created : 2026-11-06T00:09:08.694662+00:00
-- url     : https://prove2.me/submissions/697f6708-ea22-4726-85ed-00a5ff9bfeb3

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


theorem unitaryRTensor_symm_apply_tmul {H K : Type u}
    [NormedAddCommGroup H] [InnerProductSpace Complex H] [Semantics.FiniteQuantumSystem H]
    [NormedAddCommGroup K] [InnerProductSpace Complex K] [Semantics.FiniteQuantumSystem K]
    (U : Semantics.UnitaryTransport H K) (J : Type u)
    [NormedAddCommGroup J] [InnerProductSpace Complex J] [Semantics.FiniteQuantumSystem J]
    (k : K) (j : J) :
    (unitaryRTensor U J).toLinearEquiv.symm (k ⊗ₜ[Complex] j) =
      U.toLinearEquiv.symm k ⊗ₜ[Complex] j := by
  rw [LinearEquiv.symm_apply_eq]
  simp [unitaryRTensor_toLinearEquiv_apply_tmul]

theorem unitaryLTensor_symm_apply_tmul {H K : Type u}
    [NormedAddCommGroup H] [InnerProductSpace Complex H] [Semantics.FiniteQuantumSystem H]
    [NormedAddCommGroup K] [InnerProductSpace Complex K] [Semantics.FiniteQuantumSystem K]
    (I : Type u) [NormedAddCommGroup I] [InnerProductSpace Complex I]
    [Semantics.FiniteQuantumSystem I] (U : Semantics.UnitaryTransport H K)
    (i : I) (k : K) :
    (unitaryLTensor I U).toLinearEquiv.symm (i ⊗ₜ[Complex] k) =
      i ⊗ₜ[Complex] U.toLinearEquiv.symm k := by
  rw [LinearEquiv.symm_apply_eq]
  simp [unitaryLTensor_toLinearEquiv_apply_tmul]

theorem rTensor_conj_map {H K : Type u}
    [NormedAddCommGroup H] [InnerProductSpace Complex H] [Semantics.FiniteQuantumSystem H]
    [NormedAddCommGroup K] [InnerProductSpace Complex K] [Semantics.FiniteQuantumSystem K]
    (U : Semantics.UnitaryTransport H K) (J : Type u)
    [NormedAddCommGroup J] [InnerProductSpace Complex J] [Semantics.FiniteQuantumSystem J]
    (A : Semantics.Operator H) :
    (unitaryRTensor U J).conjOperator (TensorProduct.map A (1 : Semantics.Operator J)) =
      TensorProduct.map (U.conjOperator A) (1 : Semantics.Operator J) := by
  apply LinearMap.ext
  intro x
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul k j =>
      rw [Semantics.UnitaryTransport.conjOperator_apply, unitaryRTensor_symm_apply_tmul]
      simp [unitaryRTensor_toLinearEquiv_apply_tmul]
  | add x y hx hy => simp only [map_add, hx, hy]

theorem lTensor_conj_map {H K : Type u}
    [NormedAddCommGroup H] [InnerProductSpace Complex H] [Semantics.FiniteQuantumSystem H]
    [NormedAddCommGroup K] [InnerProductSpace Complex K] [Semantics.FiniteQuantumSystem K]
    (I : Type u) [NormedAddCommGroup I] [InnerProductSpace Complex I]
    [Semantics.FiniteQuantumSystem I] (U : Semantics.UnitaryTransport H K)
    (A : Semantics.Operator I) :
    (unitaryLTensor I U).conjOperator (TensorProduct.map A (1 : Semantics.Operator H)) =
      TensorProduct.map A (1 : Semantics.Operator K) := by
  apply LinearMap.ext
  intro x
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul i k =>
      rw [Semantics.UnitaryTransport.conjOperator_apply, unitaryLTensor_symm_apply_tmul]
      simp [unitaryLTensor_toLinearEquiv_apply_tmul]
  | add x y hx hy => simp only [map_add, hx, hy]

theorem reorder_apply_general (A B C D : Type u)
    [NormedAddCommGroup A] [InnerProductSpace Complex A] [Semantics.FiniteQuantumSystem A]
    [NormedAddCommGroup B] [InnerProductSpace Complex B] [Semantics.FiniteQuantumSystem B]
    [NormedAddCommGroup C] [InnerProductSpace Complex C] [Semantics.FiniteQuantumSystem C]
    [NormedAddCommGroup D] [InnerProductSpace Complex D] [Semantics.FiniteQuantumSystem D]
    (z : Semantics.CompositeSystem B C) (a : A) (d : D) :
    (boundaryToMiddleReorder A B C D).toLinearEquiv (z ⊗ₜ[Complex] (a ⊗ₜ[Complex] d)) =
      a ⊗ₜ[Complex] (z ⊗ₜ[Complex] d) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul b c => exact boundaryToMiddleReorder_toLinearEquiv_apply_tmul A B C D a b c d
  | add x y hx hy => simp only [TensorProduct.add_tmul, TensorProduct.tmul_add, map_add, hx, hy]

theorem reorder_conj_map (A B C D : Type u)
    [NormedAddCommGroup A] [InnerProductSpace Complex A] [Semantics.FiniteQuantumSystem A]
    [NormedAddCommGroup B] [InnerProductSpace Complex B] [Semantics.FiniteQuantumSystem B]
    [NormedAddCommGroup C] [InnerProductSpace Complex C] [Semantics.FiniteQuantumSystem C]
    [NormedAddCommGroup D] [InnerProductSpace Complex D] [Semantics.FiniteQuantumSystem D]
    (Y : Semantics.Operator (Semantics.CompositeSystem B C)) :
    (boundaryToMiddleReorder A B C D).conjOperator
        (TensorProduct.map Y (1 : Semantics.Operator (Semantics.CompositeSystem A D))) =
      TensorProduct.map (1 : Semantics.Operator A)
        (TensorProduct.map Y (1 : Semantics.Operator D)) := by
  have key : ∀ v, (boundaryToMiddleReorder A B C D).toLinearEquiv
      (TensorProduct.map Y (1 : Semantics.Operator (Semantics.CompositeSystem A D)) v) =
      TensorProduct.map (1 : Semantics.Operator A)
        (TensorProduct.map Y (1 : Semantics.Operator D))
        ((boundaryToMiddleReorder A B C D).toLinearEquiv v) := by
    intro v
    induction v using TensorProduct.induction_on with
    | zero => simp
    | tmul z u =>
        induction u using TensorProduct.induction_on with
        | zero => simp
        | tmul a d =>
            simp only [TensorProduct.map_tmul, Module.End.one_apply, reorder_apply_general]
        | add x y hx hy => simp only [TensorProduct.tmul_add, map_add, hx, hy]
    | add x y hx hy => simp only [map_add, hx, hy]
  apply LinearMap.ext
  intro w
  rw [Semantics.UnitaryTransport.conjOperator_apply, key]
  simp

theorem conj_compose {H K J : Type u}
    [NormedAddCommGroup H] [InnerProductSpace Complex H] [Semantics.FiniteQuantumSystem H]
    [NormedAddCommGroup K] [InnerProductSpace Complex K] [Semantics.FiniteQuantumSystem K]
    [NormedAddCommGroup J] [InnerProductSpace Complex J] [Semantics.FiniteQuantumSystem J]
    (U : Semantics.UnitaryTransport H K) (V : Semantics.UnitaryTransport K J)
    (A : Semantics.Operator H) :
    (composeUnitaryTransport U V).conjOperator A = V.conjOperator (U.conjOperator A) := rfl

theorem projectorBC_eq (M : BPTCommutingProjectorModel L kappa) (region : Finset L.Site) :
    (M.regionSubsystem (M.boundary region)).extendLocalToRegister (M.projectorBCLocal region) =
      M.projectorBC region :=
  Classical.choose_spec (M.projectorBC_supportedOnRegister_boundary region)

end QBAux

theorem solution
    (M : BPTCommutingProjectorModel L kappa) (region : Finset L.Site) :
    (M.fourFactorTransport region).conjOperator (M.projectorBC region) =
      M.fourFactorExtendBC region (M.fourFactorProjectorBCLocal region) := by
  have hT : M.fourFactorTransport region = M.boundaryGlobalToFourFactorTransport region := by
    apply QBAux.ut_ext
    apply LinearEquiv.toLinearMap_injective
    apply (EuclideanSpace.basisFun (Semantics.Qudit.Label L.localDimension) Complex).toBasis.ext
    intro labels
    change (M.fourFactorTransport region).toLinearEquiv
        (EuclideanSpace.basisFun (Semantics.Qudit.Label L.localDimension) Complex labels) =
      (M.boundaryGlobalToFourFactorTransport region).toLinearEquiv
        (EuclideanSpace.basisFun (Semantics.Qudit.Label L.localDimension) Complex labels)
    rw [QBAux.boundaryGlobal_apply_basis, QBAux.fourFactorTransport_apply_basis]
  rw [hT, ← QBAux.projectorBC_eq]
  unfold BPTCommutingProjectorModel.boundaryGlobalToFourFactorTransport
    BPTCommutingProjectorModel.boundaryGlobalToMiddleTransport
    BPTCommutingProjectorModel.fourFactorExtendBC BPTCommutingProjectorModel.fourFactorProjectorBCLocal
  dsimp only
  simp only [QBAux.conj_compose]
  have h1 : (M.regionSubsystem (M.boundary region)).registerFactorization.conjOperator
      ((M.regionSubsystem (M.boundary region)).extendLocalToRegister (M.projectorBCLocal region)) =
      TensorProduct.map (M.projectorBCLocal region)
        (1 : Semantics.Operator (M.regionSubsystem (M.boundary region)).complementSystem) := by
    exact Semantics.UnitaryTransport.conjOperator_symm_conjOperator
      (M.regionSubsystem (M.boundary region)).registerFactorization
      ((M.regionSubsystem (M.boundary region)).extendLocal (M.projectorBCLocal region))
  simp only [h1, QBAux.rTensor_conj_map, QBAux.lTensor_conj_map, QBAux.reorder_conj_map]
