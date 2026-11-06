-- Prove2me | solution 2 for QEC.Bounds.BPTCommutingProjectorModel.firstCutProjectorMC_isSymmetric
-- status  : ACCEPTED   (prove)
-- author  : @Secousses
-- created : 2026-11-06T00:08:53.451944+00:00
-- url     : https://prove2.me/submissions/51482277-5176-4fa2-b47d-90e05d1a8552

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



theorem projector_isSelfAdjoint (M : BPTCommutingProjectorModel L kappa) (c : kappa) :
    IsSelfAdjoint (M.projector c) := by
  show star (M.projector c) = M.projector c
  rw [LinearMap.star_eq_adjoint]
  exact M.projector_self_adjoint c

theorem projectorProductOn_insert (M : BPTCommutingProjectorModel L kappa) (a : kappa)
    (s : Finset kappa) (ha : a ∉ s) :
    M.projectorProductOn (insert a s) = M.projector a * M.projectorProductOn s := by
  unfold BPTCommutingProjectorModel.projectorProductOn
  exact Finset.noncommProd_insert_of_notMem s a M.projector _ ha

theorem projector_commute_projectorProductOn (M : BPTCommutingProjectorModel L kappa)
    (c : kappa) (s : Finset kappa) :
    Commute (M.projector c) (M.projectorProductOn s) := by
  unfold BPTCommutingProjectorModel.projectorProductOn
  exact Finset.noncommProd_commute s M.projector _ _ (fun x _ => M.projector_commute c x)

theorem projectorProductOn_isSelfAdjoint (M : BPTCommutingProjectorModel L kappa)
    (s : Finset kappa) : IsSelfAdjoint (M.projectorProductOn s) := by
  induction s using Finset.induction_on with
  | empty =>
      unfold BPTCommutingProjectorModel.projectorProductOn
      simp only [Finset.noncommProd_empty]
      exact IsSelfAdjoint.one _
  | insert a s ha ih =>
      rw [projectorProductOn_insert M a s ha]
      exact ((projector_isSelfAdjoint M a).commute_iff ih).mp
        (projector_commute_projectorProductOn M a s)

theorem projectorProductOn_commute (M : BPTCommutingProjectorModel L kappa)
    (s t : Finset kappa) : Commute (M.projectorProductOn s) (M.projectorProductOn t) := by
  unfold BPTCommutingProjectorModel.projectorProductOn
  apply Finset.noncommProd_commute
  intro x _
  exact (projector_commute_projectorProductOn M x s).symm


theorem fourFactorTransport_eq_boundaryGlobal (M : BPTCommutingProjectorModel L kappa)
    (region : Finset L.Site) :
    M.fourFactorTransport region = M.boundaryGlobalToFourFactorTransport region := by
  apply ut_ext
  apply LinearEquiv.toLinearMap_injective
  apply (EuclideanSpace.basisFun (Semantics.Qudit.Label L.localDimension) Complex).toBasis.ext
  intro labels
  change (M.fourFactorTransport region).toLinearEquiv
      (EuclideanSpace.basisFun (Semantics.Qudit.Label L.localDimension) Complex labels) =
    (M.boundaryGlobalToFourFactorTransport region).toLinearEquiv
      (EuclideanSpace.basisFun (Semantics.Qudit.Label L.localDimension) Complex labels)
  rw [boundaryGlobal_apply_basis, fourFactorTransport_apply_basis]

theorem fourFactorTransport_conj_projectorBC (M : BPTCommutingProjectorModel L kappa)
    (region : Finset L.Site) :
    (M.fourFactorTransport region).conjOperator (M.projectorBC region) =
      M.fourFactorExtendBC region (M.fourFactorProjectorBCLocal region) := by
  rw [fourFactorTransport_eq_boundaryGlobal, ← projectorBC_eq]
  unfold BPTCommutingProjectorModel.boundaryGlobalToFourFactorTransport
    BPTCommutingProjectorModel.boundaryGlobalToMiddleTransport
    BPTCommutingProjectorModel.fourFactorExtendBC BPTCommutingProjectorModel.fourFactorProjectorBCLocal
  dsimp only
  simp only [conj_compose]
  have h1 : (M.regionSubsystem (M.boundary region)).registerFactorization.conjOperator
      ((M.regionSubsystem (M.boundary region)).extendLocalToRegister (M.projectorBCLocal region)) =
      TensorProduct.map (M.projectorBCLocal region)
        (1 : Semantics.Operator (M.regionSubsystem (M.boundary region)).complementSystem) := by
    exact Semantics.UnitaryTransport.conjOperator_symm_conjOperator
      (M.regionSubsystem (M.boundary region)).registerFactorization
      ((M.regionSubsystem (M.boundary region)).extendLocal (M.projectorBCLocal region))
  simp only [h1, rTensor_conj_map, lTensor_conj_map, reorder_conj_map]

theorem projectorAB_eq (M : BPTCommutingProjectorModel L kappa) (region : Finset L.Site) :
    (M.regionSubsystem region).extendLocalToRegister (M.projectorABLocal region) =
      M.projectorAB region :=
  Classical.choose_spec (M.projectorAB_supportedOnRegister_region region)

theorem fourFactorProjectorABLocal_eq (M : BPTCommutingProjectorModel L kappa)
    (region : Finset L.Site) :
    M.fourFactorProjectorABLocal region =
      ((QA M region).selectedFactorization (QAB M region) (hAAB M region)).conjOperator
        (M.projectorABLocal region) := rfl

theorem fourFactorTransport_conj_projectorAB (M : BPTCommutingProjectorModel L kappa)
    (region : Finset L.Site) :
    (M.fourFactorTransport region).conjOperator (M.projectorAB region) =
      M.fourFactorExtendAB region (M.fourFactorProjectorABLocal region) := by
  rw [fourFactorTransport_eq, ← projectorAB_eq, fourFactorProjectorABLocal_eq]
  have hN : nestedFactorizationLeft (QAB M region) (QABC M region) (hABABC M region) =
      composeUnitaryTransport (QAB M region).registerFactorization
        (unitaryLTensor (QAB M region).selectedSystem
          ((QAB M region).complementFactorization (QABC M region) (hABABC M region))) := rfl
  rw [hN]
  simp only [conj_compose]
  have h1 : (QAB M region).registerFactorization.conjOperator
      ((QAB M region).extendLocalToRegister (M.projectorABLocal region)) =
      TensorProduct.map (M.projectorABLocal region)
        (1 : Semantics.Operator (QAB M region).complementSystem) :=
    Semantics.UnitaryTransport.conjOperator_symm_conjOperator
      (QAB M region).registerFactorization
      ((QAB M region).extendLocal (M.projectorABLocal region))
  simp only [h1, lTensor_conj_map, rTensor_conj_map]
  rfl

theorem conj_injective {H K : Type u}
    [NormedAddCommGroup H] [InnerProductSpace Complex H] [Semantics.FiniteQuantumSystem H]
    [NormedAddCommGroup K] [InnerProductSpace Complex K] [Semantics.FiniteQuantumSystem K]
    (U : Semantics.UnitaryTransport H K) {A B : Semantics.Operator H}
    (h : U.conjOperator A = U.conjOperator B) : A = B := by
  have := congrArg U.symm.conjOperator h
  simpa using this

theorem map_one_injective {E D : Type u}
    [NormedAddCommGroup E] [InnerProductSpace Complex E] [Semantics.FiniteQuantumSystem E]
    [NormedAddCommGroup D] [InnerProductSpace Complex D] [Semantics.FiniteQuantumSystem D]
    [Nontrivial D] {X Y : Semantics.Operator E}
    (h : TensorProduct.map X (1 : Semantics.Operator D) =
      TensorProduct.map Y (1 : Semantics.Operator D)) : X = Y := by
  obtain ⟨d, hd⟩ := exists_ne (0 : D)
  obtain ⟨φ, hφ⟩ : ∃ φ : Module.Dual Complex D, φ d ≠ 0 := by
    by_contra hcon
    push_neg at hcon
    exact hd ((Module.forall_dual_apply_eq_zero_iff Complex d).mp hcon)
  apply LinearMap.ext
  intro e
  have h1 := congrArg (fun T => T (e ⊗ₜ[Complex] d)) h
  simp only [TensorProduct.map_tmul, Module.End.one_apply] at h1
  have h2 := congrArg
    (fun z => (TensorProduct.rid Complex E) (TensorProduct.map LinearMap.id φ z)) h1
  simp only [TensorProduct.map_tmul, LinearMap.id_apply, TensorProduct.rid_tmul] at h2
  exact smul_right_injective E hφ h2

theorem nontrivial_register {I : Type u} [Fintype I] (q : I → Nat) (hq : ∀ i, 0 < q i) :
    Nontrivial (Semantics.Qudit.QuditRegister q) := by
  haveI : Nonempty (Semantics.Qudit.Label q) := Semantics.Qudit.label_nonempty q hq
  infer_instance

theorem assoc_conj_map {H K J : Type u}
    [NormedAddCommGroup H] [InnerProductSpace Complex H] [Semantics.FiniteQuantumSystem H]
    [NormedAddCommGroup K] [InnerProductSpace Complex K] [Semantics.FiniteQuantumSystem K]
    [NormedAddCommGroup J] [InnerProductSpace Complex J] [Semantics.FiniteQuantumSystem J]
    (A : Semantics.Operator H) (B : Semantics.Operator K) (C : Semantics.Operator J) :
    (tensorAssociatorUnitary H K J).conjOperator
        (TensorProduct.map (TensorProduct.map A B) C) =
      TensorProduct.map A (TensorProduct.map B C) := by
  apply LinearMap.ext
  intro x
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul h kj =>
      induction kj using TensorProduct.induction_on with
      | zero => simp
      | tmul k j =>
          have hs : (tensorAssociatorUnitary H K J).toLinearEquiv.symm
              (h ⊗ₜ[Complex] (k ⊗ₜ[Complex] j)) = (h ⊗ₜ[Complex] k) ⊗ₜ[Complex] j :=
            tensorAssociatorUnitary_symm_apply_tmul H K J h k j
          rw [Semantics.UnitaryTransport.conjOperator_apply, hs]
          simp only [TensorProduct.map_tmul]
          exact tensorAssociatorUnitary_toLinearEquiv_apply_tmul H K J (A h) (B k) (C j)
      | add x y hx hy => simp only [TensorProduct.tmul_add, map_add, hx, hy]
  | add x y hx hy => simp only [map_add, hx, hy]

theorem firstCut_conj_map_AB (M : BPTCommutingProjectorModel L kappa) (region : Finset L.Site)
    (P : Semantics.Operator (Semantics.CompositeSystem (M.fourFactorA region) (M.fourFactorB region))) :
    (M.firstCutCoordinateTransport region).conjOperator
        (TensorProduct.map
          (TensorProduct.map P (1 : Semantics.Operator (M.fourFactorC region)))
          (1 : Semantics.Operator (M.fourFactorD region))) =
      M.fourFactorExtendAB region P := by
  unfold BPTCommutingProjectorModel.firstCutCoordinateTransport
  rw [conj_compose, assoc_conj_map]
  rw [TensorProduct.map_one]
  rfl


theorem reassoc_symm_general (M : BPTCommutingProjectorModel L kappa) (region : Finset L.Site)
    (a : M.fourFactorA region) (z : Semantics.CompositeSystem (M.fourFactorB region) (M.fourFactorC region))
    (d : M.fourFactorD region) :
    (M.fourFactorMiddleReassociate region).symm.toLinearEquiv (a ⊗ₜ[Complex] (z ⊗ₜ[Complex] d)) =
      a ⊗ₜ[Complex] (TensorProduct.assoc Complex (M.fourFactorB region) (M.fourFactorC region)
        (M.fourFactorD region) (z ⊗ₜ[Complex] d)) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul b c =>
      rw [fourFactorMiddleReassociate_symm_toLinearEquiv_apply_tmul]
      simp [TensorProduct.assoc_tmul]
  | add x y hx hy =>
      simp only [TensorProduct.add_tmul, TensorProduct.tmul_add, map_add, hx, hy]

theorem Wfc_general (M : BPTCommutingProjectorModel L kappa) (region : Finset L.Site)
    (a : M.fourFactorA region) (z : Semantics.CompositeSystem (M.fourFactorB region) (M.fourFactorC region))
    (d : M.fourFactorD region) :
    (M.firstCutCoordinateTransport region).toLinearEquiv
        (((tensorAssociatorUnitary (M.fourFactorA region) (M.fourFactorB region)
            (M.fourFactorC region)).toLinearEquiv.symm (a ⊗ₜ[Complex] z)) ⊗ₜ[Complex] d) =
      a ⊗ₜ[Complex] (TensorProduct.assoc Complex (M.fourFactorB region) (M.fourFactorC region)
        (M.fourFactorD region) (z ⊗ₜ[Complex] d)) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul b c =>
      have hs : (tensorAssociatorUnitary (M.fourFactorA region) (M.fourFactorB region)
            (M.fourFactorC region)).toLinearEquiv.symm (a ⊗ₜ[Complex] (b ⊗ₜ[Complex] c)) =
          (a ⊗ₜ[Complex] b) ⊗ₜ[Complex] c :=
        tensorAssociatorUnitary_symm_apply_tmul _ _ _ a b c
      rw [hs]
      unfold BPTCommutingProjectorModel.firstCutCoordinateTransport
      simp only [composeUnitaryTransport_toLinearEquiv_apply,
        tensorAssociatorUnitary_toLinearEquiv_apply_tmul, TensorProduct.assoc_tmul]
  | add x y hx hy =>
      simp only [TensorProduct.add_tmul, TensorProduct.tmul_add, map_add, hx, hy]

theorem firstCut_conj_liftRight (M : BPTCommutingProjectorModel L kappa) (region : Finset L.Site)
    (Q : Semantics.Operator (Semantics.CompositeSystem (M.fourFactorB region) (M.fourFactorC region))) :
    (M.firstCutCoordinateTransport region).conjOperator
        (TensorProduct.map (overlapLiftRight (A := M.fourFactorA region) Q)
          (1 : Semantics.Operator (M.fourFactorD region))) =
      M.fourFactorExtendBC region Q := by
  apply LinearMap.ext
  intro x
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul a bcd =>
      induction bcd using TensorProduct.induction_on with
      | zero => simp
      | tmul b cd =>
          induction cd using TensorProduct.induction_on with
          | zero => simp
          | tmul c d =>
              have h1 : (M.firstCutCoordinateTransport region).toLinearEquiv.symm
                  (a ⊗ₜ[Complex] (b ⊗ₜ[Complex] (c ⊗ₜ[Complex] d))) =
                  (((a ⊗ₜ[Complex] b) ⊗ₜ[Complex] c) ⊗ₜ[Complex] d) := by
                rw [LinearEquiv.symm_apply_eq]
                unfold BPTCommutingProjectorModel.firstCutCoordinateTransport
                simp only [composeUnitaryTransport_toLinearEquiv_apply,
                  tensorAssociatorUnitary_toLinearEquiv_apply_tmul]
              have h2 : (M.fourFactorMiddleReassociate region).symm.toLinearEquiv.symm
                  (a ⊗ₜ[Complex] (b ⊗ₜ[Complex] (c ⊗ₜ[Complex] d))) =
                  a ⊗ₜ[Complex] ((b ⊗ₜ[Complex] c) ⊗ₜ[Complex] d) := by
                rw [LinearEquiv.symm_apply_eq]
                exact (fourFactorMiddleReassociate_symm_toLinearEquiv_apply_tmul M region a b c d).symm
              unfold BPTCommutingProjectorModel.fourFactorExtendBC
              simp only [Semantics.UnitaryTransport.conjOperator_apply, h1, h2,
                TensorProduct.map_tmul, Module.End.one_apply, overlapLiftRight_apply_tmul]
              refine (Wfc_general M region a (Q (b ⊗ₜ[Complex] c)) d).trans ?_
              exact (reassoc_symm_general M region a (Q (b ⊗ₜ[Complex] c)) d).symm
          | add x y hx hy => simp only [TensorProduct.tmul_add, map_add, hx, hy]
      | add x y hx hy => simp only [TensorProduct.tmul_add, map_add, hx, hy]
  | add x y hx hy => simp only [map_add, hx, hy]


theorem nontrivial_tensor {E F : Type u}
    [NormedAddCommGroup E] [InnerProductSpace Complex E] [Semantics.FiniteQuantumSystem E]
    [NormedAddCommGroup F] [InnerProductSpace Complex F] [Semantics.FiniteQuantumSystem F]
    [Nontrivial E] [Nontrivial F] : Nontrivial (E ⊗[Complex] F) := by
  have hE : 0 < Module.finrank Complex E := Module.finrank_pos
  have hF : 0 < Module.finrank Complex F := Module.finrank_pos
  have h : 0 < Module.finrank Complex (E ⊗[Complex] F) := by
    rw [Module.finrank_tensorProduct]
    positivity
  exact Module.finrank_pos_iff.mp h

theorem nontrivial_fourFactor (M : BPTCommutingProjectorModel L kappa) (region : Finset L.Site) :
    Nontrivial (M.fourFactorA region) ∧ Nontrivial (M.fourFactorB region) ∧
      Nontrivial (M.fourFactorC region) ∧ Nontrivial (M.fourFactorD region) :=
  ⟨nontrivial_register _ (fun _ => L.localDimension_positive _),
    nontrivial_register _ (fun _ => L.localDimension_positive _),
    nontrivial_register _ (fun _ => L.localDimension_positive _),
    nontrivial_register _ (fun _ => L.localDimension_positive _)⟩

theorem one_map_injective {E D : Type u}
    [NormedAddCommGroup E] [InnerProductSpace Complex E] [Semantics.FiniteQuantumSystem E]
    [NormedAddCommGroup D] [InnerProductSpace Complex D] [Semantics.FiniteQuantumSystem D]
    [Nontrivial E] {X Y : Semantics.Operator D}
    (h : TensorProduct.map (1 : Semantics.Operator E) X =
      TensorProduct.map (1 : Semantics.Operator E) Y) : X = Y := by
  obtain ⟨e, he⟩ := exists_ne (0 : E)
  obtain ⟨φ, hφ⟩ : ∃ φ : Module.Dual Complex E, φ e ≠ 0 := by
    by_contra hcon
    push_neg at hcon
    exact he ((Module.forall_dual_apply_eq_zero_iff Complex e).mp hcon)
  apply LinearMap.ext
  intro x
  have h1 := congrArg (fun T => T (e ⊗ₜ[Complex] x)) h
  simp only [TensorProduct.map_tmul, Module.End.one_apply] at h1
  have h2 := congrArg
    (fun z => (TensorProduct.lid Complex D) (TensorProduct.map φ LinearMap.id z)) h1
  simp only [TensorProduct.map_tmul, LinearMap.id_apply, TensorProduct.lid_tmul] at h2
  exact smul_right_injective D hφ h2

theorem projectorProductOn_idem (M : BPTCommutingProjectorModel L kappa) (s : Finset kappa) :
    M.projectorProductOn s * M.projectorProductOn s = M.projectorProductOn s := by
  induction s using Finset.induction_on with
  | empty =>
      unfold BPTCommutingProjectorModel.projectorProductOn
      simp only [Finset.noncommProd_empty, mul_one]
  | insert a s ha ih =>
      rw [projectorProductOn_insert M a s ha]
      have hp : IsIdempotentElem (M.projector a) := M.projector_idempotent a
      exact IsIdempotentElem.mul_of_commute (projector_commute_projectorProductOn M a s) hp ih

theorem extAB_eq (M : BPTCommutingProjectorModel L kappa) (region : Finset L.Site)
    (P : Semantics.Operator (Semantics.CompositeSystem (M.fourFactorA region) (M.fourFactorB region))) :
    M.fourFactorExtendAB region P =
      (tensorAssociatorUnitary (M.fourFactorA region) (M.fourFactorB region)
        (Semantics.CompositeSystem (M.fourFactorC region) (M.fourFactorD region))).conjOperator
        (TensorProduct.map P (1 : Semantics.Operator
          (Semantics.CompositeSystem (M.fourFactorC region) (M.fourFactorD region)))) := rfl

theorem extAB_mul (M : BPTCommutingProjectorModel L kappa) (region : Finset L.Site)
    (P Q : Semantics.Operator (Semantics.CompositeSystem (M.fourFactorA region) (M.fourFactorB region))) :
    M.fourFactorExtendAB region (P * Q) =
      M.fourFactorExtendAB region P * M.fourFactorExtendAB region Q := by
  have h : TensorProduct.map (P * Q) (1 : Semantics.Operator
      (Semantics.CompositeSystem (M.fourFactorC region) (M.fourFactorD region))) =
      TensorProduct.map P 1 * TensorProduct.map Q 1 := by
    rw [← TensorProduct.map_mul, mul_one]
  simp only [extAB_eq, h, Semantics.UnitaryTransport.conjOperator_mul]

theorem extAB_adjoint (M : BPTCommutingProjectorModel L kappa) (region : Finset L.Site)
    (P : Semantics.Operator (Semantics.CompositeSystem (M.fourFactorA region) (M.fourFactorB region))) :
    LinearMap.adjoint (M.fourFactorExtendAB region P) =
      M.fourFactorExtendAB region (LinearMap.adjoint P) := by
  simp only [extAB_eq, Semantics.UnitaryTransport.conjOperator_adjoint, TensorProduct.adjoint_map]
  simp

theorem extAB_injective (M : BPTCommutingProjectorModel L kappa) (region : Finset L.Site) :
    Function.Injective (M.fourFactorExtendAB region) := by
  obtain ⟨_, _, hC, hD⟩ := nontrivial_fourFactor M region
  haveI := hC
  haveI := hD
  haveI : Nontrivial (Semantics.CompositeSystem (M.fourFactorC region) (M.fourFactorD region)) :=
    nontrivial_tensor
  intro P Q h
  rw [extAB_eq, extAB_eq] at h
  exact map_one_injective (conj_injective _ h)

theorem extBC_mul (M : BPTCommutingProjectorModel L kappa) (region : Finset L.Site)
    (P Q : Semantics.Operator (Semantics.CompositeSystem (M.fourFactorB region) (M.fourFactorC region))) :
    M.fourFactorExtendBC region (P * Q) =
      M.fourFactorExtendBC region P * M.fourFactorExtendBC region Q := by
  have h : TensorProduct.map (1 : Semantics.Operator (M.fourFactorA region))
        (TensorProduct.map (P * Q) (1 : Semantics.Operator (M.fourFactorD region))) =
      TensorProduct.map 1 (TensorProduct.map P 1) * TensorProduct.map 1 (TensorProduct.map Q 1) := by
    rw [← TensorProduct.map_mul, ← TensorProduct.map_mul, mul_one, mul_one]
  unfold BPTCommutingProjectorModel.fourFactorExtendBC
  simp only [h, Semantics.UnitaryTransport.conjOperator_mul]

theorem extBC_adjoint (M : BPTCommutingProjectorModel L kappa) (region : Finset L.Site)
    (P : Semantics.Operator (Semantics.CompositeSystem (M.fourFactorB region) (M.fourFactorC region))) :
    LinearMap.adjoint (M.fourFactorExtendBC region P) =
      M.fourFactorExtendBC region (LinearMap.adjoint P) := by
  unfold BPTCommutingProjectorModel.fourFactorExtendBC
  simp only [Semantics.UnitaryTransport.conjOperator_adjoint, TensorProduct.adjoint_map]
  simp

theorem extBC_injective (M : BPTCommutingProjectorModel L kappa) (region : Finset L.Site) :
    Function.Injective (M.fourFactorExtendBC region) := by
  obtain ⟨hA, _, _, hD⟩ := nontrivial_fourFactor M region
  haveI := hA
  haveI := hD
  intro P Q h
  unfold BPTCommutingProjectorModel.fourFactorExtendBC at h
  exact map_one_injective (one_map_injective (conj_injective _ h))


theorem projectorAB_adjoint (M : BPTCommutingProjectorModel L kappa) (region : Finset L.Site) :
    LinearMap.adjoint (M.projectorAB region) = M.projectorAB region := by
  have h := projectorProductOn_isSelfAdjoint M (M.interiorChecks region)
  have h' : star (M.projectorAB region) = M.projectorAB region := h
  rwa [LinearMap.star_eq_adjoint] at h'

theorem projectorBC_adjoint (M : BPTCommutingProjectorModel L kappa) (region : Finset L.Site) :
    LinearMap.adjoint (M.projectorBC region) = M.projectorBC region := by
  have h := projectorProductOn_isSelfAdjoint M (M.boundaryChecks region)
  have h' : star (M.projectorBC region) = M.projectorBC region := h
  rwa [LinearMap.star_eq_adjoint] at h'

theorem ABl_props (M : BPTCommutingProjectorModel L kappa) (region : Finset L.Site) :
    LinearMap.adjoint (M.fourFactorProjectorABLocal region) = M.fourFactorProjectorABLocal region ∧
    M.fourFactorProjectorABLocal region * M.fourFactorProjectorABLocal region =
      M.fourFactorProjectorABLocal region := by
  have hT := fourFactorTransport_conj_projectorAB M region
  have hid : M.projectorAB region * M.projectorAB region = M.projectorAB region :=
    projectorProductOn_idem M _
  constructor
  · apply extAB_injective M region
    exact ((extAB_adjoint M region _).symm.trans (congrArg LinearMap.adjoint hT.symm)).trans
      ((Semantics.UnitaryTransport.conjOperator_adjoint _ _).trans
        ((congrArg (M.fourFactorTransport region).conjOperator (projectorAB_adjoint M region)).trans hT))
  · apply extAB_injective M region
    exact (extAB_mul M region _ _).trans
      ((congrArg₂ (· * ·) hT.symm hT.symm).trans
        ((Semantics.UnitaryTransport.conjOperator_mul _ _ _).symm.trans
          ((congrArg (M.fourFactorTransport region).conjOperator hid).trans hT)))

theorem BCl_props (M : BPTCommutingProjectorModel L kappa) (region : Finset L.Site) :
    LinearMap.adjoint (M.fourFactorProjectorBCLocal region) = M.fourFactorProjectorBCLocal region ∧
    M.fourFactorProjectorBCLocal region * M.fourFactorProjectorBCLocal region =
      M.fourFactorProjectorBCLocal region := by
  have hT := fourFactorTransport_conj_projectorBC M region
  have hid : M.projectorBC region * M.projectorBC region = M.projectorBC region :=
    projectorProductOn_idem M _
  constructor
  · apply extBC_injective M region
    exact ((extBC_adjoint M region _).symm.trans (congrArg LinearMap.adjoint hT.symm)).trans
      ((Semantics.UnitaryTransport.conjOperator_adjoint _ _).trans
        ((congrArg (M.fourFactorTransport region).conjOperator (projectorBC_adjoint M region)).trans hT))
  · apply extBC_injective M region
    exact (extBC_mul M region _ _).trans
      ((congrArg₂ (· * ·) hT.symm hT.symm).trans
        ((Semantics.UnitaryTransport.conjOperator_mul _ _ _).symm.trans
          ((congrArg (M.fourFactorTransport region).conjOperator hid).trans hT)))

theorem firstCut_commute (M : BPTCommutingProjectorModel L kappa) (region : Finset L.Site) :
    Commute (TensorProduct.map (M.fourFactorProjectorABLocal region)
        (1 : Semantics.Operator (M.fourFactorC region)))
      (overlapLiftRight (A := M.fourFactorA region) (M.fourFactorProjectorBCLocal region)) := by
  obtain ⟨_, _, _, hD⟩ := nontrivial_fourFactor M region
  haveI := hD
  have hX := (firstCut_conj_map_AB M region (M.fourFactorProjectorABLocal region)).trans
    (fourFactorTransport_conj_projectorAB M region).symm
  have hY := (firstCut_conj_liftRight M region (M.fourFactorProjectorBCLocal region)).trans
    (fourFactorTransport_conj_projectorBC M region).symm
  have hmul : ∀ Z Z' : Semantics.Operator (Semantics.CompositeSystem
      (Semantics.CompositeSystem (M.fourFactorA region) (M.fourFactorB region)) (M.fourFactorC region)),
      (M.firstCutCoordinateTransport region).conjOperator
        (TensorProduct.map (Z * Z') (1 : Semantics.Operator (M.fourFactorD region))) =
      (M.firstCutCoordinateTransport region).conjOperator
        (TensorProduct.map Z (1 : Semantics.Operator (M.fourFactorD region))) *
      (M.firstCutCoordinateTransport region).conjOperator
        (TensorProduct.map Z' (1 : Semantics.Operator (M.fourFactorD region))) := by
    intro Z Z'
    have h : TensorProduct.map (Z * Z') (1 : Semantics.Operator (M.fourFactorD region)) =
        TensorProduct.map Z 1 * TensorProduct.map Z' 1 := by
      rw [← TensorProduct.map_mul, mul_one]
    exact (congrArg _ h).trans (Semantics.UnitaryTransport.conjOperator_mul _ _ _)
  have hc : Commute (M.projectorAB region) (M.projectorBC region) :=
    projectorProductOn_commute M _ _
  have hcT : (M.fourFactorTransport region).conjOperator (M.projectorAB region) *
      (M.fourFactorTransport region).conjOperator (M.projectorBC region) =
      (M.fourFactorTransport region).conjOperator (M.projectorBC region) *
      (M.fourFactorTransport region).conjOperator (M.projectorAB region) := by
    exact (Semantics.UnitaryTransport.conjOperator_mul _ _ _).symm.trans
      ((congrArg (M.fourFactorTransport region).conjOperator hc.eq).trans
        (Semantics.UnitaryTransport.conjOperator_mul _ _ _))
  have key := (hmul (TensorProduct.map (M.fourFactorProjectorABLocal region)
        (1 : Semantics.Operator (M.fourFactorC region)))
      (overlapLiftRight (A := M.fourFactorA region) (M.fourFactorProjectorBCLocal region))).trans
    ((congrArg₂ (· * ·) hX hY).trans (hcT.trans ((congrArg₂ (· * ·) hY.symm hX.symm).trans
      (hmul (overlapLiftRight (A := M.fourFactorA region) (M.fourFactorProjectorBCLocal region))
        (TensorProduct.map (M.fourFactorProjectorABLocal region)
          (1 : Semantics.Operator (M.fourFactorC region)))).symm)))
  exact map_one_injective (conj_injective _ key)


theorem isSelfAdjoint_of_adjoint {E : Type u}
    [NormedAddCommGroup E] [InnerProductSpace Complex E] [Semantics.FiniteQuantumSystem E]
    (T : Semantics.Operator E) (h : LinearMap.adjoint T = T) : IsSelfAdjoint T := by
  show star T = T
  rw [LinearMap.star_eq_adjoint]
  exact h

theorem XX_props (M : BPTCommutingProjectorModel L kappa) (region : Finset L.Site) :
    LinearMap.adjoint (TensorProduct.map (M.fourFactorProjectorABLocal region)
        (1 : Semantics.Operator (M.fourFactorC region))) =
      TensorProduct.map (M.fourFactorProjectorABLocal region)
        (1 : Semantics.Operator (M.fourFactorC region)) ∧
    IsIdempotentElem (TensorProduct.map (M.fourFactorProjectorABLocal region)
        (1 : Semantics.Operator (M.fourFactorC region))) := by
  have hABl := ABl_props M region
  constructor
  · simp only [TensorProduct.adjoint_map, hABl.1]
    simp
  · show _ * _ = _
    rw [← TensorProduct.map_mul, hABl.2, mul_one]

theorem YY_props (M : BPTCommutingProjectorModel L kappa) (region : Finset L.Site) :
    LinearMap.adjoint (overlapLiftRight (A := M.fourFactorA region)
        (M.fourFactorProjectorBCLocal region)) =
      overlapLiftRight (A := M.fourFactorA region) (M.fourFactorProjectorBCLocal region) ∧
    IsIdempotentElem (overlapLiftRight (A := M.fourFactorA region)
        (M.fourFactorProjectorBCLocal region)) := by
  have hBCl := BCl_props M region
  constructor
  · unfold overlapLiftRight
    simp only [Semantics.UnitaryTransport.conjOperator_adjoint, TensorProduct.adjoint_map, hBCl.1]
    simp
  · unfold overlapLiftRight
    show _ * _ = _
    have h : TensorProduct.map (1 : Semantics.Operator (M.fourFactorA region))
        (M.fourFactorProjectorBCLocal region) *
        TensorProduct.map (1 : Semantics.Operator (M.fourFactorA region))
        (M.fourFactorProjectorBCLocal region) =
        TensorProduct.map (1 : Semantics.Operator (M.fourFactorA region))
        (M.fourFactorProjectorBCLocal region) := by
      rw [← TensorProduct.map_mul, hBCl.2, mul_one]
    exact (Semantics.UnitaryTransport.conjOperator_mul _ _ _).symm.trans
      ((congrArg _ h))


end QBAux

theorem solution
    (M : BPTCommutingProjectorModel L kappa) (region : Finset L.Site) :
    (M.firstCutProjectorMC region).IsSymmetric := by
  have hXad := (QBAux.XX_props M region).1
  have hYad := (QBAux.YY_props M region).1
  have hc := QBAux.firstCut_commute M region
  have hX := QBAux.isSelfAdjoint_of_adjoint _ hXad
  have hY := QBAux.isSelfAdjoint_of_adjoint _ hYad
  apply (LinearMap.isSymmetric_iff_isSelfAdjoint _).mpr
  exact (IsSelfAdjoint.commute_iff hX hY).mp hc
