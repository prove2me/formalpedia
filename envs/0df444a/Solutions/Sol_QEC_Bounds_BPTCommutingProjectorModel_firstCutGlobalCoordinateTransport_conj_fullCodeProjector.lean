-- Prove2me | solution 1 for QEC.Bounds.BPTCommutingProjectorModel.firstCutGlobalCoordinateTransport_conj_fullCodeProjector
-- status  : ACCEPTED   (prove)
-- author  : @Secousses
-- created : 2026-11-06T01:56:33.892529+00:00
-- url     : https://prove2.me/submissions/600ad13d-4bfa-4b02-8845-1f7d61c88515

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


theorem projectorProductOn_fixed (M : BPTCommutingProjectorModel L kappa) (s : Finset kappa)
    (v : L.Register) (hv : ∀ c, M.projector c v = v) : M.projectorProductOn s v = v := by
  induction s using Finset.induction_on with
  | empty =>
      unfold BPTCommutingProjectorModel.projectorProductOn
      simp only [Finset.noncommProd_empty]
      rfl
  | insert a s ha ih =>
      rw [projectorProductOn_insert M a s ha]
      show M.projector a (M.projectorProductOn s v) = v
      rw [ih, hv a]

theorem projector_mul_projectorProductOn (M : BPTCommutingProjectorModel L kappa) (c : kappa)
    (s : Finset kappa) (hc : c ∈ s) :
    M.projector c * M.projectorProductOn s = M.projectorProductOn s := by
  induction s using Finset.induction_on with
  | empty => exact absurd hc (Finset.notMem_empty c)
  | insert a s ha ih =>
      rw [projectorProductOn_insert M a s ha]
      rcases Finset.mem_insert.mp hc with h | hc'
      · subst h
        rw [← mul_assoc]
        have hp : IsIdempotentElem (M.projector c) := M.projector_idempotent c
        rw [hp.eq]
      · rw [← mul_assoc, (M.projector_commute c a).eq, mul_assoc, ih hc']

theorem projectorProductOn_univ_eq (M : BPTCommutingProjectorModel L kappa) :
    M.projectorProductOn Finset.univ = M.fullCodeProjector := by
  apply LinearMap.ext
  intro v
  have hmem : M.projectorProductOn Finset.univ v ∈ M.codeSpace.carrier := by
    show ∀ c, M.projector c (M.projectorProductOn Finset.univ v) = M.projectorProductOn Finset.univ v
    intro c
    have h := congrArg (fun T => T v)
      (projector_mul_projectorProductOn M c Finset.univ (Finset.mem_univ c))
    simp only [Module.End.mul_apply] at h
    exact h
  have hsa : LinearMap.adjoint (M.projectorProductOn Finset.univ) = M.projectorProductOn Finset.univ := by
    have h := projectorProductOn_isSelfAdjoint M Finset.univ
    have h' : star (M.projectorProductOn Finset.univ) = M.projectorProductOn Finset.univ := h
    rwa [LinearMap.star_eq_adjoint] at h'
  have hinner : ∀ w ∈ M.codeSpace.carrier,
      inner Complex (v - M.projectorProductOn Finset.univ v) w = 0 := by
    intro w hw
    have hwfix : ∀ c, M.projector c w = w := fun c => hw c
    have hPw : M.projectorProductOn Finset.univ w = w := projectorProductOn_fixed M _ w hwfix
    rw [inner_sub_left]
    have : inner Complex (M.projectorProductOn Finset.univ v) w = inner Complex v w := by
      calc inner Complex (M.projectorProductOn Finset.univ v) w
          = inner Complex (LinearMap.adjoint (M.projectorProductOn Finset.univ) v) w := by rw [hsa]
        _ = inner Complex v (M.projectorProductOn Finset.univ w) :=
          LinearMap.adjoint_inner_left _ _ _
        _ = inner Complex v w := by rw [hPw]
    rw [this, sub_self]
  exact (Submodule.eq_starProjection_of_mem_of_inner_eq_zero hmem hinner).symm


theorem interiorChecks_disjoint_exteriorChecks (M : BPTCommutingProjectorModel L kappa)
    (region : Finset L.Site) :
    Disjoint (M.interiorChecks region) (M.exteriorChecks region) := by
  rw [Finset.disjoint_left]
  intro c hI hE
  have h1 := M.support_subset_region_of_mem_interiorChecks region hI
  have h2 := M.support_subset_complement_of_mem_exteriorChecks region hE
  obtain ⟨s, hs⟩ := (Finset.mem_filter.mp hI).2
  have hs1 := (Finset.mem_inter.mp hs).1
  exact (Finset.mem_compl.mp (h2 hs1)) (h1 hs1)

theorem projectorProductOn_union (M : BPTCommutingProjectorModel L kappa) {s t : Finset kappa}
    (h : Disjoint s t) :
    M.projectorProductOn (s ∪ t) = M.projectorProductOn s * M.projectorProductOn t := by
  unfold BPTCommutingProjectorModel.projectorProductOn
  exact Finset.noncommProd_union_of_disjoint h _ _

theorem projectorProductOn_univ_split (M : BPTCommutingProjectorModel L kappa)
    (region : Finset L.Site) :
    M.projectorProductOn Finset.univ =
      M.projectorAB region * (M.projectorBC region * M.projectorCD region) := by
  have hU : M.projectorProductOn Finset.univ =
      M.projectorProductOn ((M.interiorChecks region ∪ M.exteriorChecks region) ∪
        (Finset.univ \ (M.interiorChecks region ∪ M.exteriorChecks region))) :=
    congrArg _ (Finset.union_sdiff_of_subset (Finset.subset_univ _)).symm
  rw [hU, projectorProductOn_union M Finset.disjoint_sdiff,
    projectorProductOn_union M (interiorChecks_disjoint_exteriorChecks M region)]
  have hc := projectorProductOn_commute M (M.exteriorChecks region)
    (Finset.univ \ (M.interiorChecks region ∪ M.exteriorChecks region))
  show M.projectorProductOn (M.interiorChecks region) * M.projectorProductOn (M.exteriorChecks region) *
    M.projectorProductOn (Finset.univ \ (M.interiorChecks region ∪ M.exteriorChecks region)) =
    M.projectorProductOn (M.interiorChecks region) * (M.projectorProductOn
      (Finset.univ \ (M.interiorChecks region ∪ M.exteriorChecks region)) *
      M.projectorProductOn (M.exteriorChecks region))
  rw [mul_assoc, hc.eq]

theorem fullCodeProjector_split (M : BPTCommutingProjectorModel L kappa)
    (region : Finset L.Site) :
    M.fullCodeProjector = M.projectorAB region * (M.projectorBC region * M.projectorCD region) :=
  (projectorProductOn_univ_eq M).symm.trans (projectorProductOn_univ_split M region)


theorem swap_conj_map {H K : Type u}
    [NormedAddCommGroup H] [InnerProductSpace Complex H] [Semantics.FiniteQuantumSystem H]
    [NormedAddCommGroup K] [InnerProductSpace Complex K] [Semantics.FiniteQuantumSystem K]
    (A : Semantics.Operator H) :
    (tensorSwapUnitary H K).conjOperator (TensorProduct.map A (1 : Semantics.Operator K)) =
      TensorProduct.map (1 : Semantics.Operator K) A := by
  apply LinearMap.ext
  intro x
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul k h =>
      have hs : (tensorSwapUnitary H K).toLinearEquiv.symm (k ⊗ₜ[Complex] h) =
          h ⊗ₜ[Complex] k := by
        rw [LinearEquiv.symm_apply_eq]
        exact (tensorSwapUnitary_toLinearEquiv_apply_tmul H K h k).symm
      rw [Semantics.UnitaryTransport.conjOperator_apply, hs]
      simp only [TensorProduct.map_tmul, Module.End.one_apply]
      exact tensorSwapUnitary_toLinearEquiv_apply_tmul H K (A h) k
  | add x y hx hy => simp only [map_add, hx, hy]

theorem rTensor_conj_map_gen {H K : Type u}
    [NormedAddCommGroup H] [InnerProductSpace Complex H] [Semantics.FiniteQuantumSystem H]
    [NormedAddCommGroup K] [InnerProductSpace Complex K] [Semantics.FiniteQuantumSystem K]
    (U : Semantics.UnitaryTransport H K) (J : Type u)
    [NormedAddCommGroup J] [InnerProductSpace Complex J] [Semantics.FiniteQuantumSystem J]
    (A : Semantics.Operator H) (B : Semantics.Operator J) :
    (unitaryRTensor U J).conjOperator (TensorProduct.map A B) =
      TensorProduct.map (U.conjOperator A) B := by
  apply LinearMap.ext
  intro x
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul k j =>
      rw [Semantics.UnitaryTransport.conjOperator_apply, unitaryRTensor_symm_apply_tmul]
      simp [unitaryRTensor_toLinearEquiv_apply_tmul]
  | add x y hx hy => simp only [map_add, hx, hy]

theorem lTensor_conj_map_one {H K : Type u}
    [NormedAddCommGroup H] [InnerProductSpace Complex H] [Semantics.FiniteQuantumSystem H]
    [NormedAddCommGroup K] [InnerProductSpace Complex K] [Semantics.FiniteQuantumSystem K]
    (I : Type u) [NormedAddCommGroup I] [InnerProductSpace Complex I]
    [Semantics.FiniteQuantumSystem I] (U : Semantics.UnitaryTransport H K)
    (Z : Semantics.Operator H) :
    (unitaryLTensor I U).conjOperator (TensorProduct.map (1 : Semantics.Operator I) Z) =
      TensorProduct.map (1 : Semantics.Operator I) (U.conjOperator Z) := by
  apply LinearMap.ext
  intro x
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul i k =>
      rw [Semantics.UnitaryTransport.conjOperator_apply, unitaryLTensor_symm_apply_tmul]
      simp [unitaryLTensor_toLinearEquiv_apply_tmul]
  | add x y hx hy => simp only [map_add, hx, hy]

theorem complementPartition_eq (M : BPTCommutingProjectorModel L kappa) (region : Finset L.Site) :
    M.complementPartitionTransport region = (M.regionSubsystem region).registerFactorization := by
  apply ut_ext
  apply LinearEquiv.toLinearMap_injective
  apply (EuclideanSpace.basisFun (Semantics.Qudit.Label L.localDimension) Complex).toBasis.ext
  intro labels
  change (M.complementPartitionTransport region).toLinearEquiv
      (EuclideanSpace.basisFun (Semantics.Qudit.Label L.localDimension) Complex labels) =
    (M.regionSubsystem region).registerFactorization.toLinearEquiv
      (EuclideanSpace.basisFun (Semantics.Qudit.Label L.localDimension) Complex labels)
  have hR1 : ∀ l, (M.regionComplementCoordinateRelabel region).toLinearEquiv
      (EuclideanSpace.basisFun (Semantics.Qudit.Label
        (M.regionSubsystem regionᶜ).selectedDimensions) Complex l) =
      EuclideanSpace.basisFun (Semantics.Qudit.Label
        (M.regionSubsystem region).complementDimensions) Complex
        (quditLabelRelabel (M.regionComplementCoordinateEquiv region) (fun _ => rfl) l) :=
    fun l => relabel_apply_basis (q := (M.regionSubsystem regionᶜ).selectedDimensions)
      (r := (M.regionSubsystem region).complementDimensions) _ _ l
  have hR2 : ∀ l, (M.regionDoubleComplementCoordinateRelabel region).toLinearEquiv
      (EuclideanSpace.basisFun (Semantics.Qudit.Label
        (M.regionSubsystem regionᶜ).complementDimensions) Complex l) =
      EuclideanSpace.basisFun (Semantics.Qudit.Label
        (M.regionSubsystem region).selectedDimensions) Complex
        (quditLabelRelabel (M.regionDoubleComplementCoordinateEquiv region) (fun _ => rfl) l) :=
    fun l => relabel_apply_basis (q := (M.regionSubsystem regionᶜ).complementDimensions)
      (r := (M.regionSubsystem region).selectedDimensions) _ _ l
  unfold BPTCommutingProjectorModel.complementPartitionTransport
    BPTCommutingProjectorModel.complementPartitionPostTransport
  simp only [composeUnitaryTransport_toLinearEquiv_apply, reg_apply_basis,
    unitaryRTensor_toLinearEquiv_apply_tmul, unitaryLTensor_toLinearEquiv_apply_tmul, hR1, hR2,
    tensorSwapUnitary_toLinearEquiv_apply_tmul]
  rfl


theorem projectorCD_eq (M : BPTCommutingProjectorModel L kappa) (region : Finset L.Site) :
    (M.regionSubsystem regionᶜ).extendLocalToRegister (M.projectorCDLocal region) =
      M.projectorCD region :=
  Classical.choose_spec (M.projectorCD_supportedOnRegister_complement region)

theorem fourFactorCDCoordinateTransport_eq (M : BPTCommutingProjectorModel L kappa)
    (region : Finset L.Site) :
    M.fourFactorCDCoordinateTransport region =
      composeUnitaryTransport (M.regionComplementCoordinateRelabel region)
        ((QAB M region).complementFactorization (QABC M region) (hABABC M region)) := rfl

theorem complementPartition_conj (M : BPTCommutingProjectorModel L kappa) (region : Finset L.Site)
    (Y : Semantics.Operator (M.regionSubsystem regionᶜ).selectedSystem) :
    (M.complementPartitionTransport region).conjOperator
        ((M.regionSubsystem regionᶜ).extendLocalToRegister Y) =
      TensorProduct.map (1 : Semantics.Operator (M.regionSubsystem region).selectedSystem)
        ((M.regionComplementCoordinateRelabel region).conjOperator Y) := by
  have h0 : (M.regionSubsystem regionᶜ).registerFactorization.conjOperator
      ((M.regionSubsystem regionᶜ).extendLocalToRegister Y) =
      TensorProduct.map Y (1 : Semantics.Operator (M.regionSubsystem regionᶜ).complementSystem) :=
    Semantics.UnitaryTransport.conjOperator_symm_conjOperator
      (M.regionSubsystem regionᶜ).registerFactorization
      ((M.regionSubsystem regionᶜ).extendLocal Y)
  unfold BPTCommutingProjectorModel.complementPartitionTransport
    BPTCommutingProjectorModel.complementPartitionPostTransport
  simp only [conj_compose, h0, rTensor_conj_map, lTensor_conj_map, swap_conj_map]

theorem fourFactorTransport_conj_projectorCD (M : BPTCommutingProjectorModel L kappa)
    (region : Finset L.Site) :
    (M.fourFactorTransport region).conjOperator (M.projectorCD region) =
      M.fourFactorExtendCD region (M.fourFactorProjectorCDLocal region) := by
  rw [fourFactorTransport_eq, ← projectorCD_eq]
  have hN : nestedFactorizationLeft (QAB M region) (QABC M region) (hABABC M region) =
      composeUnitaryTransport (M.complementPartitionTransport region)
        (unitaryLTensor (QAB M region).selectedSystem
          ((QAB M region).complementFactorization (QABC M region) (hABABC M region))) := by
    rw [complementPartition_eq]
    rfl
  rw [hN]
  simp only [conj_compose, complementPartition_conj, lTensor_conj_map_one, rTensor_conj_map_gen,
    Semantics.UnitaryTransport.conjOperator_one]
  rw [← TensorProduct.map_one, assoc_conj_map]
  unfold BPTCommutingProjectorModel.fourFactorExtendCD
    BPTCommutingProjectorModel.fourFactorProjectorCDLocal
  simp only [fourFactorCDCoordinateTransport_eq, conj_compose]

theorem conj_map_one_mul {H D K : Type u}
    [NormedAddCommGroup H] [InnerProductSpace Complex H] [Semantics.FiniteQuantumSystem H]
    [NormedAddCommGroup D] [InnerProductSpace Complex D] [Semantics.FiniteQuantumSystem D]
    [NormedAddCommGroup K] [InnerProductSpace Complex K] [Semantics.FiniteQuantumSystem K]
    (U : Semantics.UnitaryTransport (Semantics.CompositeSystem H D) K) (X Y : Semantics.Operator H) :
    U.conjOperator (TensorProduct.map (X * Y) (1 : Semantics.Operator D)) =
      U.conjOperator (TensorProduct.map X (1 : Semantics.Operator D)) *
        U.conjOperator (TensorProduct.map Y (1 : Semantics.Operator D)) := by
  have h : TensorProduct.map (X * Y) (1 : Semantics.Operator D) =
      TensorProduct.map X 1 * TensorProduct.map Y 1 := by
    rw [← TensorProduct.map_mul, mul_one]
  rw [h, Semantics.UnitaryTransport.conjOperator_mul]

theorem firstCut_conj_liftRight_CD (M : BPTCommutingProjectorModel L kappa) (region : Finset L.Site)
    (Z : Semantics.Operator (Semantics.CompositeSystem (M.fourFactorC region) (M.fourFactorD region))) :
    (M.firstCutCoordinateTransport region).conjOperator
        (overlapLiftRight (A := Semantics.CompositeSystem (M.fourFactorA region) (M.fourFactorB region)) Z) =
      M.fourFactorExtendCD region Z := by
  unfold BPTCommutingProjectorModel.firstCutCoordinateTransport
  simp only [conj_compose]
  unfold overlapLiftRight
  rw [Semantics.UnitaryTransport.conjOperator_symm_conjOperator]
  rw [← TensorProduct.map_one, assoc_conj_map]
  rfl

set_option maxHeartbeats 1000000 in
theorem firstCut_eq (M : BPTCommutingProjectorModel L kappa) (region : Finset L.Site) :
    (M.firstCutCoordinateTransport region).conjOperator (M.firstCutCodeLift region) =
      (M.fourFactorTransport region).conjOperator M.fullCodeProjector := by
  rw [fullCodeProjector_split M region]
  have hAB := fourFactorTransport_conj_projectorAB M region
  have hBC := fourFactorTransport_conj_projectorBC M region
  have hCD := fourFactorTransport_conj_projectorCD M region
  simp only [Semantics.UnitaryTransport.conjOperator_mul, hAB, hBC, hCD]
  unfold BPTCommutingProjectorModel.firstCutCodeLift BPTCommutingProjectorModel.firstCutProjectorMC
  rw [Semantics.UnitaryTransport.conjOperator_mul]
  have hL : (M.firstCutCoordinateTransport region).conjOperator
      (overlapLiftLeft (C := M.fourFactorD region)
        (TensorProduct.map (M.fourFactorProjectorABLocal region)
          (1 : Semantics.Operator (M.fourFactorC region)) *
          overlapLiftRight (A := M.fourFactorA region) (M.fourFactorProjectorBCLocal region))) =
      M.fourFactorExtendAB region (M.fourFactorProjectorABLocal region) *
        M.fourFactorExtendBC region (M.fourFactorProjectorBCLocal region) := by
    show (M.firstCutCoordinateTransport region).conjOperator
      (TensorProduct.map (TensorProduct.map (M.fourFactorProjectorABLocal region)
          (1 : Semantics.Operator (M.fourFactorC region)) *
          overlapLiftRight (A := M.fourFactorA region) (M.fourFactorProjectorBCLocal region))
        (1 : Semantics.Operator (M.fourFactorD region))) = _
    rw [conj_map_one_mul, firstCut_conj_map_AB, firstCut_conj_liftRight]
  rw [hL, firstCut_conj_liftRight_CD, mul_assoc]


theorem firstCut_global (M : BPTCommutingProjectorModel L kappa) (region : Finset L.Site) :
    (M.firstCutGlobalCoordinateTransport region).conjOperator M.fullCodeProjector =
      M.firstCutCodeLift region := by
  unfold BPTCommutingProjectorModel.firstCutGlobalCoordinateTransport
  exact (conj_compose _ _ _).trans
    ((congrArg (M.firstCutCoordinateTransport region).symm.conjOperator
      (firstCut_eq M region).symm).trans
      (Semantics.UnitaryTransport.symm_conjOperator_conjOperator _ _))

end QBAux

theorem solution
    (M : BPTCommutingProjectorModel L kappa) (region : Finset L.Site) :
    (M.firstCutGlobalCoordinateTransport region).conjOperator M.fullCodeProjector =
      M.firstCutCodeLift region :=
  QBAux.firstCut_global M region
