-- Prove2me | solution 1 for QEC.Bounds.BPTCommutingProjectorModel.secondCutGlobalCoordinateTransport_conj_fullCodeProjector
-- status  : ACCEPTED   (prove)
-- author  : @Secousses
-- created : 2026-11-06T04:09:54.884583+00:00
-- url     : https://prove2.me/submissions/66c1ed12-26f3-4a67-b75a-fc909552a34f

import Definitions.Def_QEC_Bounds_BPTDisentangling_FourFactor
import Definitions.Def_QEC_Bounds_BPTDisentangling_Sectors_Selection
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
  constructor
  · intro h
    by_cases hx : x ∈ region
    · exact Or.inl ⟨h, hx⟩
    · exact Or.inr ⟨h, hx⟩
  · rintro (h | h)
    · exact h.1
    · exact h.1

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

set_option maxHeartbeats 400000 in
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

set_option maxHeartbeats 400000 in
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
  rw [LinearEquiv.symm_apply_eq, unitaryRTensor_toLinearEquiv_apply_tmul,
    LinearEquiv.apply_symm_apply]

theorem unitaryLTensor_symm_apply_tmul {H K : Type u}
    [NormedAddCommGroup H] [InnerProductSpace Complex H] [Semantics.FiniteQuantumSystem H]
    [NormedAddCommGroup K] [InnerProductSpace Complex K] [Semantics.FiniteQuantumSystem K]
    (I : Type u) [NormedAddCommGroup I] [InnerProductSpace Complex I]
    [Semantics.FiniteQuantumSystem I] (U : Semantics.UnitaryTransport H K)
    (i : I) (k : K) :
    (unitaryLTensor I U).toLinearEquiv.symm (i ⊗ₜ[Complex] k) =
      i ⊗ₜ[Complex] U.toLinearEquiv.symm k := by
  rw [LinearEquiv.symm_apply_eq, unitaryLTensor_toLinearEquiv_apply_tmul,
    LinearEquiv.apply_symm_apply]

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
  | zero => simp only [map_zero]
  | tmul k j =>
      rw [Semantics.UnitaryTransport.conjOperator_apply, unitaryRTensor_symm_apply_tmul]
      simp only [TensorProduct.map_tmul, Module.End.one_apply,
        unitaryRTensor_toLinearEquiv_apply_tmul, Semantics.UnitaryTransport.conjOperator_apply,
        LinearEquiv.apply_symm_apply]
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
  | zero => simp only [map_zero]
  | tmul i k =>
      rw [Semantics.UnitaryTransport.conjOperator_apply, unitaryLTensor_symm_apply_tmul]
      simp only [TensorProduct.map_tmul, Module.End.one_apply,
        unitaryLTensor_toLinearEquiv_apply_tmul, Semantics.UnitaryTransport.conjOperator_apply,
        LinearEquiv.apply_symm_apply]
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
  | zero => simp only [TensorProduct.zero_tmul, TensorProduct.tmul_zero, map_zero]
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
    | zero => simp only [map_zero]
    | tmul z u =>
        induction u using TensorProduct.induction_on with
        | zero => simp only [TensorProduct.tmul_zero, map_zero]
        | tmul a d =>
            simp only [TensorProduct.map_tmul, Module.End.one_apply, reorder_apply_general]
        | add x y hx hy => simp only [TensorProduct.tmul_add, map_add, hx, hy]
    | add x y hx hy => simp only [map_add, hx, hy]
  apply LinearMap.ext
  intro w
  rw [Semantics.UnitaryTransport.conjOperator_apply, key, LinearEquiv.apply_symm_apply]

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

set_option maxHeartbeats 400000 in
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

theorem conj3 {H K J G : Type u}
    [NormedAddCommGroup H] [InnerProductSpace Complex H] [Semantics.FiniteQuantumSystem H]
    [NormedAddCommGroup K] [InnerProductSpace Complex K] [Semantics.FiniteQuantumSystem K]
    [NormedAddCommGroup J] [InnerProductSpace Complex J] [Semantics.FiniteQuantumSystem J]
    [NormedAddCommGroup G] [InnerProductSpace Complex G] [Semantics.FiniteQuantumSystem G]
    (U1 : Semantics.UnitaryTransport H K) (U2 : Semantics.UnitaryTransport K J)
    (U3 : Semantics.UnitaryTransport J G) (A : Semantics.Operator H) :
    (composeUnitaryTransport (composeUnitaryTransport U1 U2) U3).conjOperator A =
      U3.conjOperator (U2.conjOperator (U1.conjOperator A)) := rfl

theorem extAB_eq (M : BPTCommutingProjectorModel L kappa) (region : Finset L.Site)
    (P : Semantics.Operator (Semantics.CompositeSystem (M.fourFactorA region) (M.fourFactorB region))) :
    M.fourFactorExtendAB region P =
      (tensorAssociatorUnitary (M.fourFactorA region) (M.fourFactorB region)
        (Semantics.CompositeSystem (M.fourFactorC region) (M.fourFactorD region))).conjOperator
        (TensorProduct.map P (1 : Semantics.Operator
          (Semantics.CompositeSystem (M.fourFactorC region) (M.fourFactorD region)))) := rfl

theorem tailAB_gen {A B P Q : Type u}
    [NormedAddCommGroup A] [InnerProductSpace Complex A] [Semantics.FiniteQuantumSystem A]
    [NormedAddCommGroup B] [InnerProductSpace Complex B] [Semantics.FiniteQuantumSystem B]
    [NormedAddCommGroup P] [InnerProductSpace Complex P] [Semantics.FiniteQuantumSystem P]
    [NormedAddCommGroup Q] [InnerProductSpace Complex Q] [Semantics.FiniteQuantumSystem Q]
    (S : Semantics.UnitaryTransport P (Semantics.CompositeSystem A B)) (X : Semantics.Operator P)
    (Y0 : Semantics.Operator (Semantics.CompositeSystem P Q))
    (h : Y0 = TensorProduct.map X (1 : Semantics.Operator Q)) :
    (tensorAssociatorUnitary A B Q).conjOperator ((unitaryRTensor S Q).conjOperator Y0) =
      (tensorAssociatorUnitary A B Q).conjOperator
        (TensorProduct.map (S.conjOperator X) (1 : Semantics.Operator Q)) := by
  rw [h, rTensor_conj_map]

set_option maxHeartbeats 400000 in
theorem fourFactorTransport_conj_extendAB (M : BPTCommutingProjectorModel L kappa)
    (region : Finset L.Site) (X : Semantics.Operator (QAB M region).selectedSystem) :
    (M.fourFactorTransport region).conjOperator ((QAB M region).extendLocalToRegister X) =
      M.fourFactorExtendAB region
        (((QA M region).selectedFactorization (QAB M region) (hAAB M region)).conjOperator X) := by
  have h1 : (nestedFactorizationLeft (QAB M region) (QABC M region) (hABABC M region)).conjOperator
      ((QAB M region).extendLocalToRegister X) =
      TensorProduct.map X (1 : Semantics.Operator
        (Semantics.CompositeSystem ((QAB M region).additionalRetainedSystem (QABC M region))
          (QABC M region).complementSystem)) :=
    (conj_compose (QAB M region).registerFactorization
      (unitaryLTensor (QAB M region).selectedSystem
        ((QAB M region).complementFactorization (QABC M region) (hABABC M region))) _).trans
      ((congrArg _ (Semantics.UnitaryTransport.conjOperator_symm_conjOperator
        (QAB M region).registerFactorization ((QAB M region).extendLocal X))).trans
        (lTensor_conj_map _ _ _))
  refine (congrArg (fun U => U.conjOperator ((QAB M region).extendLocalToRegister X))
    (fourFactorTransport_eq M region)).trans ?_
  refine (conj3 _ _ _ _).trans ?_
  exact (tailAB_gen _ _ _ h1).trans (extAB_eq M region _).symm

theorem fourFactorTransport_conj_projectorAB (M : BPTCommutingProjectorModel L kappa)
    (region : Finset L.Site) :
    (M.fourFactorTransport region).conjOperator (M.projectorAB region) =
      M.fourFactorExtendAB region (M.fourFactorProjectorABLocal region) :=
  (congrArg (M.fourFactorTransport region).conjOperator (projectorAB_eq M region).symm).trans
    ((fourFactorTransport_conj_extendAB M region _).trans
      (congrArg (M.fourFactorExtendAB region) (fourFactorProjectorABLocal_eq M region).symm))

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
  | zero => simp only [map_zero]
  | tmul h kj =>
      induction kj using TensorProduct.induction_on with
      | zero => simp only [TensorProduct.tmul_zero, map_zero]
      | tmul k j =>
          have hs : (tensorAssociatorUnitary H K J).toLinearEquiv.symm
              (h ⊗ₜ[Complex] (k ⊗ₜ[Complex] j)) = (h ⊗ₜ[Complex] k) ⊗ₜ[Complex] j :=
            tensorAssociatorUnitary_symm_apply_tmul H K J h k j
          rw [Semantics.UnitaryTransport.conjOperator_apply, hs]
          simp only [TensorProduct.map_tmul]
          exact tensorAssociatorUnitary_toLinearEquiv_apply_tmul H K J (A h) (B k) (C j)
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
  | zero => simp only [map_zero]
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
  | zero => simp only [map_zero]
  | tmul k j =>
      rw [Semantics.UnitaryTransport.conjOperator_apply, unitaryRTensor_symm_apply_tmul]
      simp only [TensorProduct.map_tmul, Module.End.one_apply,
        unitaryRTensor_toLinearEquiv_apply_tmul, Semantics.UnitaryTransport.conjOperator_apply,
        LinearEquiv.apply_symm_apply]
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
  | zero => simp only [map_zero]
  | tmul i k =>
      rw [Semantics.UnitaryTransport.conjOperator_apply, unitaryLTensor_symm_apply_tmul]
      simp only [TensorProduct.map_tmul, Module.End.one_apply,
        unitaryLTensor_toLinearEquiv_apply_tmul, Semantics.UnitaryTransport.conjOperator_apply,
        LinearEquiv.apply_symm_apply]
  | add x y hx hy => simp only [map_add, hx, hy]

set_option maxHeartbeats 400000 in
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

theorem tailCD_gen {A B P Q : Type u}
    [NormedAddCommGroup A] [InnerProductSpace Complex A] [Semantics.FiniteQuantumSystem A]
    [NormedAddCommGroup B] [InnerProductSpace Complex B] [Semantics.FiniteQuantumSystem B]
    [NormedAddCommGroup P] [InnerProductSpace Complex P] [Semantics.FiniteQuantumSystem P]
    [NormedAddCommGroup Q] [InnerProductSpace Complex Q] [Semantics.FiniteQuantumSystem Q]
    (S : Semantics.UnitaryTransport P (Semantics.CompositeSystem A B)) (Z : Semantics.Operator Q)
    (Y0 : Semantics.Operator (Semantics.CompositeSystem P Q))
    (h : Y0 = TensorProduct.map (1 : Semantics.Operator P) Z) :
    (tensorAssociatorUnitary A B Q).conjOperator ((unitaryRTensor S Q).conjOperator Y0) =
      TensorProduct.map (1 : Semantics.Operator A) (TensorProduct.map (1 : Semantics.Operator B) Z) := by
  rw [h, rTensor_conj_map_gen, Semantics.UnitaryTransport.conjOperator_one,
    ← TensorProduct.map_one, assoc_conj_map]

theorem extCD_eq (M : BPTCommutingProjectorModel L kappa) (region : Finset L.Site)
    (P : Semantics.Operator (Semantics.CompositeSystem (M.fourFactorC region) (M.fourFactorD region))) :
    M.fourFactorExtendCD region P =
      TensorProduct.map (1 : Semantics.Operator (M.fourFactorA region))
        (TensorProduct.map (1 : Semantics.Operator (M.fourFactorB region)) P) := rfl

set_option maxHeartbeats 400000 in
theorem fourFactorTransport_conj_extendCD (M : BPTCommutingProjectorModel L kappa)
    (region : Finset L.Site) (Y : Semantics.Operator (M.regionSubsystem regionᶜ).selectedSystem) :
    (M.fourFactorTransport region).conjOperator
        ((M.regionSubsystem regionᶜ).extendLocalToRegister Y) =
      M.fourFactorExtendCD region
        ((M.fourFactorCDCoordinateTransport region).conjOperator Y) := by
  have hN : nestedFactorizationLeft (QAB M region) (QABC M region) (hABABC M region) =
      composeUnitaryTransport (M.complementPartitionTransport region)
        (unitaryLTensor (QAB M region).selectedSystem
          ((QAB M region).complementFactorization (QABC M region) (hABABC M region))) :=
    (rfl : nestedFactorizationLeft (QAB M region) (QABC M region) (hABABC M region) =
      composeUnitaryTransport (QAB M region).registerFactorization
        (unitaryLTensor (QAB M region).selectedSystem
          ((QAB M region).complementFactorization (QABC M region) (hABABC M region)))).trans
      (congrArg (fun R => composeUnitaryTransport R
        (unitaryLTensor (QAB M region).selectedSystem
          ((QAB M region).complementFactorization (QABC M region) (hABABC M region))))
        (complementPartition_eq M region).symm)
  have hconj : ((QAB M region).complementFactorization (QABC M region) (hABABC M region)).conjOperator
      ((M.regionComplementCoordinateRelabel region).conjOperator Y) =
      (M.fourFactorCDCoordinateTransport region).conjOperator Y :=
    (conj_compose (M.regionComplementCoordinateRelabel region)
      ((QAB M region).complementFactorization (QABC M region) (hABABC M region)) Y).symm.trans
      (congrArg (fun U => U.conjOperator Y) (fourFactorCDCoordinateTransport_eq M region).symm)
  have h1 : (nestedFactorizationLeft (QAB M region) (QABC M region) (hABABC M region)).conjOperator
      ((M.regionSubsystem regionᶜ).extendLocalToRegister Y) =
      TensorProduct.map (1 : Semantics.Operator (QAB M region).selectedSystem)
        ((M.fourFactorCDCoordinateTransport region).conjOperator Y) :=
    ((congrArg (fun U => U.conjOperator ((M.regionSubsystem regionᶜ).extendLocalToRegister Y)) hN).trans
      ((conj_compose _ _ _).trans
        ((congrArg _ (complementPartition_conj M region Y)).trans (lTensor_conj_map_one _ _ _)))).trans
      (congrArg (TensorProduct.map (1 : Semantics.Operator (QAB M region).selectedSystem)) hconj)
  refine (congrArg (fun U => U.conjOperator ((M.regionSubsystem regionᶜ).extendLocalToRegister Y))
    (fourFactorTransport_eq M region)).trans ?_
  refine (conj3 _ _ _ _).trans ?_
  exact (tailCD_gen _ _ _ h1).trans (extCD_eq M region _).symm

theorem fourFactorTransport_conj_projectorCD (M : BPTCommutingProjectorModel L kappa)
    (region : Finset L.Site) :
    (M.fourFactorTransport region).conjOperator (M.projectorCD region) =
      M.fourFactorExtendCD region (M.fourFactorProjectorCDLocal region) :=
  (congrArg (M.fourFactorTransport region).conjOperator (projectorCD_eq M region).symm).trans
    (fourFactorTransport_conj_extendCD M region _)

theorem lTensor_assoc_symm_eq {A B C D : Type u}
    [NormedAddCommGroup A] [InnerProductSpace Complex A] [Semantics.FiniteQuantumSystem A]
    [NormedAddCommGroup B] [InnerProductSpace Complex B] [Semantics.FiniteQuantumSystem B]
    [NormedAddCommGroup C] [InnerProductSpace Complex C] [Semantics.FiniteQuantumSystem C]
    [NormedAddCommGroup D] [InnerProductSpace Complex D] [Semantics.FiniteQuantumSystem D] :
    ((TensorProduct.assocIsometry Complex B C D).symm.lTensor A).toLinearEquiv.symm =
      (unitaryLTensor A (tensorAssociatorUnitary B C D)).toLinearEquiv := by
  apply LinearEquiv.ext
  intro x
  induction x using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul a z =>
      rw [LinearEquiv.symm_apply_eq, unitaryLTensor_toLinearEquiv_apply_tmul,
        LinearIsometryEquiv.toLinearEquiv_lTensor, LinearEquiv.lTensor_tmul]
      exact congrArg (TensorProduct.tmul Complex a)
        (LinearEquiv.symm_apply_apply (TensorProduct.assocIsometry Complex B C D).toLinearEquiv z).symm
  | add x y hx hy => simp only [map_add, hx, hy]

theorem reassoc_symm_eq (M : BPTCommutingProjectorModel L kappa) (region : Finset L.Site) :
    (M.fourFactorMiddleReassociate region).symm =
      unitaryLTensor (M.fourFactorA region)
        (tensorAssociatorUnitary (M.fourFactorB region) (M.fourFactorC region)
          (M.fourFactorD region)) :=
  ut_ext _ _ lTensor_assoc_symm_eq

theorem extBC_eq_lTensor (M : BPTCommutingProjectorModel L kappa) (region : Finset L.Site)
    (P : Semantics.Operator (Semantics.CompositeSystem (M.fourFactorB region) (M.fourFactorC region))) :
    M.fourFactorExtendBC region P =
      TensorProduct.map (1 : Semantics.Operator (M.fourFactorA region))
        ((tensorAssociatorUnitary (M.fourFactorB region) (M.fourFactorC region)
          (M.fourFactorD region)).conjOperator
          (TensorProduct.map P (1 : Semantics.Operator (M.fourFactorD region)))) := by
  unfold BPTCommutingProjectorModel.fourFactorExtendBC
  rw [reassoc_symm_eq, lTensor_conj_map_one]

theorem map_one_mul {E F : Type u}
    [NormedAddCommGroup E] [InnerProductSpace Complex E] [Semantics.FiniteQuantumSystem E]
    [NormedAddCommGroup F] [InnerProductSpace Complex F] [Semantics.FiniteQuantumSystem F]
    (X Y : Semantics.Operator F) :
    TensorProduct.map (1 : Semantics.Operator E) (X * Y) =
      TensorProduct.map 1 X * TensorProduct.map 1 Y := by
  rw [← TensorProduct.map_mul, mul_one]

theorem secondCut_Bbar (M : BPTCommutingProjectorModel L kappa) (region : Finset L.Site) :
    TensorProduct.map (1 : Semantics.Operator (M.fourFactorA region))
      (M.secondCutProjectorBbarM region) =
      M.fourFactorExtendBC region (M.fourFactorProjectorBCLocal region) *
        M.fourFactorExtendCD region (M.fourFactorProjectorCDLocal region) :=
  (map_one_mul _ _).trans
    (congrArg₂ (· * ·) (extBC_eq_lTensor M region _).symm rfl)

set_option maxHeartbeats 400000 in
theorem secondCut_lhs (M : BPTCommutingProjectorModel L kappa) (region : Finset L.Site) :
    (M.secondCutCoordinateTransport region).conjOperator (M.secondCutCodeLift region) =
      M.fourFactorExtendAB region (M.fourFactorProjectorABLocal region) *
        (M.fourFactorExtendBC region (M.fourFactorProjectorBCLocal region) *
          M.fourFactorExtendCD region (M.fourFactorProjectorCDLocal region)) :=
  (Semantics.UnitaryTransport.conjOperator_mul _ _ _).trans
    (congrArg₂ (· * ·) rfl
      ((Semantics.UnitaryTransport.conjOperator_symm_conjOperator _ _).trans
        (secondCut_Bbar M region)))

set_option maxHeartbeats 400000 in
theorem fullCode_conj (M : BPTCommutingProjectorModel L kappa) (region : Finset L.Site) :
    (M.fourFactorTransport region).conjOperator M.fullCodeProjector =
      M.fourFactorExtendAB region (M.fourFactorProjectorABLocal region) *
        (M.fourFactorExtendBC region (M.fourFactorProjectorBCLocal region) *
          M.fourFactorExtendCD region (M.fourFactorProjectorCDLocal region)) :=
  (congrArg (M.fourFactorTransport region).conjOperator (fullCodeProjector_split M region)).trans
    ((Semantics.UnitaryTransport.conjOperator_mul _ _ _).trans
      (congrArg₂ (· * ·) (fourFactorTransport_conj_projectorAB M region)
        ((Semantics.UnitaryTransport.conjOperator_mul _ _ _).trans
          (congrArg₂ (· * ·) (fourFactorTransport_conj_projectorBC M region)
            (fourFactorTransport_conj_projectorCD M region)))))

theorem secondCut_eq (M : BPTCommutingProjectorModel L kappa) (region : Finset L.Site) :
    (M.secondCutCoordinateTransport region).conjOperator (M.secondCutCodeLift region) =
      (M.fourFactorTransport region).conjOperator M.fullCodeProjector :=
  (secondCut_lhs M region).trans (fullCode_conj M region).symm

theorem secondCut_global (M : BPTCommutingProjectorModel L kappa) (region : Finset L.Site) :
    (M.secondCutGlobalCoordinateTransport region).conjOperator M.fullCodeProjector =
      M.secondCutCodeLift region := by
  unfold BPTCommutingProjectorModel.secondCutGlobalCoordinateTransport
  exact (conj_compose _ _ _).trans
    ((congrArg (M.secondCutCoordinateTransport region).symm.conjOperator
      (secondCut_eq M region).symm).trans
      (Semantics.UnitaryTransport.symm_conjOperator_conjOperator _ _))

end QBAux

theorem solution
    (M : BPTCommutingProjectorModel L kappa) (region : Finset L.Site) :
    (M.secondCutGlobalCoordinateTransport region).conjOperator M.fullCodeProjector =
      M.secondCutCodeLift region :=
  QBAux.secondCut_global M region
