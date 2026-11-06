-- Prove2me | solution 1 for QEC.Semantics.QuditSubsystem.selectedReferenceMarginal_pureDensity_toOperator_sum
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T13:59:36.978164+00:00
-- url     : https://prove2.me/submissions/ebaa07b0-441b-4953-87ef-10ce80b8edba

import Definitions.Def_QEC_Semantics_Entropy_Purification
import Definitions.Def_QEC_Semantics_Entropy_MatrixRelative
import Definitions.Def_QEC_Semantics_ErrorCorrection_QuditReplacement
import Definitions.Def_QEC_Semantics_ErrorCorrection_KLRecovery
import Definitions.Def_QEC_Semantics_ErrorCorrection_Detectability
import Definitions.Def_QEC_Semantics_ErrorCorrection_ReferenceDecoupling
import Theorems.Thm_QEC_Semantics_QuditSubsystem_selectedReferenceRaw_extension
import Theorems.Thm_QEC_Semantics_DensityOperator_rankOne_sum_sum
import Theorems.Thm_QEC_Semantics_DensityOperator_sum_rightTensorCoefficients_tmul


set_option autoImplicit false
noncomputable section
open QEC
open QEC.Semantics
open Classical
open DensityOperator
open scoped BigOperators ComplexOrder TensorProduct
universe u v w
open QEC.Semantics.QuditSubsystem
variable {ι : Type u} [Fintype ι] [DecidableEq ι]
variable {q : ι → Nat}
namespace QEC.Semantics.QuditSubsystem
theorem _root_.solution (S : QuditSubsystem q)
    (Ref : Type u) [NormedAddCommGroup Ref] [InnerProductSpace Complex Ref]
    [FiniteQuantumSystem Ref]
    (b : OrthonormalBasis (Fin (Module.finrank Complex Ref)) Complex Ref)
    (psi : CompositeSystem (Qudit.QuditRegister q) Ref) (hpsi : ‖psi‖ ^ 2 = 1) :
    (S.selectedReferenceMarginal Ref (pureDensity psi hpsi)).toOperator =
      ∑ i, ∑ j,
        TensorProduct.map
          (S.selectedPartialTraceFromRegister
            (InnerProductSpace.rankOne Complex (rightTensorCoefficients b psi i)
              (rightTensorCoefficients b psi j)).toLinearMap)
          (InnerProductSpace.rankOne Complex (b i) (b j)).toLinearMap := by
  change partialTraceRightRaw (CompositeSystem S.selectedSystem Ref) S.complementSystem
    ((S.selectedReferenceTransport Ref).conjOperator
      (InnerProductSpace.rankOne Complex psi psi).toLinearMap) = _
  change S.selectedReferenceRaw Ref
    (InnerProductSpace.rankOne Complex psi psi).toLinearMap = _
  conv_lhs => rw [← sum_rightTensorCoefficients_tmul b psi]
  rw [rankOne_sum_sum]
  rw [map_sum (S.selectedReferenceRaw Ref) _ Finset.univ]
  apply Finset.sum_congr rfl
  intro i _
  rw [map_sum (S.selectedReferenceRaw Ref) _ Finset.univ]
  apply Finset.sum_congr rfl
  intro j _
  rw [← tensorMap_rankOne]
  exact S.selectedReferenceRaw_extension Ref
    (InnerProductSpace.rankOne Complex (rightTensorCoefficients b psi i)
      (rightTensorCoefficients b psi j)).toLinearMap (b i) (b j)
end QEC.Semantics.QuditSubsystem
