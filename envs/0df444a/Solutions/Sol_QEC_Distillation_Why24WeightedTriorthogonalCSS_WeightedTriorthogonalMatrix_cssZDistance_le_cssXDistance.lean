-- Prove2me | solution 1 for QEC.Distillation.Why24WeightedTriorthogonalCSS.WeightedTriorthogonalMatrix.cssZDistance_le_cssXDistance
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T15:17:41.688366+00:00
-- url     : https://prove2.me/submissions/d59172c1-9cfd-4dfb-ac5f-8893542bd3ad

import Definitions.Def_QEC_Coding_HypergraphProduct_Distance
import Definitions.Def_QEC_Coding_QuditQubitConversion_U7Gate
import Definitions.Def_QEC_Distillation_MultiplicativeQuditProtocol_Phase
import Definitions.Def_QEC_Distillation_MultiplicativeQuditProtocol_Register
import Definitions.Def_QEC_Distillation_Core_TransversalGate
import Definitions.Def_QEC_Distillation_ConstantOverheadProtocol_WeightedTriorthogonalCSS
import Theorems.Thm_QEC_Distillation_Why24WeightedTriorthogonalCSS_WeightedTriorthogonalMatrix_HammingWeight_sigmaEquiv
import Theorems.Thm_QEC_Distillation_Why24WeightedTriorthogonalCSS_WeightedTriorthogonalMatrix_sigmaEquiv_mem_stabilizerCode_dual_of_mem_rowCode
import Theorems.Thm_QEC_Distillation_Why24WeightedTriorthogonalCSS_WeightedTriorthogonalMatrix_sigmaEquiv_not_mem_rowCode_dual_of_mem_rowCode_not_mem_stabilizerCode
import Theorems.Thm_QEC_Coding_HypergraphProduct_finitePredicateMinimum_le_of
import Theorems.Thm_QEC_Coding_HypergraphProduct_le_finitePredicateMinimum


set_option autoImplicit false
noncomputable section
open QEC QEC.Distillation QEC.Distillation.Why24WeightedTriorthogonalCSS
open QEC.Coding QEC.Semantics
open scoped BigOperators
open QEC.Distillation.Why24WeightedTriorthogonalCSS.WeightedTriorthogonalMatrix
variable {Logical Stabilizer Site : Type}
variable [Fintype Logical] [DecidableEq Logical]
variable [Fintype Stabilizer] [DecidableEq Stabilizer]
variable [Fintype Site] [DecidableEq Site]
namespace QEC.Distillation.Why24WeightedTriorthogonalCSS.WeightedTriorthogonalMatrix
theorem _root_.solution
    (R : WeightedTriorthogonalMatrix Logical Stabilizer Site) :
    R.cssZDistance ≤ R.cssXDistance := by
  classical
  apply HypergraphProduct.le_finitePredicateMinimum
  intro x hx
  have hmapped :
      R.sigmaEquiv x ∈ R.stabilizerCode.dual.carrier ∧
        R.sigmaEquiv x ∉ R.rowCode.dual.carrier :=
    ⟨R.sigmaEquiv_mem_stabilizerCode_dual_of_mem_rowCode hx.1,
      R.sigmaEquiv_not_mem_rowCode_dual_of_mem_rowCode_not_mem_stabilizerCode hx.1 hx.2⟩
  calc
    R.cssZDistance ≤ (HammingWeight (R.sigmaEquiv x) : WithTop Nat) :=
      HypergraphProduct.finitePredicateMinimum_le_of hmapped
    _ = (HammingWeight x : WithTop Nat) := by rw [R.HammingWeight_sigmaEquiv]
end QEC.Distillation.Why24WeightedTriorthogonalCSS.WeightedTriorthogonalMatrix
