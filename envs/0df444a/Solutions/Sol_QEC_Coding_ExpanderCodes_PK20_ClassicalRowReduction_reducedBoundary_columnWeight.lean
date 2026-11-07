-- Prove2me | solution 1 for QEC.Coding.ExpanderCodes.PK20.ClassicalRowReduction.reducedBoundary_columnWeight
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T11:23:46.156191+00:00
-- url     : https://prove2.me/submissions/501c0661-856b-4bf1-b008-5747141085a5

import Definitions.Def_QEC_Coding_CodeReduction_DistanceBalancing_Core
import Mathlib.LinearAlgebra.Dimension.StrongRankCondition
import Mathlib.LinearAlgebra.Matrix.Rank
import Definitions.Def_QEC_Coding_ExpanderCodes_ClassicalRowReduction
import Theorems.Thm_QEC_Coding_ExpanderCodes_PK20_ClassicalRowReduction_originalRow_spec
import Theorems.Thm_QEC_Coding_ExpanderCodes_PK20_ClassicalRowReduction_originalRow_injective
import Theorems.Thm_QEC_Coding_ChainComplexData_pureZLogicalQuotientEquivMiddleHomology_mk
import Theorems.Thm_QEC_Coding_ClassicalWeightReduction_boundary_single
import Theorems.Thm_QEC_Coding_ClassicalWeightReduction_linearMapOfBasisImages_single
import Theorems.Thm_QEC_Coding_ClassicalWeightReduction_originalBoundary_single
import Theorems.Thm_QEC_Coding_dualChainComplex_boundary1
import Theorems.Thm_QEC_Coding_dualChainComplex_boundary2
import Theorems.Thm_QEC_Semantics_UnitaryTransport_conjDensity_apply
import Theorems.Thm_QEC_Semantics_UnitaryTransport_conjDensity_toOperator
attribute [local simp] QEC.Coding.ChainComplexData.pureZLogicalQuotientEquivMiddleHomology_mk
attribute [local simp] QEC.Coding.ClassicalWeightReduction.boundary_single
attribute [local simp] QEC.Coding.ClassicalWeightReduction.linearMapOfBasisImages_single
attribute [local simp] QEC.Coding.ClassicalWeightReduction.originalBoundary_single
attribute [local simp] QEC.Coding.dualChainComplex_boundary1
attribute [local simp] QEC.Coding.dualChainComplex_boundary2
attribute [local simp] QEC.Semantics.UnitaryTransport.conjDensity_apply
attribute [local simp] QEC.Semantics.UnitaryTransport.conjDensity_toOperator



set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.ExpanderCodes QEC.Coding.ExpanderCodes.PK20 QEC.Coding.ExpanderCodes.PK20.ClassicalRowReduction
open QEC.Coding
open QEC.Coding.DistanceBalancing
universe u
variable {bit check : Type u}
variable [Fintype bit] [DecidableEq bit]
variable [Fintype check] [DecidableEq check]
namespace QEC.Coding.ExpanderCodes.PK20.ClassicalRowReduction
theorem _root_.solution
    (Y : Word (ZMod 2) bit →ₗ[ZMod 2] Word (ZMod 2) check)
    (a : bit) :
    HammingWeight (reducedBoundary Y (Pi.single a 1)) ≤
      HammingWeight (Y (Pi.single a 1)) := by
  classical
  rw [HammingWeight_eq_card_hammingSupport,
    HammingWeight_eq_card_hammingSupport]
  apply Finset.card_le_card_of_injOn (originalRow Y)
  · intro r hr
    have hcoordinate : reducedBoundary Y (Pi.single a 1) r = r.1 a := by
      simp [reducedBoundary, reducedMatrix, Matrix.toLin'_apply,
        Matrix.mulVec, dotProduct_single_one]
    have horiginal : Y (Pi.single a 1) (originalRow Y r) = r.1 a := by
      calc
        Y (Pi.single a 1) (originalRow Y r) =
            wordPairing (Pi.single (originalRow Y r) 1)
              (Y (Pi.single a 1)) := by
                symm
                exact single_one_dotProduct _ _
        _ = wordPairing
              (wordLinearMapTranspose Y (Pi.single (originalRow Y r) 1))
              (Pi.single a 1) := by
                symm
                exact wordPairing_wordLinearMapTranspose Y _ _
        _ = wordLinearMapTranspose Y
              (Pi.single (originalRow Y r) 1) a :=
                dotProduct_single_one _ _
        _ = r.1 a := congrFun (originalRow_spec Y r) a
    simpa [hammingSupport, hcoordinate, horiginal] using hr
  · exact (originalRow_injective Y).injOn
end QEC.Coding.ExpanderCodes.PK20.ClassicalRowReduction
