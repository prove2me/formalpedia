-- Prove2me | solution 1 for QEC.Coding.ChainComplexData.binaryCSSCode_homologicalDistance
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T20:12:33.283182+00:00
-- url     : https://prove2.me/submissions/a3c5a989-3f83-4ac2-a7d9-babdaa719cf0

import Definitions.Def_QEC_Coding_Core_Definitions
import Definitions.Def_QEC_Semantics_ErrorCorrection_CodeSupport
import Definitions.Def_QEC_Semantics_ErrorCorrection_KLRecovery
import Definitions.Def_QEC_Semantics_Channels_Kraus
import Definitions.Def_QEC_Semantics_Channels_KrausKnillLaflamme
import Definitions.Def_QEC_Semantics_Core_Qubit
import Definitions.Def_QEC_Coding_Stabilizer_PauliSemantics
import Theorems.Thm_QEC_Coding_ChainComplexData_pureZLogicalQuotientEquivMiddleHomology_mk
import Theorems.Thm_QEC_Coding_algebraicCSSMinimumDistance_of_sector_minima
attribute [local simp] QEC.Coding.ChainComplexData.pureZLogicalQuotientEquivMiddleHomology_mk



set_option autoImplicit false
noncomputable section
open QEC
open QEC.Coding
open Classical
open scoped BigOperators
universe u w
open QEC.Coding.ChainComplexData
namespace QEC.Coding.ChainComplexData
theorem _root_.solution
    {ι κ lambda : Type u} [Fintype ι] [DecidableEq ι] [Fintype κ] [Fintype lambda]
    (K : ChainComplexData
      (ZMod 2) (Word (ZMod 2) κ) (Word (ZMod 2) ι) (Word (ZMod 2) lambda))
    {dX dZ : Nat}
    (hX : PureXLogicalMinimumDistance
      (K.binaryCSSCode).xCode (K.binaryCSSCode).zCode dX)
    (hZ : PureZLogicalMinimumDistance
      (K.binaryCSSCode).xCode (K.binaryCSSCode).zCode dZ) :
    (∀ x : K.middleBoundaryCode.dual.carrier,
      K.pureXLogicalQuotientEquivMiddleCohomology (Submodule.Quotient.mk x) =
        Submodule.Quotient.mk (K.middleBoundaryDualEquivMiddleCocycleCode x)) ∧
    (∀ z : K.firstCoboundaryCheckCode.dual.carrier,
      K.pureZLogicalQuotientEquivMiddleHomology (Submodule.Quotient.mk z) =
        Submodule.Quotient.mk (K.firstCoboundaryDualEquivMiddleCycleCode z)) ∧
    AlgebraicCSSMinimumDistance
      (K.binaryCSSCode).xCode (K.binaryCSSCode).zCode (min dX dZ) := by
  exact ⟨K.pureXLogicalQuotientEquivMiddleCohomology_mk,
    K.pureZLogicalQuotientEquivMiddleHomology_mk,
    algebraicCSSMinimumDistance_of_sector_minima hX hZ⟩
end QEC.Coding.ChainComplexData
