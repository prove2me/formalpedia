-- Prove2me | solution 1 for QEC.Coding.ExpanderCodes.PK20.ClassicalRowReduction.reducedBoundary_rowWeight
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T11:23:04.887866+00:00
-- url     : https://prove2.me/submissions/97c49b3f-47dc-46f8-823b-519354c58978

import Definitions.Def_QEC_Coding_CodeReduction_DistanceBalancing_Core
import Mathlib.LinearAlgebra.Dimension.StrongRankCondition
import Mathlib.LinearAlgebra.Matrix.Rank
import Definitions.Def_QEC_Coding_ExpanderCodes_ClassicalRowReduction
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


section
namespace QEC.Coding.ExpanderCodes.PK20.ClassicalRowReduction
open QEC.Coding
open QEC.Coding.DistanceBalancing
universe u
variable {bit check : Type u}
variable [Fintype bit] [DecidableEq bit]
variable [Fintype check] [DecidableEq check]
private theorem pairing_row_eq_apply
    (Y : Word (ZMod 2) bit →ₗ[ZMod 2] Word (ZMod 2) check)
    (x : Word (ZMod 2) bit) (b : check) :
    wordPairing (wordLinearMapTranspose Y (Pi.single b 1)) x = Y x b := by
  rw [wordPairing_wordLinearMapTranspose]
  exact single_one_dotProduct b (Y x)
end QEC.Coding.ExpanderCodes.PK20.ClassicalRowReduction
end

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
    {w : Nat}
    (hRow : ∀ b, HammingWeight
      (wordLinearMapTranspose Y (Pi.single b 1)) ≤ w) :
    ∀ r, HammingWeight
      (wordLinearMapTranspose (reducedBoundary Y) (Pi.single r 1)) ≤ w := by
  intro r
  obtain ⟨b, hb⟩ := independentRows_subset Y r.2
  have hSelected :
      wordLinearMapTranspose (reducedBoundary Y) (Pi.single r 1) = r.1 := by
    ext a
    calc
      wordLinearMapTranspose (reducedBoundary Y) (Pi.single r 1) a =
          wordPairing (wordLinearMapTranspose (reducedBoundary Y)
            (Pi.single r 1)) (Pi.single a 1) := by
            symm
            exact dotProduct_single_one _ _
      _ = reducedBoundary Y (Pi.single a 1) r :=
        pairing_row_eq_apply (reducedBoundary Y) (Pi.single a 1) r
      _ = r.1 a := by
        simp [reducedBoundary, reducedMatrix, Matrix.toLin'_apply,
          Matrix.mulVec, dotProduct_single_one]
  rw [hSelected, ← hb]
  exact hRow b
end QEC.Coding.ExpanderCodes.PK20.ClassicalRowReduction
