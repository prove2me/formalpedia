-- Prove2me | solution 1 for QEC.Coding.ExpanderCodes.PK20.ClassicalRowReduction.ker_reducedBoundary_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T11:24:20.181057+00:00
-- url     : https://prove2.me/submissions/2b770f36-84ca-414a-9764-bdc437bd9297

import Definitions.Def_QEC_Coding_CodeReduction_DistanceBalancing_Core
import Mathlib.LinearAlgebra.Dimension.StrongRankCondition
import Mathlib.LinearAlgebra.Matrix.Rank
import Definitions.Def_QEC_Coding_ExpanderCodes_ClassicalRowReduction
import Theorems.Thm_QEC_Coding_ExpanderCodes_PK20_ClassicalRowReduction_span_independentRows
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
    (Y : Word (ZMod 2) bit →ₗ[ZMod 2] Word (ZMod 2) check) :
    LinearMap.ker (reducedBoundary Y) = LinearMap.ker Y := by
  ext x
  constructor
  · intro hx
    rw [LinearMap.mem_ker] at hx ⊢
    funext b
    have hrow : wordLinearMapTranspose Y (Pi.single b 1) ∈
        Submodule.span (ZMod 2)
          (independentRows Y : Set (Word (ZMod 2) bit)) := by
      rw [span_independentRows Y]
      exact Submodule.subset_span ⟨b, rfl⟩
    have horth : ∀ v ∈ Submodule.span (ZMod 2)
        (independentRows Y : Set (Word (ZMod 2) bit)),
        wordPairing v x = 0 := by
      intro v hv
      refine Submodule.span_induction (p := fun v _ => wordPairing v x = 0)
        ?_ ?_ ?_ ?_ hv
      · intro v hvRows
        have hvReduced := congrFun hx ⟨v, hvRows⟩
        simpa [reducedBoundary, reducedMatrix, Matrix.toLin'_apply,
          Matrix.mulVec, dotProduct, wordPairing_apply, mul_comm] using hvReduced
      · simp [wordPairing_apply]
      · intro v w _ _ hv hw
        simp [wordPairing_apply, dotProduct_add, hv, hw]
      · intro c v _ hv
        simp [wordPairing_apply, hv]
    rw [← pairing_row_eq_apply Y x b]
    exact horth _ hrow
  · intro hx
    rw [LinearMap.mem_ker] at hx ⊢
    funext r
    obtain ⟨b, hb⟩ := independentRows_subset Y r.2
    have hpair : wordPairing r.1 x = 0 := by
      rw [← hb, pairing_row_eq_apply Y x b]
      exact congrFun hx b
    simpa [reducedBoundary, reducedMatrix, Matrix.toLin'_apply,
      Matrix.mulVec, wordPairing_apply] using hpair
end QEC.Coding.ExpanderCodes.PK20.ClassicalRowReduction
