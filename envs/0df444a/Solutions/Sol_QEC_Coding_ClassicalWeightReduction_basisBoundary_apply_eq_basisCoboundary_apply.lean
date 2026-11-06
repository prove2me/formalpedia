-- Prove2me | solution 1 for QEC.Coding.ClassicalWeightReduction.basisBoundary_apply_eq_basisCoboundary_apply
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T19:42:08.964117+00:00
-- url     : https://prove2.me/submissions/435f4342-b110-4407-9f39-bb8d568c0bd5

import Definitions.Def_QEC_Coding_ChainComplex_HomotopyDistance
import Definitions.Def_QEC_Coding_CodeReduction_Classical_Core
import Theorems.Thm_QEC_Coding_ClassicalWeightReduction_pathVertexCoboundary_apply_eq_pathEdgeBoundary_apply
import Theorems.Thm_QEC_Coding_ClassicalWeightReduction_optionalSingle_map_auxiliaryCheckIndex_apply_of_ne
import Theorems.Thm_QEC_Coding_ClassicalWeightReduction_optionalSingle_map_auxiliaryBitIndex_apply_of_ne
import Theorems.Thm_QEC_Coding_ClassicalWeightReduction_single_bitIncidenceAt_apply
import Theorems.Thm_QEC_Coding_ClassicalWeightReduction_single_bitIncidenceAt_apply_of_ne
import Theorems.Thm_QEC_Coding_ClassicalWeightReduction_single_checkIncidenceAt_apply
import Theorems.Thm_QEC_Coding_ClassicalWeightReduction_single_checkIncidenceAt_apply_of_ne
import Theorems.Thm_QEC_Coding_ClassicalWeightReduction_linearMapOfBasisImages_single
import Theorems.Thm_QEC_Coding_ClassicalWeightReduction_originalBoundary_single
import Theorems.Thm_QEC_Coding_ClassicalWeightReduction_boundary_single
import Theorems.Thm_QEC_Coding_ChainComplexData_pureZLogicalQuotientEquivMiddleHomology_mk
import Theorems.Thm_QEC_Semantics_UnitaryTransport_conjDensity_apply
import Theorems.Thm_QEC_Semantics_UnitaryTransport_conjDensity_toOperator
attribute [local simp] QEC.Coding.ChainComplexData.pureZLogicalQuotientEquivMiddleHomology_mk
attribute [local simp] QEC.Semantics.UnitaryTransport.conjDensity_apply
attribute [local simp] QEC.Semantics.UnitaryTransport.conjDensity_toOperator


attribute [local simp] QEC.Coding.ClassicalWeightReduction.linearMapOfBasisImages_single
attribute [local simp] QEC.Coding.ClassicalWeightReduction.originalBoundary_single
attribute [local simp] QEC.Coding.ClassicalWeightReduction.boundary_single

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.ClassicalWeightReduction
open scoped BigOperators
universe u v w
variable {F : Type u} [Field F] [Fintype F] [DecidableEq F]
variable {Check : Type v} {Bit : Type w}
variable [Fintype Check] [DecidableEq Check]
variable [Fintype Bit] [DecidableEq Bit]
variable (R : Check → Bit → Prop) [DecidableRel R]
omit [Fintype F] [DecidableEq F]
namespace QEC.Coding.ClassicalWeightReduction
theorem _root_.solution
    (i : WeightReducedBit R) (q : WeightReducedCheck R) :
    basisBoundary (F := F) R i q = basisCoboundary (F := F) R q i := by
  classical
  cases i with
  | inl e =>
      cases q with
      | inl e' =>
          unfold basisBoundary basisCoboundary primaryBitBoundary
            primaryCheckCoboundary auxiliaryCheckIndex auxiliaryBitIndex
          simp only [Pi.add_apply, optionalSingle_map_inr_apply_inl,
            add_zero, Pi.single_apply]
          by_cases h : e = e'
          · subst e'
            rw [if_pos rfl, if_pos rfl]
          · have h' : e' ≠ e := fun heq => h heq.symm
            have hsCheck : (Sum.inl e' : WeightReducedCheck R) ≠ Sum.inl e := by
              exact fun heq => h' (Sum.inl.inj heq)
            have hsBit : (Sum.inl e : WeightReducedBit R) ≠ Sum.inl e' := by
              exact fun heq => h (Sum.inl.inj heq)
            rw [if_neg hsCheck, if_neg hsBit]
      | inr a =>
          rcases a with ⟨b, j⟩
          by_cases hb : e.1.2 = b
          · subst b
            unfold basisBoundary basisCoboundary primaryBitBoundary
              auxiliaryCheckCoboundary
            simp only [Pi.add_apply,
              optionalSingle_map_auxiliaryCheckIndex_apply_same,
              single_bitIncidenceAt_apply]
            simp only [Pi.single_apply, Sum.inr_ne_inl,
              if_false, zero_add]
            simpa only [Pi.add_apply, Pi.single_apply] using
              (pathVertexCoboundary_apply_eq_pathEdgeBoundary_apply
                (F := F) (bitPosition R e) j)
          · unfold basisBoundary basisCoboundary primaryBitBoundary
              auxiliaryCheckCoboundary
            simp only [Pi.add_apply,
              optionalSingle_map_auxiliaryCheckIndex_apply_of_ne R hb,
              single_bitIncidenceAt_apply_of_ne R e hb]
            simp only [Pi.single_apply, Sum.inr_ne_inl, if_false, add_zero]
  | inr a =>
      rcases a with ⟨c, j⟩
      cases q with
      | inl e =>
          by_cases hc : e.1.1 = c
          · subst c
            unfold basisBoundary basisCoboundary auxiliaryBitBoundary
              primaryCheckCoboundary
            simp only [Pi.add_apply,
              optionalSingle_map_auxiliaryBitIndex_apply_same,
              single_checkIncidenceAt_apply]
            simp only [Pi.single_apply, Sum.inr_ne_inl,
              if_false, zero_add]
            simpa only [Pi.add_apply, Pi.single_apply] using
              (pathVertexCoboundary_apply_eq_pathEdgeBoundary_apply
                (F := F) (checkPosition R e) j).symm
          · unfold basisBoundary basisCoboundary auxiliaryBitBoundary
              primaryCheckCoboundary
            simp only [Pi.add_apply,
              optionalSingle_map_auxiliaryBitIndex_apply_of_ne R hc,
              single_checkIncidenceAt_apply_of_ne R e hc]
            simp only [Pi.single_apply, Sum.inr_ne_inl, if_false, add_zero]
      | inr a' =>
          simp [basisBoundary, basisCoboundary, auxiliaryBitBoundary,
            auxiliaryCheckCoboundary]
end QEC.Coding.ClassicalWeightReduction
