-- Prove2me | solution 1 for QEC.Coding.PuncturedReedMuller.shortenedReedMullerCode_dual_eq_punctured_of_lt_of_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T14:06:41.007636+00:00
-- url     : https://prove2.me/submissions/4373754f-5045-4268-92ca-b417fbedb5a4

import Definitions.Def_QEC_Coding_ReedMuller_Base
import Definitions.Def_QEC_Coding_ReedMuller_Punctured
import Theorems.Thm_QEC_Coding_PuncturedReedMuller_wordPairing_restrictKept_eq_of_restrictLow_eq_zero
import Theorems.Thm_QEC_Coding_ChainComplexData_pureZLogicalQuotientEquivMiddleHomology_mk
import Theorems.Thm_QEC_Coding_ReedMuller_reedMullerCode_dual_eq_complementary
import Theorems.Thm_QEC_Semantics_UnitaryTransport_conjDensity_apply
import Theorems.Thm_QEC_Semantics_UnitaryTransport_conjDensity_toOperator
attribute [local simp] QEC.Coding.ChainComplexData.pureZLogicalQuotientEquivMiddleHomology_mk
attribute [local simp] QEC.Semantics.UnitaryTransport.conjDensity_apply
attribute [local simp] QEC.Semantics.UnitaryTransport.conjDensity_toOperator


section
noncomputable section
namespace QEC
namespace Coding
namespace PuncturedReedMuller
open ReedMuller
private theorem wordPairing_zeroExtendLow {m w : Nat}
    (low : Word (ZMod 2) (LowPoint m w))
    (full : Word (ZMod 2) (BooleanPoint m)) :
    wordPairing (zeroExtendLow m w low) full =
      wordPairing low (restrictLow m w full) := by
  calc
    wordPairing (zeroExtendLow m w low) full =
        wordPairing (restrictLow m w (zeroExtendLow m w low))
          (restrictLow m w full) :=
      (wordPairing_restrictLow_eq_of_restrictKept_eq_zero
        (zeroExtendLow m w low) full (restrictKept_zeroExtendLow low)).symm
    _ = wordPairing low (restrictLow m w full) := by
      rw [restrictLow_zeroExtendLow]
private theorem wordPairing_zeroExtendKept {m w : Nat}
    (kept : Word (ZMod 2) (KeptPoint m w))
    (full : Word (ZMod 2) (BooleanPoint m)) :
    wordPairing (zeroExtendKept m w kept) full =
      wordPairing kept (restrictKept m w full) := by
  calc
    wordPairing (zeroExtendKept m w kept) full =
        wordPairing (restrictKept m w (zeroExtendKept m w kept))
          (restrictKept m w full) :=
      (wordPairing_restrictKept_eq_of_restrictLow_eq_zero
        (zeroExtendKept m w kept) full (restrictLow_zeroExtendKept kept)).symm
    _ = wordPairing kept (restrictKept m w full) := by
      rw [restrictKept_zeroExtendKept]
end PuncturedReedMuller
end Coding
end QEC
end
end

set_option autoImplicit false
noncomputable section
open QEC
open QEC.Coding
open QEC.Coding.PuncturedReedMuller
open ReedMuller
namespace QEC.Coding.PuncturedReedMuller
theorem _root_.solution
    {w r m : Nat} (hrm : r < m) (hcomplement : w ≤ m - r - 1) :
    (shortenedReedMullerCode (m - r - 1) m w).dual.carrier =
      (puncturedReedMullerCode r m w).carrier := by
  apply le_antisymm
  · intro kept hkept
    let retainedExtension :=
      (restrictKept m w).comp (lowCoordinateExtension hcomplement)
    let lowFunctional := wordLinearMapTranspose retainedExtension kept
    let witness := zeroExtendKept m w kept - zeroExtendLow m w lowFunctional
    have hwitnessDual : witness ∈
        (reedMullerCode (m - r - 1) m).dual.carrier := by
      refine ((reedMullerCode (m - r - 1) m).mem_dual witness).2 ?_
      intro full hfull
      let residual := full - lowCoordinateExtension hcomplement
        (restrictLow m w full)
      have hresidual : residual ∈
          (reedMullerCode (m - r - 1) m).carrier := by
        dsimp [residual]
        exact (reedMullerCode (m - r - 1) m).carrier.sub_mem hfull
          (lowCoordinateExtension_mem_reedMullerCode hcomplement _)
      have hresidualLow : restrictLow m w residual = 0 := by
        simp [residual, map_sub, restrictLow_lowCoordinateExtension]
      have hresidualShortened : restrictKept m w residual ∈
          (shortenedReedMullerCode (m - r - 1) m w).carrier :=
        (mem_shortenedReedMullerCode _).2
          ⟨residual, hresidual, hresidualLow, rfl⟩
      have horthogonal : wordPairing kept (restrictKept m w residual) = 0 :=
        (shortenedReedMullerCode (m - r - 1) m w).orthogonal_of_mem_dual
          hkept hresidualShortened
      have htranspose : wordPairing lowFunctional (restrictLow m w full) =
          wordPairing kept
            (restrictKept m w
              (lowCoordinateExtension hcomplement (restrictLow m w full))) := by
        simpa [lowFunctional, retainedExtension, LinearMap.comp_apply] using
          (wordPairing_wordLinearMapTranspose
            ((restrictKept m w).comp (lowCoordinateExtension hcomplement)) kept
            (restrictLow m w full))
      calc
        wordPairing witness full =
            wordPairing (zeroExtendKept m w kept) full +
              wordPairing (zeroExtendLow m w lowFunctional) full := by
          simp [witness, sub_eq_add_neg, ZModModule.neg_eq_self,
            wordPairing.map_add]
        _ = wordPairing kept (restrictKept m w full) +
              wordPairing lowFunctional (restrictLow m w full) := by
          rw [wordPairing_zeroExtendKept, wordPairing_zeroExtendLow]
        _ = wordPairing kept (restrictKept m w full) +
              wordPairing kept
                (restrictKept m w
                  (lowCoordinateExtension hcomplement
                    (restrictLow m w full))) := by
          rw [htranspose]
        _ = wordPairing kept (restrictKept m w residual) := by
          simp [residual, sub_eq_add_neg, ZModModule.neg_eq_self]
        _ = 0 := horthogonal
    have hwitness : witness ∈ (reedMullerCode r m).carrier := by
      rw [← reedMullerCode_dual_eq_complementary hrm]
      exact hwitnessDual
    refine (mem_puncturedReedMullerCode _).2 ⟨witness, hwitness, ?_⟩
    simp [witness, map_sub]
  · intro kept hkept
    refine ((shortenedReedMullerCode (m - r - 1) m w).mem_dual kept).2 ?_
    intro shortened hshortened
    rcases (mem_puncturedReedMullerCode kept).1 hkept with
      ⟨fullKept, hfullKept, hrestrictKept⟩
    rcases (mem_shortenedReedMullerCode shortened).1 hshortened with
      ⟨fullShortened, hfullShortened, hrestrictLow, hrestrictShortened⟩
    have hfullKeptDual : fullKept ∈
        (reedMullerCode (m - r - 1) m).dual.carrier := by
      rw [reedMullerCode_dual_eq_complementary hrm]
      exact hfullKept
    calc
      wordPairing kept shortened =
          wordPairing (restrictKept m w fullKept)
            (restrictKept m w fullShortened) := by
        rw [hrestrictKept, hrestrictShortened]
      _ = wordPairing (restrictKept m w fullShortened)
            (restrictKept m w fullKept) := by
        simp only [wordPairing_apply]
        exact dotProduct_comm _ _
      _ = wordPairing fullShortened fullKept :=
        wordPairing_restrictKept_eq_of_restrictLow_eq_zero
          fullShortened fullKept hrestrictLow
      _ = wordPairing fullKept fullShortened := by
        simp only [wordPairing_apply]
        exact dotProduct_comm _ _
      _ = 0 :=
        (reedMullerCode (m - r - 1) m).orthogonal_of_mem_dual
          hfullKeptDual hfullShortened
end QEC.Coding.PuncturedReedMuller
