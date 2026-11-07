-- Prove2me | solution 1 for QEC.Coding.PuncturedReedMuller.systematicKeptLift_mem_shortenedReedMullerCode_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T15:14:17.670892+00:00
-- url     : https://prove2.me/submissions/ffcbd654-f04e-4ab9-a6dd-038d84a3600e

import Definitions.Def_QEC_Coding_ReedMuller_Base
import Definitions.Def_QEC_Coding_ReedMuller_Punctured
import Theorems.Thm_QEC_Coding_ChainComplexData_pureZLogicalQuotientEquivMiddleHomology_mk
import Theorems.Thm_QEC_Semantics_UnitaryTransport_conjDensity_apply
import Theorems.Thm_QEC_Semantics_UnitaryTransport_conjDensity_toOperator
attribute [local simp] QEC.Coding.ChainComplexData.pureZLogicalQuotientEquivMiddleHomology_mk
attribute [local simp] QEC.Semantics.UnitaryTransport.conjDensity_apply
attribute [local simp] QEC.Semantics.UnitaryTransport.conjDensity_toOperator



set_option autoImplicit false
noncomputable section
open QEC
open QEC.Coding
open QEC.Coding.PuncturedReedMuller
open ReedMuller
namespace QEC.Coding.PuncturedReedMuller
theorem _root_.solution {w r m : Nat}
    (h : Admissible w r m)
    (logical : Word (ZMod 2) (LowPoint m w)) :
    systematicKeptLift h logical ∈
      (shortenedReedMullerCode r m w).carrier ↔ logical = 0 := by
  have hwr : w ≤ r := by
    have := h.2.1
    omega
  have hnoKernel : w < m - r := by
    have := h.2
    omega
  constructor
  · intro hmem
    rcases (mem_shortenedReedMullerCode _).1 hmem with
      ⟨full, hfull, hlow, hkept⟩
    have hsameKept : restrictKept m w full =
        restrictKept m w (lowCoordinateExtension hwr logical) := by
      simpa [systematicKeptLift, LinearMap.comp_apply] using hkept
    have hdifference : full - lowCoordinateExtension hwr logical ∈
        (reedMullerCode r m).carrier :=
      (reedMullerCode r m).carrier.sub_mem hfull
        (lowCoordinateExtension_mem_reedMullerCode hwr logical)
    have hdifferenceKept : restrictKept m w
        (full - lowCoordinateExtension hwr logical) = 0 := by
      rw [map_sub, hsameKept, sub_self]
    have hdifferenceZero := restrictKept_eq_zero_of_mem_reedMullerCode
      hnoKernel hdifference hdifferenceKept
    have hfullEq : full = lowCoordinateExtension hwr logical :=
      sub_eq_zero.mp hdifferenceZero
    calc
      logical = restrictLow m w (lowCoordinateExtension hwr logical) :=
        (restrictLow_lowCoordinateExtension hwr logical).symm
      _ = restrictLow m w full := by rw [hfullEq]
      _ = 0 := hlow
  · intro hlogical
    subst logical
    refine (mem_shortenedReedMullerCode _).2
      ⟨0, (reedMullerCode r m).carrier.zero_mem, ?_, ?_⟩
    · simp
    · simp [systematicKeptLift]
end QEC.Coding.PuncturedReedMuller
