-- Prove2me | solution 1 for QEC.Coding.PuncturedReedMuller.exists_systematicKeptLift_add_shortened
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T15:14:16.65029+00:00
-- url     : https://prove2.me/submissions/fb3db823-09c8-44b9-acf8-16f4f4f51e10

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
    {word : Word (ZMod 2) (KeptPoint m w)}
    (hword : word ∈ (puncturedReedMullerCode r m w).carrier) :
    ∃ logical shortened,
      shortened ∈ (shortenedReedMullerCode r m w).carrier ∧
        systematicKeptLift h logical + shortened = word := by
  rcases (mem_puncturedReedMullerCode word).1 hword with
    ⟨full, hfull, rfl⟩
  have hwr : w ≤ r := by
    have := h.2.1
    omega
  let logical := restrictLow m w full
  let shortenedFull := full - lowCoordinateExtension hwr logical
  let shortened := restrictKept m w shortenedFull
  have hshortenedFull :
      shortenedFull ∈ (reedMullerCode r m).carrier := by
    exact (reedMullerCode r m).carrier.sub_mem hfull
      (lowCoordinateExtension_mem_reedMullerCode hwr logical)
  have hshortenedLow : restrictLow m w shortenedFull = 0 := by
    simp [shortenedFull, logical, map_sub,
      restrictLow_lowCoordinateExtension]
  have hshortened :
      shortened ∈ (shortenedReedMullerCode r m w).carrier :=
    (mem_shortenedReedMullerCode shortened).2
      ⟨shortenedFull, hshortenedFull, hshortenedLow, rfl⟩
  refine ⟨logical, shortened, hshortened, ?_⟩
  change
    restrictKept m w (lowCoordinateExtension hwr logical) +
        restrictKept m w shortenedFull =
      restrictKept m w full
  simp [shortenedFull, map_sub]
end QEC.Coding.PuncturedReedMuller
