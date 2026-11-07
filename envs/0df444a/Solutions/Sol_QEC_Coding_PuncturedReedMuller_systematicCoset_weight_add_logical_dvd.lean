-- Prove2me | solution 1 for QEC.Coding.PuncturedReedMuller.systematicCoset_weight_add_logical_dvd
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T15:14:46.957051+00:00
-- url     : https://prove2.me/submissions/d648882e-91dc-44ed-9f9f-d90c53896f16

import Definitions.Def_QEC_Coding_ReedMuller_Base
import Definitions.Def_QEC_Coding_ReedMuller_Punctured
import Theorems.Thm_QEC_Coding_ChainComplexData_pureZLogicalQuotientEquivMiddleHomology_mk
import Theorems.Thm_QEC_Coding_ReedMuller_reedMullerCode_hammingWeight_dvd_pow_two
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
theorem _root_.solution {w r m nu : Nat}
    (h : Admissible w r m) (hdegree : nu * r < m)
    (logical : Word (ZMod 2) (LowPoint m w))
    {word : Word (ZMod 2) (KeptPoint m w)}
    (hcoset : word - systematicKeptLift h logical ∈
      (shortenedReedMullerCode r m w).carrier) :
    2 ^ nu ∣ HammingWeight word + HammingWeight logical := by
  have hwr : w ≤ r := by
    have := h.2.1
    omega
  have hr : 0 < r := by
    have := h.2.1
    omega
  rcases (mem_shortenedReedMullerCode _).1 hcoset with
    ⟨shortenedFull, hshortenedFull, hshortenedLow, hshortenedKept⟩
  let full := shortenedFull + lowCoordinateExtension hwr logical
  have hfull : full ∈ (reedMullerCode r m).carrier := by
    exact (reedMullerCode r m).carrier.add_mem hshortenedFull
      (lowCoordinateExtension_mem_reedMullerCode hwr logical)
  have hlow : restrictLow m w full = logical := by
    calc
      restrictLow m w full =
          restrictLow m w shortenedFull +
            restrictLow m w (lowCoordinateExtension hwr logical) := by
              simp [full, map_add]
      _ = logical := by
        simp [hshortenedLow, restrictLow_lowCoordinateExtension]
  have hsystematic : systematicKeptLift h logical =
      restrictKept m w (lowCoordinateExtension hwr logical) := by
    simp [systematicKeptLift, LinearMap.comp_apply]
  have hkeptSum : restrictKept m w shortenedFull +
      systematicKeptLift h logical = word := by
    exact ((sub_eq_iff_eq_add).mp hshortenedKept.symm).symm
  have hkept : restrictKept m w full = word := by
    calc
      restrictKept m w full =
          restrictKept m w shortenedFull +
            restrictKept m w (lowCoordinateExtension hwr logical) := by
              simp [full, map_add]
      _ = restrictKept m w shortenedFull +
          systematicKeptLift h logical := by rw [← hsystematic]
      _ = word := hkeptSum
  have hweight : HammingWeight full =
      HammingWeight logical + HammingWeight word := by
    calc
      HammingWeight full =
          HammingWeight (restrictLow m w full) +
            HammingWeight (restrictKept m w full) :=
        HammingWeight_eq_restrictLow_add_restrictKept full
      _ = HammingWeight logical + HammingWeight word := by
        rw [hlow, hkept]
  have hward : 2 ^ nu ∣ HammingWeight full :=
    reedMullerCode_hammingWeight_dvd_pow_two hr hdegree hfull
  rw [hweight] at hward
  simpa [Nat.add_comm] using hward
end QEC.Coding.PuncturedReedMuller
