-- Prove2me | solution 1 for QEC.Coding.PuncturedReedMuller.puncturedReedMullerCode_relativeMinimumDistance_shortened
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T15:14:45.873208+00:00
-- url     : https://prove2.me/submissions/595fdede-6a02-4e3f-bd70-af5e6b28d104

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
theorem _root_.solution
    {m r w : Nat} (hnoKernel : w < m - r) :
    RelativeMinimumDistance (puncturedReedMullerCode r m w)
      (shortenedReedMullerCode r m w) (binomialTail (m - r) w) := by
  have hrm : r ≤ m := by omega
  obtain ⟨full, hfull, hfullLow, hweight⟩ :=
    exists_reedMullerCodeword_restrictedWeight_eq_binomialTail_and_low_ne_zero
      (w := w) hrm
  let kept := restrictKept m w full
  have hkept : kept ∈ (puncturedReedMullerCode r m w).carrier :=
    (mem_puncturedReedMullerCode kept).2 ⟨full, hfull, rfl⟩
  have hkeptOutside :
      kept ∉ (shortenedReedMullerCode r m w).carrier := by
    intro hshortened
    rcases (mem_shortenedReedMullerCode kept).1 hshortened with
      ⟨shortenedFull, hshortenedFull, hshortenedLow, hshortenedKept⟩
    have hdifference :
        full - shortenedFull ∈ (reedMullerCode r m).carrier :=
      (reedMullerCode r m).carrier.sub_mem hfull hshortenedFull
    have hdifferenceKept :
        restrictKept m w (full - shortenedFull) = 0 := by
      rw [map_sub, show restrictKept m w full = kept by rfl,
        hshortenedKept, sub_self]
    have hdifferenceZero : full - shortenedFull = 0 :=
      restrictKept_eq_zero_of_mem_reedMullerCode
        hnoKernel hdifference hdifferenceKept
    have hfullEq : full = shortenedFull := sub_eq_zero.mp hdifferenceZero
    apply hfullLow
    rw [hfullEq, hshortenedLow]
  have hkeptWeight :
      HammingWeight kept = binomialTail (m - r) w := by
    simpa [kept, restrictedWeight] using hweight
  rcases puncturedReedMullerCode_minimumDistance hnoKernel with
    ⟨_minimumWitness, _hminimumWitness, _hminimumWitnessNonzero,
      _hminimumWitnessWeight, hleast⟩
  refine ⟨kept, hkept, hkeptOutside, hkeptWeight, ?_⟩
  intro candidate hcandidate hcandidateOutside
  have hcandidateNonzero : candidate ≠ 0 := by
    intro hzero
    apply hcandidateOutside
    rw [hzero]
    exact (shortenedReedMullerCode r m w).carrier.zero_mem
  exact hleast candidate hcandidate hcandidateNonzero
end QEC.Coding.PuncturedReedMuller
