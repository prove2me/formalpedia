-- Prove2me | solution 1 for QEC.Coding.StabilizerCode.DecoderDressedLogical.elementaryError_commutator_dressedLogical_mul_goodSyndromeProjector_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T12:06:15.637195+00:00
-- url     : https://prove2.me/submissions/5f01a6d8-3e65-4176-97f7-f1cf30a2c46e

import Definitions.Def_QEC_Coding_Stabilizer_DecoderDressedLogical
import Definitions.Def_QEC_Coding_Stabilizer_GoodSyndromeProtectedSector
import Theorems.Thm_QEC_Coding_StabilizerCode_DecoderDressedLogical_elementaryError_commute_dressedLogical_on_good_syndrome

set_option autoImplicit false
noncomputable section
open QEC
open QEC.Coding
open QEC.Coding.StabilizerCode
open PauliSymplectic
open Semantics
open scoped BigOperators
universe u v
variable {ι : Type u} [Fintype ι] [DecidableEq ι]
variable {κ : Type v} [Fintype κ] [DecidableEq κ]
open QEC.Coding.StabilizerCode.DecoderDressedLogical
variable {H : LocalStabilizerHamiltonian (ι := ι) (κ := κ)}
namespace QEC.Coding.StabilizerCode.DecoderDressedLogical
theorem _root_.solution
    (D : DecoderDressedLogical H)
    (elementaryErrors : Finset (Binary ι))
    {error : Binary ι} (herror : error ∈ elementaryErrors)
    {logical : Binary ι}
    (hlogical : H.code.1.InBinaryNormalizer logical) :
    (toHermitianQubitOperator error * D.dressedLogical logical -
        D.dressedLogical logical * toHermitianQubitOperator error) *
      D.goodSyndromeProjector elementaryErrors = 0 := by
  classical
  rw [goodSyndromeProjector, Finset.mul_sum]
  apply Finset.sum_eq_zero
  intro syndrome hsyndrome
  rw [sub_mul]
  apply sub_eq_zero.mpr
  apply D.elementaryError_commute_dressedLogical_on_good_syndrome
    elementaryErrors
  · exact (Finset.mem_filter.mp hsyndrome).2
  · exact herror
  · exact hlogical
end QEC.Coding.StabilizerCode.DecoderDressedLogical
