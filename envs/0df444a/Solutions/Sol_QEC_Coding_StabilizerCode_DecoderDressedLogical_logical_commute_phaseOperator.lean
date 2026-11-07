-- Prove2me | solution 1 for QEC.Coding.StabilizerCode.DecoderDressedLogical.logical_commute_phaseOperator
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T11:45:01.734196+00:00
-- url     : https://prove2.me/submissions/7bef0aa4-2a8a-4753-82e3-fd237d40a521

import Definitions.Def_QEC_Coding_Stabilizer_JointMeasurement
import Definitions.Def_QEC_Coding_Stabilizer_LocalHamiltonian
import Definitions.Def_QEC_Coding_Stabilizer_DecoderDressedLogical
import Theorems.Thm_QEC_Coding_StabilizerCode_LocalStabilizerHamiltonian_normalizer_commute_syndromeProjector

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
    (D : DecoderDressedLogical H) {logical : Binary ι}
    (hlogical : H.code.1.InBinaryNormalizer logical)
    (phaseLogical : Binary ι) :
    Commute (toHermitianQubitOperator logical) (D.phaseOperator phaseLogical) := by
  classical
  change toHermitianQubitOperator logical * D.phaseOperator phaseLogical =
    D.phaseOperator phaseLogical * toHermitianQubitOperator logical
  rw [phaseOperator, Finset.mul_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro syndrome _
  rw [mul_smul_comm, smul_mul_assoc,
    (H.normalizer_commute_syndromeProjector hlogical syndrome).eq]
end QEC.Coding.StabilizerCode.DecoderDressedLogical
