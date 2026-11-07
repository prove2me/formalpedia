-- Prove2me | solution 1 for QEC.Coding.StabilizerCode.DecoderDressedLogical.phaseOperator_commute
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T11:35:34.451877+00:00
-- url     : https://prove2.me/submissions/4701a6fc-d369-443c-bb62-e5f2df8efc1e

import Definitions.Def_QEC_Coding_Stabilizer_JointMeasurement
import Definitions.Def_QEC_Coding_Stabilizer_LocalHamiltonian
import Definitions.Def_QEC_Coding_Stabilizer_DecoderDressedLogical
import Theorems.Thm_QEC_Coding_StabilizerCode_DecoderDressedLogical_phaseOperator_mul

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
    (D : DecoderDressedLogical H) (left right : Binary ι) :
    Commute (D.phaseOperator left) (D.phaseOperator right) := by
  change D.phaseOperator left * D.phaseOperator right =
    D.phaseOperator right * D.phaseOperator left
  rw [D.phaseOperator_mul left right, D.phaseOperator_mul right left]
  apply Finset.sum_congr rfl
  intro syndrome _
  rw [mul_comm]
end QEC.Coding.StabilizerCode.DecoderDressedLogical
