-- Prove2me | solution 1 for QEC.Coding.StabilizerCode.DecoderDressedLogical.dressedLogical_commute_generatorOperator
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T11:59:57.579801+00:00
-- url     : https://prove2.me/submissions/66942255-fd93-4c01-be13-131427d636f3

import Definitions.Def_QEC_Coding_Stabilizer_JointMeasurement
import Definitions.Def_QEC_Coding_Stabilizer_LocalHamiltonian
import Definitions.Def_QEC_Coding_Stabilizer_DecoderDressedLogical
import Theorems.Thm_QEC_Coding_StabilizerCode_DecoderDressedLogical_logical_commute_generatorOperator
import Theorems.Thm_QEC_Coding_StabilizerCode_DecoderDressedLogical_generatorOperator_commute_phaseOperator

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
    (hlogical : H.code.1.InBinaryNormalizer logical) (check : κ) :
    Commute (D.dressedLogical logical) (H.generatorOperator check) := by
  have hlogicalGenerator := D.logical_commute_generatorOperator hlogical check
  have hphaseGenerator := D.generatorOperator_commute_phaseOperator check logical
  change (toHermitianQubitOperator logical * D.phaseOperator logical) *
      H.generatorOperator check =
    H.generatorOperator check *
      (toHermitianQubitOperator logical * D.phaseOperator logical)
  calc
    (toHermitianQubitOperator logical * D.phaseOperator logical) *
        H.generatorOperator check =
      toHermitianQubitOperator logical *
        (D.phaseOperator logical * H.generatorOperator check) := by
          rw [mul_assoc]
    _ = toHermitianQubitOperator logical *
        (H.generatorOperator check * D.phaseOperator logical) := by
          rw [hphaseGenerator.eq]
    _ = (toHermitianQubitOperator logical * H.generatorOperator check) *
        D.phaseOperator logical := by rw [mul_assoc]
    _ = (H.generatorOperator check * toHermitianQubitOperator logical) *
        D.phaseOperator logical := by rw [hlogicalGenerator.eq]
    _ = H.generatorOperator check *
        (toHermitianQubitOperator logical * D.phaseOperator logical) := by
          rw [mul_assoc]
end QEC.Coding.StabilizerCode.DecoderDressedLogical
