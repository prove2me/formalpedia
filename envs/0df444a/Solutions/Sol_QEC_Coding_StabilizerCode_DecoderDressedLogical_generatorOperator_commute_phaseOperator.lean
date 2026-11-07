-- Prove2me | solution 1 for QEC.Coding.StabilizerCode.DecoderDressedLogical.generatorOperator_commute_phaseOperator
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T11:57:03.692364+00:00
-- url     : https://prove2.me/submissions/c2ecaafe-679c-43ca-a8b5-436cb859b2c0

import Definitions.Def_QEC_Coding_Stabilizer_JointMeasurement
import Definitions.Def_QEC_Coding_Stabilizer_LocalHamiltonian
import Definitions.Def_QEC_Coding_Stabilizer_DecoderDressedLogical
import Theorems.Thm_QEC_Coding_StabilizerCode_DecoderDressedLogical_generatorOperator_commute_syndromeProjector

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
    (D : DecoderDressedLogical H) (check : κ) (logical : Binary ι) :
    Commute (H.generatorOperator check) (D.phaseOperator logical) := by
  classical
  change H.generatorOperator check * D.phaseOperator logical =
    D.phaseOperator logical * H.generatorOperator check
  rw [phaseOperator, Finset.mul_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro syndrome _
  rw [mul_smul_comm, smul_mul_assoc,
    (D.generatorOperator_commute_syndromeProjector check syndrome).eq]
end QEC.Coding.StabilizerCode.DecoderDressedLogical
