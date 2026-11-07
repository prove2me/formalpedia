-- Prove2me | solution 1 for QEC.Coding.StabilizerCode.DecoderDressedLogical.dressedLogical_commute_hamiltonian
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T12:03:21.627112+00:00
-- url     : https://prove2.me/submissions/d4df8ca5-65d7-4edd-a5a5-7aa536f0c43e

import Definitions.Def_QEC_Coding_Stabilizer_JointMeasurement
import Definitions.Def_QEC_Coding_Stabilizer_LocalHamiltonian
import Definitions.Def_QEC_Coding_Stabilizer_DecoderDressedLogical
import Theorems.Thm_QEC_Coding_StabilizerCode_DecoderDressedLogical_dressedLogical_commute_generatorOperator

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
    (hlogical : H.code.1.InBinaryNormalizer logical) :
    Commute (D.dressedLogical logical) H.operator := by
  classical
  change D.dressedLogical logical * H.operator =
    H.operator * D.dressedLogical logical
  rw [LocalStabilizerHamiltonian.operator, Finset.mul_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro check _
  have hgenerator := D.dressedLogical_commute_generatorOperator hlogical check
  change D.dressedLogical logical * (-(H.generatorOperator check)) =
    -(H.generatorOperator check) * D.dressedLogical logical
  rw [mul_neg, neg_mul, hgenerator.eq]
end QEC.Coding.StabilizerCode.DecoderDressedLogical
