-- Prove2me | solution 1 for QEC.Coding.StabilizerCode.DecoderDressedLogical.syndromeProjector_commute_phaseOperator
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T12:00:27.095738+00:00
-- url     : https://prove2.me/submissions/c27cf9f5-4cc8-4204-8b9d-0ffdf8c81884

import Definitions.Def_QEC_Coding_Stabilizer_DecoderDressedLogical
import Definitions.Def_QEC_Coding_Stabilizer_GoodSyndromeProtectedSector
import Theorems.Thm_QEC_Coding_StabilizerCode_DecoderDressedLogical_phaseOperator_mul_syndromeProjector
import Theorems.Thm_QEC_Coding_StabilizerCode_DecoderDressedLogical_syndromeProjector_mul_phaseOperator

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
    (D : DecoderDressedLogical H) (logical : Binary ι)
    (syndrome : DecoderSyndrome κ) :
    Commute (H.syndromeProjector syndrome) (D.phaseOperator logical) := by
  change H.syndromeProjector syndrome * D.phaseOperator logical =
    D.phaseOperator logical * H.syndromeProjector syndrome
  rw [D.syndromeProjector_mul_phaseOperator,
    D.phaseOperator_mul_syndromeProjector]
end QEC.Coding.StabilizerCode.DecoderDressedLogical
