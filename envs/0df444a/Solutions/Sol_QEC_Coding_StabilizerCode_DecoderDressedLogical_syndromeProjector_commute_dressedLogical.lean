-- Prove2me | solution 1 for QEC.Coding.StabilizerCode.DecoderDressedLogical.syndromeProjector_commute_dressedLogical
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T12:03:33.528732+00:00
-- url     : https://prove2.me/submissions/b31f759a-662f-4263-927a-5dc9d2568916

import Definitions.Def_QEC_Coding_Stabilizer_DecoderDressedLogical
import Definitions.Def_QEC_Coding_Stabilizer_GoodSyndromeProtectedSector
import Theorems.Thm_QEC_Coding_StabilizerCode_DecoderDressedLogical_syndromeProjector_commute_phaseOperator
import Theorems.Thm_QEC_Coding_StabilizerCode_LocalStabilizerHamiltonian_normalizer_commute_syndromeProjector
import Theorems.Thm_QEC_Locality_NoEdgeBetween_symm


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
    (syndrome : DecoderSyndrome κ) :
    Commute (H.syndromeProjector syndrome) (D.dressedLogical logical) := by
  have hbare := H.normalizer_commute_syndromeProjector hlogical syndrome
  have hphase := D.syndromeProjector_commute_phaseOperator logical syndrome
  change H.syndromeProjector syndrome *
      (toHermitianQubitOperator logical * D.phaseOperator logical) =
    (toHermitianQubitOperator logical * D.phaseOperator logical) *
      H.syndromeProjector syndrome
  calc
    H.syndromeProjector syndrome *
          (toHermitianQubitOperator logical * D.phaseOperator logical) =
        (H.syndromeProjector syndrome *
          toHermitianQubitOperator logical) * D.phaseOperator logical := by
            rw [mul_assoc]
    _ = (toHermitianQubitOperator logical *
          H.syndromeProjector syndrome) * D.phaseOperator logical := by
            rw [hbare.eq.symm]
    _ = toHermitianQubitOperator logical *
        (H.syndromeProjector syndrome * D.phaseOperator logical) := by
          rw [mul_assoc]
    _ = toHermitianQubitOperator logical *
        (D.phaseOperator logical * H.syndromeProjector syndrome) := by
          rw [hphase.eq]
    _ = (toHermitianQubitOperator logical * D.phaseOperator logical) *
        H.syndromeProjector syndrome := by rw [mul_assoc]
end QEC.Coding.StabilizerCode.DecoderDressedLogical
