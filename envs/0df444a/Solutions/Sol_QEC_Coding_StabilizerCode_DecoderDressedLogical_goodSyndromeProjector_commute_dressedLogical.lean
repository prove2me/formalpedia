-- Prove2me | solution 1 for QEC.Coding.StabilizerCode.DecoderDressedLogical.goodSyndromeProjector_commute_dressedLogical
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T12:06:03.635147+00:00
-- url     : https://prove2.me/submissions/2181dfc1-6552-4707-ac25-5828ea422dec

import Definitions.Def_QEC_Coding_Stabilizer_DecoderDressedLogical
import Definitions.Def_QEC_Coding_Stabilizer_GoodSyndromeProtectedSector
import Theorems.Thm_QEC_Coding_StabilizerCode_DecoderDressedLogical_syndromeProjector_commute_dressedLogical

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
    (D : DecoderDressedLogical H) (elementaryErrors : Finset (Binary ι))
    {logical : Binary ι} (hlogical : H.code.1.InBinaryNormalizer logical) :
    Commute (D.goodSyndromeProjector elementaryErrors)
      (D.dressedLogical logical) := by
  classical
  change D.goodSyndromeProjector elementaryErrors * D.dressedLogical logical =
    D.dressedLogical logical * D.goodSyndromeProjector elementaryErrors
  rw [goodSyndromeProjector, Finset.sum_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro syndrome _
  exact (D.syndromeProjector_commute_dressedLogical hlogical syndrome).eq
end QEC.Coding.StabilizerCode.DecoderDressedLogical
