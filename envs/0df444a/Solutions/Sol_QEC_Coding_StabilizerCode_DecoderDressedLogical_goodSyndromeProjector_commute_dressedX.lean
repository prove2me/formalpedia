-- Prove2me | solution 1 for QEC.Coding.StabilizerCode.DecoderDressedLogical.goodSyndromeProjector_commute_dressedX
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T12:08:55.475936+00:00
-- url     : https://prove2.me/submissions/9f18cb39-12fb-44cf-bf03-24e5c557a1a0

import Definitions.Def_QEC_Coding_Stabilizer_DecoderDressedLogical
import Definitions.Def_QEC_Coding_Stabilizer_GoodSyndromeProtectedSector
import Theorems.Thm_QEC_Coding_StabilizerCode_DecoderDressedLogical_goodSyndromeProjector_commute_dressedLogical

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
    (D : DecoderDressedLogical H) (elementaryErrors : Finset (Binary ι)) :
    Commute (D.goodSyndromeProjector elementaryErrors) D.dressedX :=
  D.goodSyndromeProjector_commute_dressedLogical elementaryErrors
    D.logicalX_normalizer
end QEC.Coding.StabilizerCode.DecoderDressedLogical
