-- Prove2me | solution 1 for QEC.Coding.StabilizerCode.DecoderDressedLogical.goodSyndromeProjector_add_badSyndromeProjector
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T11:35:52.265992+00:00
-- url     : https://prove2.me/submissions/6585d839-d9f2-43eb-9c65-c409ff1d994f

import Definitions.Def_QEC_Coding_Stabilizer_DecoderDressedLogical
import Definitions.Def_QEC_Coding_Stabilizer_GoodSyndromeProtectedSector
import Theorems.Thm_QEC_Coding_StabilizerCode_LocalStabilizerHamiltonian_sum_syndromeProjector_eq_one


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
    D.goodSyndromeProjector elementaryErrors +
        D.badSyndromeProjector elementaryErrors = 1 := by
  classical
  rw [goodSyndromeProjector, badSyndromeProjector,
    goodSyndromes, badSyndromes,
    Finset.sum_filter_add_sum_filter_not]
  exact H.sum_syndromeProjector_eq_one
end QEC.Coding.StabilizerCode.DecoderDressedLogical
