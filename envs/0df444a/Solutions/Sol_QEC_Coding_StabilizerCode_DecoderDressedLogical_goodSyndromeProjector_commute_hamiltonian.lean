-- Prove2me | solution 1 for QEC.Coding.StabilizerCode.DecoderDressedLogical.goodSyndromeProjector_commute_hamiltonian
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T12:00:28.180208+00:00
-- url     : https://prove2.me/submissions/8e8b31a2-fbae-4e14-a52d-1e9f6a465500

import Definitions.Def_QEC_Coding_Stabilizer_DecoderDressedLogical
import Definitions.Def_QEC_Coding_Stabilizer_GoodSyndromeProtectedSector
import Theorems.Thm_QEC_Coding_StabilizerCode_DecoderDressedLogical_syndromeProjector_commute_hamiltonian

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
    Commute (D.goodSyndromeProjector elementaryErrors) H.operator := by
  classical
  change D.goodSyndromeProjector elementaryErrors * H.operator =
    H.operator * D.goodSyndromeProjector elementaryErrors
  rw [goodSyndromeProjector, Finset.sum_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro syndrome _
  exact (D.syndromeProjector_commute_hamiltonian syndrome).eq
end QEC.Coding.StabilizerCode.DecoderDressedLogical
