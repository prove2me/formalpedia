-- Prove2me | solution 1 for QEC.Coding.StabilizerCode.DecoderDressedLogical.goodSyndromeProjector_mul_self
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T10:17:32.856758+00:00
-- url     : https://prove2.me/submissions/57994a41-5cd8-41ca-9013-9003f264021f

import Definitions.Def_QEC_Coding_Stabilizer_DecoderDressedLogical
import Definitions.Def_QEC_Coding_Stabilizer_GoodSyndromeProtectedSector
import Theorems.Thm_QEC_Coding_StabilizerCode_LocalStabilizerHamiltonian_syndromeProjector_mul_of_ne
import Theorems.Thm_QEC_Coding_StabilizerCode_LocalStabilizerHamiltonian_syndromeProjector_mul_self
import Theorems.Thm_QEC_Locality_NoEdgeBetween_symm
attribute [local simp] QEC.Coding.StabilizerCode.LocalStabilizerHamiltonian.syndromeProjector_mul_self



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
    D.goodSyndromeProjector elementaryErrors *
        D.goodSyndromeProjector elementaryErrors =
      D.goodSyndromeProjector elementaryErrors := by
  classical
  rw [goodSyndromeProjector, Finset.sum_mul_sum]
  apply Finset.sum_congr rfl
  intro syndrome hsyndrome
  rw [Finset.sum_eq_single syndrome]
  · exact H.syndromeProjector_mul_self syndrome
  · intro other hother hne
    exact H.syndromeProjector_mul_of_ne syndrome other hne.symm
  · exact fun hnot => (hnot hsyndrome).elim
end QEC.Coding.StabilizerCode.DecoderDressedLogical
